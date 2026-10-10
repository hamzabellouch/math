import Mathlib
import OAI.Analysis.Commutator.DerivationKaplansky
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.ReducingMatrix
import OAI.Analysis.Commutator.SeparableReducingHull

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.SeparableTest

open SeparableReducingHull ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (Y : H →L[ℂ] H)

def generators : ((Fin h×Fin h)⊕Unit) → H →L[ℂ] H :=
  Sum.elim (fun ij => X ij.1 ij.2) (fun _ => Y)

def space (ξ : PiLp 2 (fun _ : Fin h => H)) : Submodule ℂ H := hull (generators h X Y) (fun i => ξ i)

instance space_complete (ξ : PiLp 2 (fun _ : Fin h => H)) : CompleteSpace (space h X Y ξ) :=
  SeparableReducingHull.hull_complete _ _

instance space_separable (ξ : PiLp 2 (fun _ : Fin h => H)) : TopologicalSpace.SeparableSpace (space h X Y ξ) :=
  SeparableReducingHull.hull_separable _ _

def algebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun ij : Fin h×Fin h => X ij.1 ij.2))).topologicalClosure

instance algebra_closed : IsClosed (algebra h X : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance algebra_cstar : CStarAlgebra (algebra h X) := StarSubalgebra.cstarAlgebra _

local instance : PartialOrder (algebra h X) := CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (algebra h X) := CStarAlgebra.spectralOrderedRing _

lemma entry_mem (i j : Fin h) : X i j∈algebra h X :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (i,j)))

def entries : Matrix (Fin h) (Fin h) (algebra h X) := fun i j => ⟨X i j,entry_mem h X i j⟩

lemma algebra_le (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) : algebra h X≤P.toStarSubalgebra := by
  apply StarSubalgebra.topologicalClosure_minimal
  · exact StarAlgebra.adjoin_le (by rintro _ ⟨⟨i,j⟩,rfl⟩; exact hX i j)
  · exact VonNeumannCStar.isClosed P

variable (ξ : PiLp 2 (fun _ : Fin h => H))

lemma algebra_reduces : algebra h X≤reducingAlgebra (space h X Y ξ) := by
  apply StarSubalgebra.topologicalClosure_minimal
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact generator_mem_reducingAlgebra (generators h X Y) (fun i => ξ i) (Sum.inl (i,j))
  · exact reducingAlgebra_closed _ (hull_closed _ _)

lemma algebra_invariant (a : algebra h X) (x : H) (hx : x∈space h X Y ξ) :
    (a:H →L[ℂ] H) x∈space h X Y ξ := (algebra_reduces h X Y ξ a.property).1 x hx

lemma Y_invariant : ∀ x∈space h X Y ξ,Y x∈space h X Y ξ :=
  invariant (generators h X Y) (fun i => ξ i) (Sum.inr Unit.unit)

def representation : algebra h X →⋆ₐ[ℂ] (space h X Y ξ →L[ℂ] space h X Y ξ) :=
  restrict (algebra h X).subtype _ (algebra_invariant h X Y ξ)

def restrictedY : space h X Y ξ →L[ℂ] space h X Y ξ := Y.restrict (Y_invariant h X Y ξ)

def vector : PiLp 2 (fun _ : Fin h => space h X Y ξ) :=
  WithLp.toLp 2 (fun i => ⟨ξ i,vector_mem _ _ i⟩)

lemma include_vector : matrixInclusion (space h X Y ξ) h (vector h X Y ξ)=ξ := by ext i; rfl

lemma vector_norm : ‖vector h X Y ξ‖=‖ξ‖ := by
  rw [←(matrixInclusion (space h X Y ξ) h).norm_map,include_vector]

lemma scalar_bound (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) (a : algebra h X) :
    ‖restrictedY h X Y ξ*representation h X Y ξ a-representation h X Y ξ a*restrictedY h X Y ξ‖≤
      commutatorSeminorm P Y*‖a‖ := by
  have hb := norm_commutator_compression_le (algebra h X).subtype (space h X Y ξ)
    (algebra_invariant h X Y ξ) Y a
  rw [compression_eq_restrict _ Y (Y_invariant h X Y ξ)] at hb
  exact hb.trans (commutator_bound P Y (algebra_le h X P hX a.property))

lemma seminorm_bound (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) :
    commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range) (restrictedY h X Y ξ)≤
      commutatorSeminorm P Y :=
  DerivationColumns.seminorm_bicommutant_le _ _ (commutatorSeminorm_nonneg P Y)
    (scalar_bound h X Y ξ P hX)

lemma matrix_norm_le : ‖matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))‖≤
    ‖matrixOperator h X‖ :=
  restricted_matrix_norm_le (algebra h X).subtype (space h X Y ξ)
    (algebra_invariant h X Y ξ) h (entries h X)

lemma commutator_vector :
    (diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y) ξ=
    matrixInclusion (space h X Y ξ) h
      ((diagonalAmplification h (restrictedY h X Y ξ)*
        matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))-
        matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))*
        diagonalAmplification h (restrictedY h X Y ξ)) (vector h X Y ξ)) := by
  have hh := congrArg (fun L => L (vector h X Y ξ))
    (matrix_commutator_intertwines (algebra h X).subtype (space h X Y ξ)
      (algebra_invariant h X Y ξ) Y (Y_invariant h X Y ξ) h (entries h X))
  change (diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y)
      (matrixInclusion (space h X Y ξ) h (vector h X Y ξ))=_ at hh
  rw [include_vector] at hh
  exact hh

end Kadison.SeparableTest

end

end
end

end OAI
