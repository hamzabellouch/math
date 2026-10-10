import OAI.Analysis.KadisonKastler.PublishedUltrapower
import OAI.Analysis.FactorGeneration.FiniteComparison

namespace OAI

/-! # Unitary lifts through quotients of finite-factor sequence algebras

The concrete finite-factor polar decomposition extends to a unitary.
Applying it coordinatewise, continuous functional calculus shows that a
unitary quotient class has a bounded sequence of unitary representatives.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance liftOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance liftPreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance liftLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance liftStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
local instance liftSequenceOrder : PartialOrder (BoundedSequence (Algebra M)) :=
  CStarAlgebra.spectralOrder _
local instance liftSequenceStarOrder : StarOrderedRing (BoundedSequence (Algebra M)) :=
  CStarAlgebra.spectralOrderedRing _

/-- Coordinatewise unitary polar decomposition in the concrete factor. -/
theorem exists_unitary_polar (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (x : Algebra M) : ∃ v : unitary (Algebra M), (v : Algebra M) * CFC.abs x = x := by
  apply Generator.Tracial.exists_unitary_polar_decomposition _ hM.finite x
  intro c hc
  obtain ⟨z, hz⟩ := hM.factor c hc
  exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩

/-- A unitary in a quotient of the bounded sequences has actual unitary
coordinate representatives. Surjectivity and finite polar decomposition
suffice; there is no norm or trace approximation premise. -/
theorem exists_unitary_sequence_lift (hM : Generator.IsII1Factor M.toStarSubalgebra)
    {Q : Type*} [CStarAlgebra Q]
    (π : BoundedSequence (Algebra M) →⋆ₐ[ℂ] Q) (hπ : Function.Surjective π)
    (u : unitary Q) :
    ∃ v : unitary (BoundedSequence (Algebra M)), π (v : BoundedSequence (Algebra M)) = u := by
  let : PartialOrder Q := CStarAlgebra.spectralOrder Q
  let : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing Q
  let : Nontrivial (Algebra M) := ⟨⟨0, 1, fun h => hM.nonzero (congrArg Subtype.val h)⟩⟩
  obtain ⟨x, hx⟩ := hπ u
  choose w hw using (fun j : ℕ => exists_unitary_polar hM (x j))
  let y : BoundedSequence (Algebra M) := BoundedContinuousFunction.mkOfDiscrete
    (fun j => (w j : Algebra M)) 2 (by
      intro i j
      calc dist (w i : Algebra M) (w j : Algebra M) ≤ ‖(w i : Algebra M)‖ + ‖(w j : Algebra M)‖ :=
          dist_le_norm_add_norm _ _
        _ ≤ 2 := by rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]; norm_num)
  have hy : y ∈ unitary (BoundedSequence (Algebra M)) := by
    constructor <;> apply BoundedContinuousFunction.ext <;> intro j
    · exact (w j).property.1
    · exact (w j).property.2
  have hxy : y * CFC.abs x = x := by
    apply BoundedContinuousFunction.ext
    intro j
    change (w j : Algebra M) * (CFC.abs x) j = x j
    rw [← boundedSequenceEval_apply j (CFC.abs x),
      starAlgHom_map_abs (boundedSequenceEval j)]
    exact hw j
  have hmap := congrArg π hxy
  rw [map_mul, starAlgHom_map_abs π, hx] at hmap
  have huabs : CFC.abs (u : Q) = 1 := by
    rw [CFC.abs, u.property.1, CFC.sqrt_one]
  rw [huabs, mul_one] at hmap
  exact ⟨⟨y, hy⟩, hmap⟩

/-- The standard represented tracial ultrapower admits unitary lifts. -/
theorem TracialUltrapower.unitary_lift
    {hM : Generator.IsII1Factor M.toStarSubalgebra} {ω : Ultrafilter ℕ}
    (Q : TracialUltrapower (concreteFactorTrace hM) ω) (u : unitary (Algebra Q.algebra)) :
    ∃ v : unitary (BoundedSequence (Algebra M)), Q.quotient v = u :=
  exists_unitary_sequence_lift hM Q.quotient Q.surjective u

end

end KadisonKastler

end OAI
