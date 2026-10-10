import Mathlib
import OAI.Analysis.Commutator.FreeMomentsTransport
import OAI.Analysis.Commutator.MatrixTowerGNS
import OAI.Analysis.Commutator.VectorFreeGeneration

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.GeneratedFreePair

open FreeMoments

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (D : VonNeumannAlgebra H) (k : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def algebra : VonNeumannAlgebra H := NormalGNS.bicommutant (D.toStarSubalgebra⊔k.range)

lemma left_mem (d : D) : (d:H →L[ℂ] H)∈algebra D k :=
  NormalGNS.subset_bicommutant _ ((show D.toStarSubalgebra ≤ D.toStarSubalgebra ⊔ k.range from le_sup_left) d.property)

lemma right_mem (a : A) : k a∈algebra D k :=
  NormalGNS.subset_bicommutant _ ((show k.range ≤ D.toStarSubalgebra ⊔ k.range from le_sup_right) ⟨a,rfl⟩)

lemma left_le : D.toStarSubalgebra≤(algebra D k).toStarSubalgebra := fun a ha =>
  left_mem D k ⟨a,ha⟩

abbrev leftHom : D →⋆ₐ[ℂ] algebra D k := VectorGNS.inclusion (algebra D k) D (left_le D k)

def rightHom : A →⋆ₐ[ℂ] algebra D k := k.codRestrict (algebra D k).toStarSubalgebra (right_mem D k)

def ambient (b : Bool) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  if b then k.range else D.toStarSubalgebra

def factors (b : Bool) : StarSubalgebra ℂ (algebra D k) :=
  (ambient D k b).comap (algebra D k).toStarSubalgebra.subtype

lemma false_range : factors D k false=(leftHom D k).range := by
  ext a
  change (a:H →L[ℂ] H)∈D ↔ ∃ d : D,leftHom D k d=a
  constructor
  · intro ha
    exact ⟨⟨a,ha⟩,Subtype.ext rfl⟩
  · rintro ⟨d,rfl⟩
    exact d.property

lemma right_factor (a : A) : rightHom D k a∈factors D k true := by
  change k a∈k.range
  exact ⟨a,rfl⟩

lemma original_generation (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer
    (Set.centralizer (((iSup (factors D k)).map (algebra D k).toStarSubalgebra.subtype) : Set _)) := by
  have hj : D.toStarSubalgebra⊔k.range≤
      (iSup (factors D k)).map (algebra D k).toStarSubalgebra.subtype := by
    apply sup_le
    · intro d hd
      exact ⟨leftHom D k ⟨d,hd⟩,(le_iSup (factors D k) false) hd,rfl⟩
    · rintro b ⟨x,rfl⟩
      exact ⟨rightHom D k x,(le_iSup (factors D k) true) (right_factor D k x),rfl⟩
  have hb := (NormalGNS.mem_bicommutant _ _).mp a.property
  intro T hT
  apply hb T
  intro x hx
  exact hT x (hj hx)

lemma le_ambient (M : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
    (hkM : ∀ a : A,k a∈M) : (algebra D k).toStarSubalgebra≤M.toStarSubalgebra := by
  intro a ha
  change a∈(M : Set (H →L[ℂ] H))
  rw [←M.centralizer_centralizer]
  have hb := (NormalGNS.mem_bicommutant _ _).mp ha
  have hj : D.toStarSubalgebra⊔k.range≤M.toStarSubalgebra := sup_le hDM (by
    rintro b ⟨x,rfl⟩
    exact hkM x)
  intro T hT
  apply hb T
  intro x hx
  exact hT x (hj hx)

include D k in
theorem free_in_generated (ξ : H)
    (hfree : Free (ambient D k) (VectorFunctional.functional ξ).toLinearMap) :
    Free (factors D k) (VectorGNS.subalgebraTrace (algebra D k) ξ).toLinearMap := by
  apply free_of_map (factors D k) (ambient D k)
    (VectorGNS.subalgebraTrace (algebra D k) ξ).toLinearMap
    (VectorFunctional.functional ξ).toLinearMap (algebra D k).toStarSubalgebra.subtype
    (fun _ => rfl) (fun _ _ ha => ha) hfree

lemma in_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hD : ∀ d : D,(d:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hk : ∀ a : A,k a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  have hle := le_ambient D k (NormalGNS.bicommutant S)
    (fun d hd => (NormalGNS.mem_bicommutant _ _).mpr (hD ⟨d,hd⟩))
    (fun b => (NormalGNS.mem_bicommutant _ _).mpr (hk b))
  exact (NormalGNS.mem_bicommutant _ _).mp (hle a.property)

lemma in_range_bicommutant {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (l : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hD : ∀ d : D,(d:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (Set.range l)))
    (hk : ∀ a : A,k a∈Set.range l)
    (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (Set.range l)) := by
  exact in_bicommutant D k l.range hD
    (fun b => Set.subset_centralizer_centralizer (hk b)) a

end Kadison.GeneratedFreePair

end

end
end

end OAI
