import Mathlib
import OAI.Analysis.Commutator.MatrixTower

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

abbrev concreteStage (n : ℕ) : Matrix (F n).I (F n).I ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp (F n).hom

def stageAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n,(concreteStage M F n).range

def generated : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))
  centralizer_centralizer' := by
    have h : ((StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))) :
        StarSubalgebra ℂ (H →L[ℂ] H)).carrier =
        Set.centralizer (Set.centralizer (stageAlgebra M F : Set (H →L[ℂ] H))) := by
      exact (StarSubalgebra.coe_centralizer_centralizer ℂ _).trans (by
        rw [StarMemClass.star_coe_eq,Set.union_self])
    change _ = ((StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))) :
      StarSubalgebra ℂ (H →L[ℂ] H)).carrier
    rw [h]
    simp only [Set.centralizer_centralizer_centralizer]

lemma mem_generated (a : H →L[ℂ] H) : a∈generated M F ↔
    a∈Set.centralizer (Set.centralizer (stageAlgebra M F : Set (H →L[ℂ] H))) := by
  change a∈(StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (stageAlgebra M F : Set (H →L[ℂ] H)))) ↔ _
  rw [←SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq,Set.union_self]

lemma stageAlgebra_le : stageAlgebra M F≤M.toStarSubalgebra := by
  apply iSup_le
  intro n
  rintro a ⟨b,rfl⟩
  exact ((F n).hom b).property

lemma generated_le : generated M F≤M := by
  intro a ha
  change a∈(M : Set (H →L[ℂ] H))
  rw [←M.centralizer_centralizer]
  intro c hc
  apply (mem_generated M F a).mp ha c
  intro b hb
  exact hc b (stageAlgebra_le M F hb)

lemma stage_mem (n : ℕ) (a : Matrix (F n).I (F n).I ℂ) : concreteStage M F n a∈generated M F := by
  apply (mem_generated M F _).mpr
  apply Set.subset_centralizer_centralizer
  exact (le_iSup (fun n => (concreteStage M F n).range) n) ⟨a,rfl⟩

def stageHom (n : ℕ) : Matrix (F n).I (F n).I ℂ →⋆ₐ[ℂ] generated M F :=
  (concreteStage M F n).codRestrict (generated M F).toStarSubalgebra (stage_mem M F n)

variable (hirr : ∀ a : M,(∀ n b,(F n).hom b*a=a*(F n).hom b) → ∃ z : ℂ,a=z • (1:M))

include hirr in
lemma generated_irreducible (a : H →L[ℂ] H) (ha : a∈M)
    (hc : a∈Set.centralizer (generated M F : Set (H →L[ℂ] H))) :
    ∃ z : ℂ,a=z • (1:H →L[ℂ] H) := by
  obtain ⟨z,hz⟩ := hirr ⟨a,ha⟩ (fun n b => Subtype.ext (hc _ (stage_mem M F n b)))
  exact ⟨z,congrArg Subtype.val hz⟩

include hirr in
lemma generated_factor : FactorCorner.IsFactor (generated M F) := by
  intro a ha hc
  exact generated_irreducible M F hirr a (generated_le M F ha) hc

end Kadison.MatrixTower

end

end
end

end OAI
