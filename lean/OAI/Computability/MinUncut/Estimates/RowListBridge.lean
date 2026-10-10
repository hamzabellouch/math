import Mathlib
import OAI.Computability.MinUncut.Estimates.InnerAssembly
import OAI.Computability.MinUncut.Estimates.FourthTest

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier hiding F₂
open MinUncut.Inner RowNoise
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

attribute [local irreducible] MinUncut.Inner.gradient

lemma oddAtom_iff_labelList {R : Type*} [Fintype R] [DecidableEq R]
    (r : R) (F : (R → Forms A) → ℝ) (D : Rest (W := Forms A) r)
    {θ : ℝ} (hθ : 0<θ) :
    θ≤oddAtom r (AffineMap.const F₂ A 1) F D ↔
      (labelList (fun b => F (joinRow r b D)) θ).Nonempty := by
  constructor
  · intro h
    have he : ∃ α : Module.Dual F₂ (Forms A),
        oddAtom r (AffineMap.const F₂ A 1) F D =
          if α (AffineMap.const F₂ A 1)=1 then |rowCoefficient r F α D| else 0 := by
      obtain ⟨α,_,he⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
        (fun α : Module.Dual F₂ (Forms A) =>
          if α (AffineMap.const F₂ A 1)=1 then |rowCoefficient r F α D| else 0)
      exact ⟨α,he⟩
    obtain ⟨α,he⟩ := he
    rw [he] at h
    split_ifs at h with ho
    · obtain ⟨a,rfl⟩ := oddFrequency_exists_label α ho
      exact ⟨a, (mem_labelList _ θ a).mpr h⟩
    · linarith
  · rintro ⟨a,ha⟩
    exact ((mem_labelList _ θ a).mp ha).trans
      (rowCoefficient_le_oddAtom r (AffineMap.const F₂ A 1)
        F (labelFrequency a) (labelFrequency_odd a) D)

lemma rowAtom_iff_list (f : FoldedProof A) (σ η : ℝ) {θ : ℝ} (hθ : 0<θ)
    (x : Point m n) (i : Fin m)
    (D : Rest (W := Forms A) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) :
    θ≤rowAtom f σ η x i D c ↔
      (labelList (comparisonRow f σ η c x ⟨i,face x i⟩ D) θ).Nonempty :=
  oddAtom_iff_labelList (⟨i,face x i⟩ : Row m n) (fun B => gradient f B σ η c x) D hθ

lemma rowAtomIndicator_eq_list (f : FoldedProof A) (σ η : ℝ) {θ : ℝ} (hθ : 0<θ)
    (x : Point m n) (i : Fin m)
    (D : Rest (W := Forms A) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) :
    rowAtomIndicator f σ η θ x i D c =
      if (labelList (comparisonRow f σ η c x ⟨i,face x i⟩ D) θ).Nonempty then 1 else 0 := by
  simp only [rowAtomIndicator,rowAtom_iff_list f σ η hθ]

end MinUncut.Composition

end
end

end OAI
