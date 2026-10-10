import OAI.MeasureTheory.Falconer.Estimates.FinitePopularity

namespace OAI

/-! Popular sums retain a controlled portion of the additive energy.
The threshold and every loss are explicit. -/
namespace Falconer

theorem popular_square_mass {α : Type*} (S : Finset α) (w : α → ℝ)
    {θ M P I : ℝ} (hθ : 0 ≤ θ) (_hM : 0 ≤ M)
    (hw : ∀ x ∈ S, 0 ≤ w x ∧ w x ≤ M)
    (htotal : ∑ x ∈ S, w x ≤ P) (henergy : I ≤ ∑ x ∈ S, (w x)^2) :
    let G := S.filter fun x => θ ≤ w x
    θ*(G.card : ℝ) ≤ P ∧ I-θ*P ≤ M*(∑ x ∈ G, w x) := by
  let G := S.filter fun x => θ ≤ w x
  let D := S.filter fun x => ¬θ ≤ w x
  have hgood : (∑ x ∈ G, w x) ≤ P :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x hx _ => (hw x hx).1)).trans htotal
  have hgcard : θ*(G.card : ℝ) ≤ ∑ x ∈ G, w x := by
    calc
      _ = ∑ _x ∈ G, θ := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
  have hbad : (∑ x ∈ D, (w x)^2) ≤ θ*P := by
    calc
      _ ≤ ∑ x ∈ D, θ*w x := by
        apply Finset.sum_le_sum
        intro x hx
        have hxS := (Finset.mem_filter.mp hx).1
        have hsmall := (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
        nlinarith [(hw x hxS).1]
      _ = θ*∑ x ∈ D, w x := (Finset.mul_sum ..).symm
      _ ≤ θ*P := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x hx _ => (hw x hx).1)).trans htotal) hθ
  have hhigh : (∑ x ∈ G, (w x)^2) ≤ M*∑ x ∈ G, w x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have h := hw x (Finset.mem_filter.mp hx).1
    nlinarith
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun x => θ ≤ w x) (fun x => (w x)^2)
  have hremaining : I-θ*P ≤ M*∑ x ∈ G, w x := by
    change (∑ x ∈ G, (w x)^2)+(∑ x ∈ D, (w x)^2) = _ at hsplit
    linarith
  exact ⟨hgcard.trans hgood,hremaining⟩

end Falconer

end OAI
