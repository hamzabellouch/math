import OAI.MeasureTheory.Falconer.Geometry.CommonRectangles
import OAI.MeasureTheory.Falconer.Estimates.ScalarRatioCard

namespace OAI

/-! The large rectangles from the scalar energy refinement have a common
reference set with small ratio projections. -/
namespace Falconer
open scoped Pointwise

 theorem common_small_ratio_projections {α : Type*} {δ ρ L : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ) (c : α → ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card : ℝ) ≤ ((A i).card : ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card : ℝ) ≤ ((B i).card : ℝ))
    (M : ℕ) (hc : ∀ i ∈ I, c i ≠ 0 ∧ |c i| ≤ M ∧ |(c i)⁻¹| ≤ M)
    (hproj : ∀ i ∈ I,
      ((scalarCells δ (A i+(B i).image (fun y => c i*y))).card : ℝ) ≤ L) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card : ℝ) ≤ 2*(J.card : ℝ) ∧
      ∀ j ∈ J,
        ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card : ℝ)*
          ρ^12*(X.card : ℝ)*(Y.card : ℝ)^2 ≤
            4096*(2*(M*M)+3)*(2*M+3)^2*L^4 := by
  classical
  obtain ⟨i₀,hi₀,J,hJI,hJ,hoverlap⟩ := common_rectangular_subsets I X Y A B
    hI hX hY hρ hA hB hsizeA hsizeB
  refine ⟨i₀,hi₀,J,hJI,hJ,?_⟩
  intro j hj
  have hjI := hJI hj
  let Xj := A i₀ ∩ A j
  let Yj := B i₀ ∩ B j
  have hXj : Xj ⊆ X := Finset.inter_subset_left.trans (hA i₀ hi₀)
  have hYj : Yj ⊆ Y := Finset.inter_subset_left.trans (hB i₀ hi₀)
  have h0 : ((scalarCells δ (A i₀+Yj.image (fun y => c i₀*y))).card : ℝ) ≤ L :=
    (Nat.cast_le.mpr (Finset.card_le_card (scalarCells_mono δ
      (Finset.add_subset_add (Finset.Subset.refl _) (Finset.image_subset_image
        (show Yj ⊆ B i₀ from Finset.inter_subset_left)))))).trans (hproj i₀ hi₀)
  have h1 : ((scalarCells δ (Xj+Yj.image (fun y => c j*y))).card : ℝ) ≤ L :=
    (Nat.cast_le.mpr (Finset.card_le_card (scalarCells_mono δ
      (Finset.add_subset_add (show Xj ⊆ A j from Finset.inter_subset_right)
        (Finset.image_subset_image (show Yj ⊆ B j from Finset.inter_subset_right)))))).trans (hproj j hjI)
  have hr : |c j/c i₀| ≤ (M*M : ℕ) := by
    rw [div_eq_mul_inv,abs_mul,Nat.cast_mul]
    exact mul_le_mul (hc j hjI).2.1 (hc i₀ hi₀).2.2 (abs_nonneg _) (Nat.cast_nonneg _)
  have ht := scalar_ratio_card_bound hδ hL (hc i₀ hi₀).1 (hc j hjI).1
    (A i₀) Xj Yj (show Xj ⊆ A i₀ from Finset.inter_subset_left)
    (fun x hx y hy hxy => hXsep x (hXj hx) y (hXj hy) hxy)
    (fun x hx y hy hxy => hYsep x (hYj hx) y (hYj hy) hxy)
    (div_mul_cancel₀ (c j) (hc i₀ hi₀).1) M (M*M) (hc i₀ hi₀).2.2 (hc j hjI).2.2 hr h0 h1
  have hh := scalar_ratio_card_lower (by positivity : 0 ≤
      ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card : ℝ))
    (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card)
    (hoverlap j hj).1 (hoverlap j hj).2 ht
  convert hh using 1
  push_cast
  ring

end Falconer

end OAI
