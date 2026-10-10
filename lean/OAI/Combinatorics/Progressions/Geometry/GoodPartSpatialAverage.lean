import OAI.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem mean_norm_complexMean_le (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (f : X → Y → ℂ) :
    q.mean (fun y => ‖p.complexMean (fun x => f x y)‖) ≤
      p.mean (fun x => q.mean (fun y => ‖f x y‖)) := by
  apply (q.mean_mono (fun y => p.norm_complexMean_le_mean_norm (fun x => f x y))).trans_eq
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem mean_norm_goodPart_le (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (Good : X → Prop) (f : ∀ x, Good x → Y → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x hx, q.mean (fun y => ‖f x hx y‖) ≤ ε) :
    q.mean (fun y => ‖p.complexMean (fun x => if hx : Good x then f x hx y else 0)‖) ≤ ε := by
  apply (p.mean_norm_complexMean_le q (fun x y => if hx : Good x then f x hx y else 0)).trans
  apply (p.mean_mono (fun x => ?_)).trans_eq (p.mean_const ε)
  by_cases hx : Good x
  · simpa only [hx, dite_true] using h x hx
  · simpa only [hx, dite_false, norm_zero, q.mean_const] using hε

theorem complexMean_goodPart_test_le (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (Good : X → Prop) (f : ∀ x, Good x → Y → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x hx, q.mean (fun y => ‖f x hx y‖) ≤ ε)
    (φ : Y → ℂ) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ‖q.complexMean (fun y =>
      p.complexMean (fun x => if hx : Good x then f x hx y else 0) * φ y)‖ ≤ ε := by
  apply (q.norm_complexMean_le_mean_norm _).trans
  apply le_trans (q.mean_mono (fun y => ?_)) (p.mean_norm_goodPart_le q Good f hε h)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hφ y)

end Erdos3.FiniteProbabilityWeights

namespace Erdos3

open scoped BigOperators Classical

variable {X K I : Type*} [Fintype X] [Fintype K] [Fintype I]
variable (p : FiniteProbabilityWeights X) (Good : X → Prop)
variable (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z)
variable (f : ∀ x, Good x → (K × I → ℤ) → ℂ)

include hW hZ in
theorem selectedResidue_goodPart_error {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x hx, selectedResidueDensityMass stride cells W (fun z => ‖f x hx z‖) ≤ ε) :
    selectedResidueDensityMass stride cells W
      (fun z => ‖p.complexMean (fun x => if hx : Good x then f x hx z else 0)‖) ≤ ε := by
  have ht := p.mean_norm_goodPart_le (selectedResidueFiniteLaw stride cells W hW hZ) Good
    (fun x hx z => f x hx z.val) hε (fun x hx => by
      rw [selectedResidueFiniteLaw_densityMass stride cells W hW hZ (fun z => ‖f x hx z‖)]
      exact h x hx)
  rw [selectedResidueFiniteLaw_densityMass stride cells W hW hZ
    (fun z => ‖p.complexMean (fun x => if hx : Good x then f x hx z else 0)‖)] at ht
  exact ht

theorem selectedResidue_goodPart_test_error {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x hx, selectedResidueDensityMass stride cells W (fun z => ‖f x hx z‖) ≤ ε)
    (φ : (K × I → ℤ) → ℂ) (hφ : ∀ z, ‖φ z‖ ≤ 1) :
    ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
      (p.complexMean (fun x => if hx : Good x then f x hx z else 0) * φ z)‖ ≤ ε := by
  have ht := p.complexMean_goodPart_test_le (selectedResidueFiniteLaw stride cells W hW hZ) Good
    (fun x hx z => f x hx z.val) hε (fun x hx => by
      rw [selectedResidueFiniteLaw_densityMass stride cells W hW hZ (fun z => ‖f x hx z‖)]
      exact h x hx) (fun z => φ z.val) (fun z => hφ z.val)
  rw [selectedResidueFiniteLaw_complexMean stride cells W hW hZ
    (fun z => p.complexMean (fun x => if hx : Good x then f x hx z else 0) * φ z)] at ht
  exact ht

end Erdos3

end

end OAI
