import OAI.Geometry.RCD.Metric.RescaledFiniteNets

namespace OAI

/-! # Uniform cardinality of separated centers in a rescaled ball -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A finer covering net bounds every separated family in a fixed
rescaled ball. In particular it bounds overlap of enlarged patch balls. -/
theorem NoncollapsedRCD.rescaled_separated_card {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {R : ℝ} (hR : 0 < R) :
    ∃ N : ℕ, ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∀ s : Finset X,
      (s : Set X).Pairwise (fun x y => r ≤ dist x y) →
      (∀ x ∈ s, dist x p ≤ R*r) → s.card ≤ N := by
  classical
  obtain ⟨N, hN⟩ := hX.rescaled_finite_nets hn hR (by norm_num : (0:ℝ)<1/4)
  refine ⟨N, ?_⟩
  intro p r hr hcurv s hsep hnear
  obtain ⟨t, htN, _, hcover⟩ := hN p r hr hcurv
  have hselect (x : s) : ∃ y ∈ t, dist x.val y < (1/4:ℝ)*r :=
    hcover x.val (hnear x.val x.property)
  choose f hft hfd using hselect
  let F : s → t := fun x => ⟨f x, hft x⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hdist := hsep x.property y.property hne
    have heq : f x = f y := congrArg Subtype.val hxy
    have htriangle := dist_triangle x.val (f x) y.val
    rw [heq, dist_comm (f y) y.val] at htriangle
    have hx := hfd x
    have hy := hfd y
    rw [heq] at hx
    linarith
  have hcard := Fintype.card_le_of_injective F hF
  simp only [Fintype.card_coe] at hcard
  exact hcard.trans htN

end RegularPointCoordinates

end

end OAI
