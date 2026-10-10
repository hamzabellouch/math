import OAI.Geometry.RCD.Sobolev.LocalWeakMaximal
import OAI.Geometry.RCD.Metric.ModelFiveBallBound
import OAI.Geometry.RCD.Metric.ModelScaleControl

namespace OAI

/-! # The local maximal estimate for the actual RCD measure -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

def fiveBallConstant (n : ℕ) : ℝ := Real.cosh 1^(n-1)*5^n

theorem NoncollapsedRCD.five_ball_doubling {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {R : ℝ} (hR : 0 < R)
    (hcurv : -1 ≤ K*(5*R)^2) :
    ∀ x r, 0 < r → r ≤ R → (hausdorff n X).real (ball x (5*r)) ≤
      fiveBallConstant n*(hausdorff n X).real (ball x r) := by
  obtain ⟨a,ha,hBG,hscale⟩ := hX.model_comparison_with_scale_control hn
  have haR : a*(5*R) ≤ 1 := by
    have hh := hscale (5*R/3) (by positivity) (by nlinarith [hcurv])
    simpa only [show 3*(5*R/3)=5*R by ring] using hh
  have hc : Real.cosh (a*(5*R)) ≤ Real.cosh 1 := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity),abs_one]
    exact haR
  intro x r hr hrR
  apply (model_five_ball_bound (hausdorff n X) (by omega) ha hBG x hr hrR).trans
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.cosh_pos _).le hc _) (by positivity)

theorem NoncollapsedRCD.local_weak_maximal {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {R t : ℝ} (hR : 0 < R) (hcurv : -1 ≤ K*(5*R)^2) (ht : 0 < t)
    {f : X → ℝ} (hf : Integrable f (hausdorff n X))
    (hf0 : ∀ᵐ x ∂hausdorff n X, 0 ≤ f x) (p : X) :
    (hausdorff n X).real (ball p R ∩ ballAverageBad (hausdorff n X) f R t) ≤
      (fiveBallConstant n/t)*∫ y, f y ∂hausdorff n X :=
  RegularPointCoordinates.local_weak_maximal (hausdorff n X) hf hf0
    (fun _ _ => (hX.finiteOnBounded _ isBounded_ball).ne) p
    (by unfold fiveBallConstant; positivity) ht (hX.five_ball_doubling hn hR hcurv)

theorem NoncollapsedRCD.local_maximal_good_set {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : X) {R t : ℝ} (hR : 0 < R) (hcurv : -1 ≤ K*(5*R)^2) (ht : 0 < t)
    {f : X → ℝ} (hf : IntegrableOn f (ball p (2*R)) (hausdorff n X))
    (hf0 : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (2*R)), 0 ≤ f x) :
    ∃ U : Set X, IsCompact U ∧ U ⊆ closedBall p R ∧
      (hausdorff n X).real (ball p R \ U) ≤
        (fiveBallConstant n/t)*∫ y in ball p (2*R), f y ∂hausdorff n X ∧
      ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
        ∫ y in ball x r, f y ∂hausdorff n X ≤ t*(hausdorff n X).real (ball x r) := by
  let μ := hausdorff n X
  let Ω := ball p (2*R)
  let F := Ω.indicator f
  have hF : Integrable F μ := hf.integrable_indicator measurableSet_ball
  have hF0 : ∀ᵐ x ∂μ, 0 ≤ F x := by
    have hh := (ae_restrict_iff' measurableSet_ball).mp hf0
    filter_upwards [hh] with x hx
    by_cases h : x ∈ Ω
    · simpa only [F,indicator_of_mem h] using hx h
    · simp only [F,indicator_of_notMem h,le_refl]
  let U := closedBall p R \ ballAverageBad μ F R t
  have hU : IsCompact U := (isCompact_closedBall (x := p) (r := R)).diff
    (isOpen_ballAverageBad μ hF hF0 (fun _ _ => (hX.finiteOnBounded _ isBounded_ball).ne) ht.le)
  refine ⟨U,hU,sdiff_subset,?_,?_⟩
  · have he : ball p R \ U = ball p R ∩ ballAverageBad μ F R t := by
      ext x
      constructor
      · rintro ⟨hx,hxu⟩
        exact ⟨hx,by by_contra hb; exact hxu ⟨ball_subset_closedBall hx,hb⟩⟩
      · rintro ⟨hx,hxb⟩
        exact ⟨hx,fun h => h.2 hxb⟩
    rw [he]
    simpa only [F,Ω,integral_indicator measurableSet_ball] using
      hX.local_weak_maximal hn hR hcurv ht hF hF0 p
  · intro x hx r hr hrR
    have hnobad : x ∉ ballAverageBad μ F R t := hx.2
    have hav : ∫ y in ball x r, F y ∂μ ≤ t*μ.real (ball x r) := by
      by_contra hh
      exact hnobad ⟨r,hr,hrR,lt_of_not_ge hh⟩
    have hsub : ball x r ⊆ Ω := by
      intro y hy
      have hd := dist_triangle y x p
      have hyx : dist y x < r := hy
      have hxp : dist x p ≤ R := hx.1
      change dist y p < 2*R
      linarith
    have he : (∫ y in ball x r, F y ∂μ) = ∫ y in ball x r, f y ∂μ := by
      change (∫ y in ball x r, Ω.indicator f y ∂μ) = _
      rw [setIntegral_indicator measurableSet_ball,inter_eq_left.mpr hsub]
    rwa [he] at hav

end RegularPointCoordinates

end

end OAI
