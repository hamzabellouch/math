import OAI.Probability.SLE.AngularLaws
import OAI.Probability.SLE.NearRealContraction

namespace OAI

/-! Nondegenerate waypoint normalization from actual inverse charts and
physical clearance. The existing weak omitted-value estimate is enough;
no sharp conformal-radius comparison is required. -/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

theorem waypoint_derivative_bounds_of_clearance
    (F g : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hiF : InjOn F upperHalfPlane)
    (hg : DifferentiableOn ℂ g D) (hig : InjOn g D)
    (hFD : MapsTo F upperHalfPlane D) (hgH : MapsTo g D upperHalfPlane)
    (hgf : ∀ z ∈ upperHalfPlane, g (F z) = z)
    (z a : ℂ) (s ρ R : ℝ) (hs : 0 < s) (hρ : 0 < ρ)
    (hz : ‖z‖ = 1) (hzs : s ≤ z.im)
    (hclear : ball (F z) ρ ⊆ D) (ha : a ∉ F '' upperHalfPlane)
    (hnear : ‖F z - a‖ ≤ R) :
    ρ / (128 * Real.pi) ≤ ‖deriv F z‖ ∧
      ‖deriv F z‖ ≤ (128 * Real.pi) * R / s := by
  have hzH : z ∈ upperHalfPlane := hs.trans_le hzs
  have hy : 0 < z.im := hzH
  have hC : 0 < 128 * Real.pi := by positivity
  have hball := ball_subset_upperHalfPlane (le_rfl : z.im ≤ z.im)
  have hu := univalent_omitted_value_bound_ball hy (hF.mono hball)
    (hiF.mono hball) a (fun ha' => ha (image_mono hball ha'))
  have hgF : HasDerivAt g (deriv g (F z)) (F z) :=
    (hg.differentiableAt (hD.mem_nhds (hFD hzH))).hasDerivAt
  have hFz := (hF.differentiableAt (isOpen_upperHalfPlane.mem_nhds hzH)).hasDerivAt
  have heq : (g ∘ F) =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_upperHalfPlane.mem_nhds hzH] with w hw
    exact hgf w hw
  have hprod : deriv g (F z) * deriv F z = 1 :=
    ((hgF.comp z hFz).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
  have hnormprod : ‖deriv g (F z)‖ * ‖deriv F z‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have homit : (z.re : ℂ) ∉ g '' ball (F z) ρ := by
    rintro ⟨w, hw, he⟩
    have hh := hgH (hclear hw)
    rw [he] at hh
    simp only [upperHalfPlane, mem_ofPred_eq, Complex.ofReal_im, lt_self_iff_false] at hh
  have hl := univalent_omitted_value_bound_ball hρ (hg.mono hclear)
    (hig.mono hclear) (z.re : ℂ) homit
  have hvertical : ‖g (F z) - (z.re : ℂ)‖ = z.im := by
    rw [hgf z hzH]
    have he : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
  rw [hvertical] at hl
  have hy1 : z.im ≤ 1 := by simpa only [hz] using Complex.im_le_norm z
  constructor
  · apply (div_le_iff₀ hC).mpr
    have hh := mul_le_mul_of_nonneg_right hl (norm_nonneg (deriv F z))
    rw [mul_assoc, hnormprod, mul_one] at hh
    nlinarith [norm_nonneg (deriv F z)]
  · apply (le_div_iff₀ hs).mpr
    have hsu := mul_le_mul_of_nonneg_right hzs (norm_nonneg (deriv F z))
    have hR := mul_le_mul_of_nonneg_left hnear hC.le
    nlinarith

/-- Bounded physical tips, a common clearance ball, and an interior
waypoint angle supply exactly the normal-family normalization constants. -/
theorem waypoint_family_normalization_of_clearance
    (F g : ℕ → ℂ → ℂ) (D : ℕ → Set ℂ) (hD : ∀ n, IsOpen (D n))
    (hF : ∀ n, DifferentiableOn ℂ (F n) upperHalfPlane)
    (hiF : ∀ n, InjOn (F n) upperHalfPlane)
    (hg : ∀ n, DifferentiableOn ℂ (g n) (D n))
    (hig : ∀ n, InjOn (g n) (D n))
    (hFD : ∀ n, MapsTo (F n) upperHalfPlane (D n))
    (hgH : ∀ n, MapsTo (g n) (D n) upperHalfPlane)
    (hgf : ∀ n z, z ∈ upperHalfPlane → g n (F n z) = z)
    (z a : ℕ → ℂ) (s ρ R A : ℝ) (hs : 0 < s) (hρ : 0 < ρ)
    (hz : ∀ n, ‖z n‖ = 1 ∧ s ≤ (z n).im)
    (hclear : ∀ n, ball (F n (z n)) ρ ⊆ D n)
    (ha : ∀ n, a n ∉ F n '' upperHalfPlane)
    (hnear : ∀ n, ‖F n (z n) - a n‖ ≤ R) (htip : ∀ n, ‖a n‖ ≤ A) :
    ∃ m M : ℝ, 0 < m ∧
      (∀ n, ‖F n (z n)‖ ≤ M) ∧
      (∀ n, m ≤ ‖deriv (F n) (z n)‖ ∧ ‖deriv (F n) (z n)‖ ≤ M) ∧
      (∀ n, ‖a n‖ ≤ M) := by
  let M := max A (max (A + R) ((128 * Real.pi) * R / s))
  have hAM : A ≤ M := le_max_left _ _
  have hvalM : A + R ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hderM : (128 * Real.pi) * R / s ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨ρ / (128 * Real.pi), M, by positivity, ?_, ?_, ?_⟩
  · intro n
    calc
      ‖F n (z n)‖ ≤ ‖F n (z n) - a n‖ + ‖a n‖ := by
        simpa only [add_comm] using norm_le_insert' (F n (z n)) (a n)
      _ ≤ R + A := add_le_add (hnear n) (htip n)
      _ = A + R := add_comm _ _
      _ ≤ M := hvalM
  · intro n
    have hb := waypoint_derivative_bounds_of_clearance (F n) (g n) (D n) (hD n)
      (hF n) (hiF n) (hg n) (hig n) (hFD n) (hgH n) (hgf n)
      (z n) (a n) s ρ R hs hρ (hz n).1 (hz n).2 (hclear n) (ha n) (hnear n)
    exact ⟨hb.1, hb.2.trans hderM⟩
  · exact fun n => (htip n).trans hAM

end SLEExactGauge

end

end OAI
