import OAI.Geometry.EinsteinFour.Matrix
import OAI.Geometry.EinsteinFour.MomentObstruction
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

/-! The weighted Poisson argument and the scalar weight used to balance the
Weyl moments. The Bochner and Poisson identities imply the exact bound for the test
function, including zero norm values. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter

noncomputable section

/-- The derivative of `H` relative to the derivative of the square root. -/
def derivativeRatio (b : ℝ) : ℝ := 1 + b ^ 2 / 8 - b ^ 4 / 128

theorem hasDerivAt_H {b : ℝ} (hb : 0 < b) :
    HasDerivAt MomentObstruction.H (derivativeRatio b / (2 * Real.sqrt b)) b := by
  have hp : HasDerivAt (fun z : ℝ => 1 + z ^ 2 / 40 - z ^ 4 / 1152)
      (b / 20 - b ^ 3 / 288) b := by
    convert ((((hasDerivAt_id b).pow 2).div_const 40).const_add 1).sub
      (((hasDerivAt_id b).pow 4).div_const 1152) using 1
    · ext z
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  convert (Real.hasDerivAt_sqrt (ne_of_gt hb)).mul hp using 1
  · rfl
  · unfold derivativeRatio
    have hs : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
    field_simp [hs]
    rw [Real.sq_sqrt hb.le]
    ring

/-- The exact quartic remainder makes the squared derivative ratio small. -/
theorem derivativeRatio_bounds {b : ℝ} (hb : 0 ≤ b) (hb2 : b ≤ 2) :
    0 ≤ derivativeRatio b ∧ (derivativeRatio b) ^ 2 ≤ 1 + b ^ 2 / 4 := by
  let z := b ^ 2 / 4
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by dsimp [z]; nlinarith
  have hratio : derivativeRatio b = 1 + z / 2 - z ^ 2 / 8 := by
    dsimp [z, derivativeRatio]
    ring
  have hzz : z ^ 2 ≤ z := by nlinarith
  have hrem : 0 ≤ z ^ 3 * (8 - z) :=
    mul_nonneg (pow_nonneg hz _) (by linarith)
  constructor
  · rw [hratio]
    nlinarith
  · have hid : (1 + z / 2 - z ^ 2 / 8) ^ 2 =
        1 + z - z ^ 3 * (8 - z) / 64 := by ring
    rw [hratio, hid]
    change 1 + z - z ^ 3 * (8 - z) / 64 ≤ 1 + z
    linarith

/-- This formulation is defined even at `b = 0`: the supplied energy is the
squared gradient of `sqrt b`, whose almost-everywhere zero-set convention
comes from the geometric regularization argument. -/
theorem weighted_H_energy_le {v b e : ℝ}
    (hb : 0 ≤ b) (hb2 : b ≤ 2) (he : 0 ≤ e) :
    (derivativeRatio b) ^ 2 * e / (4 + v ^ 2 + b ^ 2) ≤ e / 4 := by
  have hK : 0 < 4 + v ^ 2 + b ^ 2 := by positivity
  apply (div_le_iff₀ hK).2
  have hratio := (derivativeRatio_bounds hb hb2).2
  have hm := mul_le_mul_of_nonneg_right hratio he
  have hv := mul_nonneg (sq_nonneg v) he
  nlinarith

/-- An integral version of the closed two-by-two determinant criterion.
It needs no square-root integrability assumptions. -/
theorem integral_pairing_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g c : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hc : Integrable c μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hpoint : ∀ᵐ ω ∂μ, c ω ^ 2 ≤ f ω * g ω) :
    (∫ ω, c ω ∂μ) ^ 2 ≤ (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  apply (quadratic_form_det_of_nonneg _ _ _ ?_).2.2
  intro x y
  have hnonneg : 0 ≤ ∫ ω, f ω * x ^ 2 + 2 * c ω * x * y + g ω * y ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf0, hg0, hpoint] with ω hfω hgω hcω
    exact quadratic_form_nonneg_of_det _ _ _ hfω hgω hcω x y
  have h1 := integral_add ((hf.mul_const (x ^ 2)).add
    (((hc.const_mul 2).mul_const x).mul_const y)) (hg.mul_const (y ^ 2))
  have h2 := integral_add (hf.mul_const (x ^ 2))
    (((hc.const_mul 2).mul_const x).mul_const y)
  simp only [Pi.add_apply] at h1
  rw [h1, h2] at hnonneg
  simpa only [integral_mul_const, integral_const_mul] using hnonneg

/-- Abstract form of the weighted Poisson proof. For the geometric application,
`f = |grad a|²/K`, `g = K |grad phi|²`, and `c = -<grad a,grad phi>`;
integration by parts gives `E c = Var a`, while the improved Bochner identity
gives `E g ≤ Var a`. Neither geometric identity is assumed to be published. -/
theorem variance_le_of_poisson_pairing {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g c : Ω → ℝ} {V : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hc : Integrable c μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hpoint : ∀ᵐ ω ∂μ, c ω ^ 2 ≤ f ω * g ω)
    (hV : 0 ≤ V) (hpair : (∫ ω, c ω ∂μ) = V)
    (hbochner : (∫ ω, g ω ∂μ) ≤ V) :
    V ≤ ∫ ω, f ω ∂μ := by
  have hF : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae hf0
  have hcs := integral_pairing_sq_le hf hg hc hf0 hg0 hpoint
  rw [hpair] at hcs
  have hmul := mul_le_mul_of_nonneg_left hbochner hF
  by_cases hz : V = 0
  · simpa [hz] using hF
  · have hp : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
    nlinarith

/-- Pointwise Cauchy--Schwarz with the reciprocal Poisson weight. -/
theorem weighted_inner_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a p : E) {K : ℝ} (hK : 0 < K) :
    (-inner ℝ a p) ^ 2 ≤ (‖a‖ ^ 2 / K) * (K * ‖p‖ ^ 2) := by
  have hcs := abs_real_inner_le_norm a p
  have habs : |inner ℝ a p| ^ 2 ≤ (‖a‖ * ‖p‖) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
  have hid : (‖a‖ ^ 2 / K) * (K * ‖p‖ ^ 2) = ‖a‖ ^ 2 * ‖p‖ ^ 2 := by
    field_simp [ne_of_gt hK]
  rw [hid]
  simpa only [neg_sq, sq_abs, mul_pow] using habs

/-- The scalar consequence of the integrated Bochner identity and the
curvature contraction on trace-free Hessians. Here `p` and `s` are squared
gradient and trace-free Hessian norms, and `c` is the curvature contraction.
The two geometric identities are retained separately, rather than assuming
the improved weighted bound as a single premise. -/
theorem bochner_weighted_energy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {v b p s c : Ω → ℝ} {L : ℝ}
    (hp : Integrable p μ) (hs : Integrable s μ) (hc : Integrable c μ)
    (hvp : Integrable (fun ω => (v ω ^ 2 + b ω ^ 2) * p ω) μ)
    (hbochner : L = 4 * (∫ ω, p ω ∂μ) + (4 / 3) * ∫ ω, s ω ∂μ)
    (hcurvature : (∫ ω, c ω ∂μ) = 3 * ∫ ω, (v ω ^ 2 + b ω ^ 2) * p ω ∂μ)
    (hoperator : ∀ᵐ ω ∂μ, c ω ≤ 4 * s ω) :
    (∫ ω, (4 + v ω ^ 2 + b ω ^ 2) * p ω ∂μ) ≤ L := by
  have hbound : (∫ ω, c ω ∂μ) ≤ 4 * ∫ ω, s ω ∂μ := by
    calc
      _ ≤ ∫ ω, 4 * s ω ∂μ := integral_mono_ae hc (hs.const_mul 4) hoperator
      _ = _ := integral_const_mul _ _
  have hid : (fun ω => (4 + v ω ^ 2 + b ω ^ 2) * p ω) =
      (fun ω => 4 * p ω + (v ω ^ 2 + b ω ^ 2) * p ω) := by
    funext ω
    ring
  rw [hid, integral_add (hp.const_mul 4) hvp, integral_const_mul]
  linarith

/-- The weight used in the two-moment obstruction satisfies exactly the
variance bound needed by `balanced_moments`. The hypotheses here separate
the geometric weighted-variance theorem from the integrated norm equation. -/
theorem H_variance_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {v b e : Ω → ℝ}
    (he : Integrable e μ)
    (hweighted : Integrable (fun ω => (derivativeRatio (b ω)) ^ 2 * e ω /
      (4 + v ω ^ 2 + b ω ^ 2)) μ)
    (hb : ∀ᵐ ω ∂μ, b ω ∈ Set.Icc (0 : ℝ) 2)
    (he0 : ∀ᵐ ω ∂μ, 0 ≤ e ω)
    (hvariance : (∫ ω, MomentObstruction.H (b ω) ^ 2 ∂μ) -
      (∫ ω, MomentObstruction.H (b ω) ∂μ) ^ 2 ≤
      ∫ ω, (derivativeRatio (b ω)) ^ 2 * e ω / (4 + v ω ^ 2 + b ω ^ 2) ∂μ)
    (hnorm : (4 / 9) * (∫ ω, e ω ∂μ) ≤
      (∫ ω, b ω ^ 2 ∂μ) - ∫ ω, b ω ∂μ) :
    (∫ ω, MomentObstruction.H (b ω) ^ 2 ∂μ) -
      (∫ ω, MomentObstruction.H (b ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, b ω ^ 2 ∂μ) - ∫ ω, b ω ∂μ) := by
  have henergy : (∫ ω, (derivativeRatio (b ω)) ^ 2 * e ω /
      (4 + v ω ^ 2 + b ω ^ 2) ∂μ) ≤ (∫ ω, e ω ∂μ) / 4 := by
    calc
      _ ≤ ∫ ω, e ω / 4 ∂μ := by
        apply integral_mono_ae hweighted (he.div_const 4)
        filter_upwards [hb, he0] with ω hbω heω
        exact weighted_H_energy_le hbω.1 hbω.2 heω
      _ = _ := integral_div _ _
  linarith

end

end PositiveEinsteinFour.Variance

end OAI
