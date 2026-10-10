import OAI.NumberTheory.CubicMoment.Estimates.MellinStrip
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

namespace OAI

/-! The contour step for the full smooth character sum. Polynomial
vertical growth is an analytic property of the L-function; the decay,
integrability and vanishing edges are derived for the actual weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

def mellinEdgeMajorant (C t : ℝ) : ℝ := C/(1+|t|)^2

lemma mellinEdgeMajorant_integrable (C : ℝ) : Integrable (mellinEdgeMajorant C) := by
  have hi : Integrable (fun t : ℝ => (1+‖t‖)^(-(2:ℝ))) :=
    integrable_one_add_norm (by norm_num)
  convert hi.const_mul C using 1
  ext t
  rw [mellinEdgeMajorant, Real.rpow_neg (by positivity), Real.rpow_ofNat,
    Real.norm_eq_abs, div_eq_mul_inv]

lemma mellinEdgeMajorant_tendsto (C : ℝ) :
    Tendsto (mellinEdgeMajorant C) atTop (𝓝 0) ∧
      Tendsto (mellinEdgeMajorant C) atBot (𝓝 0) := by
  have h (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
      Tendsto (mellinEdgeMajorant C) l (𝓝 0) := by
    change Tendsto (fun t : ℝ => C/(1+|t|)^2) l (𝓝 0)
    have hp : Tendsto (fun t : ℝ => (1+|t|)⁻¹) l (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun t => by linarith) hl)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0),
      mul_zero] using (hp.pow 2).const_mul C
  exact ⟨h atTop tendsto_abs_atTop_atTop,h atBot tendsto_abs_atBot_atTop⟩

lemma norm_mellinHecke_integrand_le (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ + ((τ-t : ℝ) : ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
          L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K τ := by
  obtain ⟨Cw,hCw,hdecay⟩ := smooth_mellin_strip_decay W hW hpos hsm (|a|+|b|) (N+2)
  let B := Z^b*C*(1+|t|)^N
  have hB : 0 ≤ B := by positivity
  refine ⟨B*Cw,by positivity,?_⟩
  intro σ hσ τ
  have hσabs : |σ| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hσ.1]
    · linarith [le_abs_self b,abs_nonneg a,hσ.2]
  have hscale : ‖(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)‖ ≤ Z^b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Z)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hZ hσ.2
  have hshift : (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hd := abs_sub_le τ 0 t
    simp only [sub_zero,zero_sub,abs_neg] at hd
    nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]
  have hL' : ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤
      C*((1+|t|)^N*(1+|τ|)^N) :=
    (hL σ hσ τ).trans (mul_le_mul_of_nonneg_left hshift hC)
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin W (σ+(τ:ℂ)*Complex.I)‖ * Z^b *
        (C*((1+|t|)^N*(1+|τ|)^N)))*(1+|τ|)^2 := by
      rw [norm_mul,norm_mul]
      gcongr
    _ = B*((1+|τ|)^(N+2)*‖mellin W (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      dsimp [B]
      ring
    _ ≤ B*Cw := mul_le_mul_of_nonneg_left (hdecay σ hσabs τ) hB

/-- Shifting the full Mellin integrand crosses no pole when the
nonprincipal L-function is entire. The weight supplies every required
decay and convergence assertion. -/
theorem mellinHecke_contour_shift (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hab : a ≤ b) (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) (hLd : Differentiable ℂ L) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    (∫ τ : ℝ, mellin W (a+(τ:ℂ)*Complex.I) * (Z:ℂ)^(a+(τ:ℂ)*Complex.I) *
      L (a+((τ-t : ℝ):ℂ)*Complex.I)) =
    ∫ τ : ℝ, mellin W (b+(τ:ℂ)*Complex.I) * (Z:ℂ)^(b+(τ:ℂ)*Complex.I) *
      L (b+((τ-t : ℝ):ℂ)*Complex.I) := by
  let f : ℂ → ℂ := fun s => mellin W s*(Z:ℂ)^s*L (s-(t:ℂ)*Complex.I)
  have hZn : (Z:ℂ) ≠ 0 := by exact_mod_cast (show Z ≠ 0 by linarith)
  have : NeZero (Z:ℂ) := ⟨hZn⟩
  have hf : Differentiable ℂ f :=
    ((smooth_mellin_entire W hW hpos hsm.continuous).mul
      (differentiable_const_cpow_of_neZero _)).mul
      (hLd.comp (differentiable_id.sub_const _))
  obtain ⟨K,_,hbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t L hC N hL
  have heq (σ τ : ℝ) : f (σ+(τ:ℂ)*Complex.I) =
      mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        L (σ+((τ-t : ℝ):ℂ)*Complex.I) := by
    dsimp [f]
    congr 2
    push_cast
    ring
  have hshift := mellin_contour_shift_of_majorant hab f hf.differentiableOn
    (mellinEdgeMajorant K) (mellinEdgeMajorant_integrable K)
    (mellinEdgeMajorant_tendsto K).1 (mellinEdgeMajorant_tendsto K).2
    (by intro σ hσ τ; rw [heq]; exact hbound σ hσ τ)
  simpa only [heq] using hshift

end CubicFirstMoment

end

end OAI
