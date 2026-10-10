import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTwistedTransform

namespace OAI

/-! Uniform support, size and far-left transform bounds from the actual
logarithmic derivative hypotheses on the weight family. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma UniformLogWeights.upper_support {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∀ i x, Real.exp h.radius < x → W i x = 0 := by
  intro i x hx
  by_contra hn
  have hxp : 0 < x := (Real.exp_pos _).trans hx
  have hu : -Real.log x ∈ tsupport (fun u : ℝ => W i (Real.exp (-u))) := by
    apply subset_tsupport
    change W i (Real.exp (-(-Real.log x))) ≠ 0
    simpa only [neg_neg,Real.exp_log hxp] using hn
  have hb := h.support_bound i (-Real.log x) hu
  have hl : Real.log x ≤ h.radius := by
    rw [abs_neg] at hb
    exact (le_abs_self _).trans hb
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hxp] at he
  exact (not_lt_of_ge he) hx

lemma UniformLogWeights.uniform_norm_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, ‖W i x‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := h.derivative_bound 0
  refine ⟨M,hM,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he := hbound i (-Real.log x)
    simpa only [norm_iteratedFDeriv_zero,neg_neg,Real.exp_log hx] using he
  · have hz : W i x = 0 := by
      by_contra hn
      exact hx (h.positive i (subset_tsupport _ hn))
    simpa only [hz,norm_zero] using hM

lemma UniformLogWeights.mellin_polynomial_majorant {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (σ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (t τ : ℝ),
      ‖mellin (W i) (σ+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^N ≤
        mellinEdgeMajorant (C*(1+|t|)^N) τ := by
  obtain ⟨C,hC,hdecay⟩ := h.mellin_decay |σ| (N+2)
  refine ⟨C,hC,?_⟩
  intro i t τ
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin (W i) (σ+(τ:ℂ)*Complex.I)‖*
        ((1+|t|)^N*(1+|τ|)^N))*(1+|τ|)^2 := by
      gcongr
      exact shifted_power_le N τ t
    _ = (1+|t|)^N*((1+|τ|)^(N+2)*‖mellin (W i) (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      ring
    _ ≤ (1+|t|)^N*C := mul_le_mul_of_nonneg_left (hdecay i σ le_rfl τ) (by positivity)
    _ = _ := mul_comm _ _

theorem UniformLogWeights.metaplecticShiftTransform_far_left {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ v : ℝ, 0 < v → ∀ t : ℝ,
      ‖metaplecticShiftTransform ℓ (W i) (1/2-(m:ℝ)) v t‖ ≤
        C*v^(1/2-(m:ℝ))*(1+|t|)^(4*m) := by
  obtain ⟨Cg,hCg,hQ⟩ := metaplecticGamma_half_integer_bound ℓ m
  obtain ⟨Cw,hCw,hdecay⟩ := h.mellin_polynomial_majorant
    (1/2-(m:ℝ)) (4*m)
  let I : ℝ := ∫ τ : ℝ, mellinEdgeMajorant 1 τ
  have hI : 0 ≤ I := integral_nonneg (fun τ => by
    unfold mellinEdgeMajorant
    positivity)
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)‖*Cg*Cw*I,by positivity,?_⟩
  intro i v hv t
  have hb (τ : ℝ) :
      ‖(v:ℂ)^(((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((1/2-(m:ℝ):ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
        mellin (W i) (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ ≤
      (v^(1/2-(m:ℝ))*Cg*Cw*(1+|t|)^(4*m))*mellinEdgeMajorant 1 τ := by
    have he : (((1/2-(m:ℝ):ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
        (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
    have hq := hQ (τ-t)
    rw [←he] at hq
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have hre : (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I).re = 1/2-(m:ℝ) := by simp
    rw [hre]
    calc
      _ ≤ (v^(1/2-(m:ℝ))*(Cg*(1+|τ-t|)^(4*m)))*
          ‖mellin (W i) (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ := by
        gcongr
      _ = (v^(1/2-(m:ℝ))*Cg)*
          (‖mellin (W i) (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(4*m)) := by ring
      _ ≤ (v^(1/2-(m:ℝ))*Cg)*mellinEdgeMajorant (Cw*(1+|t|)^(4*m)) τ :=
        mul_le_mul_of_nonneg_left (hdecay i t τ) (by positivity)
      _ = _ := by unfold mellinEdgeMajorant; ring
  rw [metaplecticShiftTransform,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)‖*
        (∫ τ : ℝ, (v^(1/2-(m:ℝ))*Cg*Cw*(1+|t|)^(4*m))*mellinEdgeMajorant 1 τ) := by
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      exact norm_integral_le_of_norm_le ((mellinEdgeMajorant_integrable 1).const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul]; dsimp [I]; ring


theorem UniformLogWeights.metaplecticTransform_twisted_far_left
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ v : ℝ, 0 < v → ∀ t : ℝ,
      ‖metaplecticTransform ℓ (fun x => W i x*mellinPhase t x) ((m:ℝ)-1/2) v‖ ≤
        C*v^(1/2-(m:ℝ))*(1+|t|)^(4*m) := by
  obtain ⟨C,hC,hbound⟩ := h.metaplecticShiftTransform_far_left ℓ m
  refine ⟨C,hC,?_⟩
  intro i v hv t
  rw [metaplecticTransform_twisted ℓ (W i) _ hv t,norm_mul,mellinPhase_norm,one_mul]
  simpa only [show -((m:ℝ)-1/2) = 1/2-(m:ℝ) by ring] using hbound i v hv t

end CubicFirstMoment

end

end OAI
