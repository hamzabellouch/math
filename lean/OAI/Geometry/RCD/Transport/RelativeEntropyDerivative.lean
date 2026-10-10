import OAI.Geometry.RCD.Transport.RelativeEntropyIntegral

namespace OAI

/-! # First variation of entropy with a uniform relative quadratic remainder -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem relative_entropy_integral_hasDerivAt_zero {f : ℝ → X → ℝ} {r v : X → ℝ}
    (hr : Measurable r) (hv : Measurable v) (hr0 : ∀ᵐ x ∂μ, 0≤r x)
    (hf0 : ∀ t : ℝ, ∀ᵐ x ∂μ, 0≤f t x) (hzero : f 0=ᵐ[μ]r)
    (hri : Integrable r μ) (hent : Integrable (fun x => r x*Real.log (r x)) μ)
    (hf : ∀ t : ℝ, Integrable (fun x => f t x*Real.log (f t x)) μ)
    {B C : ℝ≥0} (hb : ∀ᵐ x ∂μ, |v x|≤B*r x)
    (he : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂μ, |f t x-r x-t*v x|≤C*t^2*r x) :
    HasDerivAt (fun t : ℝ => ∫ x, f t x*Real.log (f t x) ∂μ)
      (∫ x, (1+Real.log (r x))*v x ∂μ) 0 := by
  let I := ∫ x, r x ∂μ
  let J := ∫ x, |r x*Real.log (r x)| ∂μ
  have hI : 0≤I := integral_nonneg_of_ae hr0
  have hJ : 0≤J := integral_nonneg fun _ => abs_nonneg _
  have hF0 : (∫ x, f 0 x*Real.log (f 0 x) ∂μ)=(∫ x, r x*Real.log (r x) ∂μ) :=
    integral_congr_ae (hzero.fun_comp fun a : ℝ => a*Real.log a)
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let η := ε/(2*((B:ℝ)+1)*(I+1))
  have hη : 0<η := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hunit⟩ := entropy_unit_remainder hη
  have hsmall : η*(B:ℝ)*I≤ε/2 := by
    calc
      _ ≤ η*((B:ℝ)+1)*(I+1) := by gcongr <;> linarith
      _ = ε/2 := by dsimp [η]; field_simp
  let A := (η*(C:ℝ)+(C:ℝ))*I+(C:ℝ)*J
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (B:ℝ)*|t|+(C:ℝ)*t^2<δ := by
    have hc : Continuous (fun t : ℝ => (B:ℝ)*|t|+(C:ℝ)*t^2) := by fun_prop
    exact hc.continuousAt.eventually (Iio_mem_nhds (by
      simpa only [abs_zero,mul_zero,zero_pow (by decide : 2≠0),add_zero] using hδ))
  have hA : ∀ᶠ t : ℝ in 𝓝 0, |t| * A<ε/2 := by
    exact (continuous_abs.mul_const A).continuousAt.eventually
      (Iio_mem_nhds (by simpa only [abs_zero,zero_mul] using half_pos hε))
  filter_upwards [he,hnear,hA] with t he ht hAt
  have hi := relative_entropy_integral_remainder μ hr hv hr0 (hf0 t) hη.le hri hent (hf t) hb he hunit ht
  have hbound : (η*((B:ℝ)*|t|+(C:ℝ)*t^2)+(C:ℝ)*t^2)*I+(C:ℝ)*t^2*J≤ε*|t| := by
    calc
      _ = (η*(B:ℝ)*I+|t| * A)*|t| := by dsimp [A]; rw [←sq_abs t]; ring
      _ ≤ (ε/2+ε/2)*|t| :=
        mul_le_mul_of_nonneg_right (add_le_add hsmall hAt.le) (abs_nonneg t)
      _ = _ := by ring
  simpa only [sub_zero,smul_eq_mul,Real.norm_eq_abs,hF0,mul_comm t] using hi.trans hbound

end RegularPointCoordinates

end

end OAI
