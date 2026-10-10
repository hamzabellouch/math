import Mathlib
import OAI.Geometry.WeakHessian.Transport.FormAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma FormActionBound.hamiltonJacobi_slope
    {u W : ℝ → Lp ℝ 2 m} {s q A ε : ℝ} {v : Lp ℝ 2 m}
    (hu : HasDerivAt u v s) (hqs : 0 < q+s)
    (hS : Sobolev m (W s : X → ℝ))
    (hΓ : MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hun : ∀ z, s < z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ z, s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : FormActionBound m (fun x => u s x+ε) v A) :
    ∀ r, (A+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < r →
      ∀ᶠ z in 𝓝[>] s, slope (fun t => ⟪W t,u t⟫_ℝ) s z < r := by
  let Γ : Lp ℝ 2 m := hΓ.toLp (fun x => (weakGradient m (W s) x)^2)
  have hΓe : Γ =ᵐ[m] fun x => (weakGradient m (W s) x)^2 := hΓ.coeFn_toLp
  have hpair (z : ℝ) : ⟪Γ,u z⟫_ℝ = ∫ x, u z x*(weakGradient m (W s) x)^2 ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΓe] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real]
  have hρΓ : Integrable (fun x => u s x*(weakGradient m (W s) x)^2) m :=
    (L2.integrable_inner (u s) Γ).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have hE : (∫ x, (u s x+ε)*(weakGradient m (W s) x)^2 ∂m) =
      ⟪Γ,u s⟫_ℝ+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m) := by
    simp_rw [add_mul]
    rw [integral_add hρΓ (hS.2.2.integrable_sq.const_mul ε),integral_const_mul,← hpair s]
  have hAa := hA (W s) hS
  rw [hE,real_inner_comm (W s) v] at hAa
  have hder : HasDerivAt (fun z => ⟪W s,u z⟫_ℝ) ⟪W s,v⟫_ℝ s := by
    simpa using (hasDerivAt_const s (W s)).inner ℝ hu
  have hsl : Tendsto (slope (fun z => ⟪W s,u z⟫_ℝ) s) (𝓝[>] s) (𝓝 ⟪W s,v⟫_ℝ) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hder).2
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] s) (𝓝 s) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun z => -(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      slope (fun z => ⟪W s,u z⟫_ℝ) s z) (𝓝[>] s)
      (𝓝 (-⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ)) := by
    have hdnom : Tendsto (fun z => 2*(q+z)) (𝓝[>] s) (𝓝 (2*(q+s))) :=
      (tendsto_const_nhds.add hid).const_mul 2
    have hpl : Tendsto (fun z => ⟪Γ,u z⟫_ℝ) (𝓝[>] s) (𝓝 ⟪Γ,u s⟫_ℝ) :=
      (continuousAt_const.inner hu.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have HH := (((tendsto_const_nhds (x := -(q+s))).div hdnom
      (by positivity : 2*(q+s) ≠ 0)).mul hpl).add hsl
    convert HH using 1
    congr 1
    field_simp [hqs.ne']
  intro r hr
  have hlt : -⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ < r := by linarith
  filter_upwards [hlim.eventually_lt_const hlt,self_mem_nhdsWithin] with z hz hzs
  change s < z at hzs
  apply lt_of_le_of_lt _ hz
  rw [slope_def_field,slope_def_field]
  apply (div_le_iff₀ (sub_pos.mpr hzs)).mpr
  have hiW : Integrable (fun x => (W z x-W s x)*u z x) m :=
    (L2.integrable_inner (u z) (W z)).sub (L2.integrable_inner (u z) (W s)) |>.congr (by
      filter_upwards [] with x
      simp only [RCLike.inner_apply,RCLike.conj_to_real,Pi.sub_apply]
      ring)
  have hiΓ : Integrable (fun x => (weakGradient m (W s) x)^2*u z x) m :=
    (L2.integrable_inner Γ (u z)).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have H := integral_mono_ae hiW (hiΓ.const_mul (-(z-s)*(q+s)/(2*(q+z)))) (by
    filter_upwards [hHJ z hzs,hun z hzs] with x hx hn
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hx hn)
  have hI : (∫ x, (W z x-W s x)*u z x ∂m) = ⟪W z-W s,u z⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (W z) (W s)] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm,Pi.sub_apply]
  rw [hI,integral_const_mul] at H
  have hIΓ : (∫ x, (weakGradient m (W s) x)^2*u z x ∂m) = ⟪Γ,u z⟫_ℝ := by
    rw [hpair]; congr 1; funext x; ring
  rw [hIΓ,inner_sub_left] at H
  have he : (-(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      (⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ)/(z-s))*(z-s) =
      (-(z-s)*(q+s)/(2*(q+z)))*⟪Γ,u z⟫_ℝ+⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ := by
    field_simp [sub_ne_zero.mpr hzs.ne']; ring
  rw [he]
  linarith

end WeakHessian

end
end

end OAI
