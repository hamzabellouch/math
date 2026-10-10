import Mathlib
import OAI.Geometry.WeakMTW.Variations.NoFocalCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def brokenAction (K : E × E → ℝ) (e : ℝ → ℝ) (a : ℝ → E)
    (τ ε : ℝ) (z : E) (q : ℝ × E) : ℝ :=
  τ / 2 * e q.1 + K (a q.1,q.2) / ε + K (q.2,z) / ε

 theorem brokenAction_smooth {K : E × E → ℝ} {e : ℝ → ℝ} {a c : ℝ → E}
    (τ ε : ℝ) (z : E)
    (he : ContDiffAt ℝ ∞ e 0) (ha : ContDiffAt ℝ ∞ a 0)
    (hK : ContDiffAt ℝ ∞ K (a 0,c 0)) (hZ : ContDiffAt ℝ ∞ K (c 0,z)) :
    ContDiffAt ℝ ∞ (brokenAction K e a τ ε z) (0,c 0) := by
  exact ((contDiffAt_const.mul (he.comp (0,c 0) contDiffAt_fst)).add
    ((hK.comp (0,c 0) ((ha.comp (0,c 0) contDiffAt_fst).prodMk contDiffAt_snd)).div_const ε)).add
    ((hZ.comp (0,c 0) (contDiffAt_snd.prodMk contDiffAt_const)).div_const ε)

 theorem brokenAction_fderiv {K : E × E → ℝ} {e : ℝ → ℝ} {a c : ℝ → E}
    (τ ε s : ℝ) (z : E) (he : DifferentiableAt ℝ e s) (ha : DifferentiableAt ℝ a s)
    (hK : DifferentiableAt ℝ K (a s,c s)) (hZ : DifferentiableAt ℝ K (c s,z))
    (u : ℝ × E) :
    fderiv ℝ (brokenAction K e a τ ε z) (s,c s) u =
      τ / 2 * (u.1 * deriv e s) +
      fderiv ℝ K (a s,c s) (u.1 • deriv a s,u.2) / ε +
      fderiv ℝ K (c s,z) (u.2,0) / ε := by
  have heq := he.hasFDerivAt.comp (s,c s) (hasFDerivAt_fst (𝕜 := ℝ) (p := (s,c s)))
  have haq := ha.hasFDerivAt.comp (s,c s) (hasFDerivAt_fst (𝕜 := ℝ) (p := (s,c s)))
  have hkq := hK.hasFDerivAt.comp (s,c s) (haq.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := (s,c s))))
  have hzq := hZ.hasFDerivAt.comp (s,c s)
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := (s,c s))).prodMk (hasFDerivAt_const (𝕜 := ℝ) z (s,c s)))
  have hh := ((heq.const_mul (τ/2)).add (hkq.const_mul ε⁻¹)).add (hzq.const_mul ε⁻¹)
  have hfun : brokenAction K e a τ ε z = (fun q : ℝ × E =>
      τ/2 * e q.1 + ε⁻¹ * K (a q.1,q.2) + ε⁻¹ * K (q.2,z)) := by
    funext q; simp only [brokenAction,div_eq_mul_inv]; ring
  rw [hfun]
  have hheq := hh.fderiv
  simp only [Pi.add_def, Function.comp_def] at hheq
  rw [hheq]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, smul_eq_mul, fderiv_eq_smul_deriv]
  change τ / 2 * (u.1 * deriv e s) +
    ε⁻¹ * fderiv ℝ K (a s,c s) (u.1 • deriv a s,u.2) +
    ε⁻¹ * fderiv ℝ K (c s,z) (u.2,0) = _
  ring

 theorem brokenAction_null_momentum {K : E × E → ℝ} {e : ℝ → ℝ} {a c : ℝ → E}
    {p A : ℝ → E →L[ℝ] ℝ} {p' : E →L[ℝ] ℝ} {τ ε : ℝ} {z : E}
    (hε : ε ≠ 0) (he : ContDiffAt ℝ ∞ e 0) (ha : ContDiffAt ℝ ∞ a 0)
    (hc : HasDerivAt c 0 0) (hp : HasDerivAt p p' 0)
    (hK : ContDiffAt ℝ ∞ K (a 0,c 0)) (hZ : ContDiffAt ℝ ∞ K (c 0,z))
    (hm : IsLocalMin (brokenAction K e a τ ε z) (0,c 0))
    (hshort : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ w : E × E,
      fderiv ℝ K (a s,c s) w = ε * (p s w.2 - A s w.1))
    (hgauss : ∀ᶠ s in 𝓝 (0 : ℝ), A s (deriv a s) = τ / 2 * deriv e s) : p' = 0 := by
  let R : E → E →L[ℝ] ℝ := fun y =>
    ε⁻¹ • (fderiv ℝ K (y,z)).comp (ContinuousLinearMap.inl ℝ E E)
  have hR : DifferentiableAt ℝ R (c 0) := by
    have hd := (hZ.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
    have hh : DifferentiableAt ℝ (fun y => (fderiv ℝ K (y,z)).comp
        (ContinuousLinearMap.inl ℝ E E)) (c 0) :=
      (hd.comp (c 0) (differentiableAt_id.prodMk (differentiableAt_const z))).clm_comp
        (differentiableAt_const _)
    exact hh.const_smul ε⁻¹
  have hes : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ e s :=
    ((he.of_le (m := 1) (by simp)).eventually (by simp)).mono (fun _ h => h.differentiableAt (by simp))
  have has : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ a s :=
    ((ha.of_le (m := 1) (by simp)).eventually (by simp)).mono (fun _ h => h.differentiableAt (by simp))
  have hKs : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ K (a s,c s) := by
    have ht : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ 1 K (a s,c s) :=
      (ha.continuousAt.prodMk hc.continuousAt).tendsto ((hK.of_le (m := 1) (by simp)).eventually (by simp))
    exact ht.mono (fun _ h => h.differentiableAt (by simp))
  have hZs : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ K (c s,z) := by
    have ht : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ 1 K (c s,z) :=
      (hc.continuousAt.prodMk continuousAt_const).tendsto ((hZ.of_le (m := 1) (by simp)).eventually (by simp))
    exact ht.mono (fun _ h => h.differentiableAt (by simp))
  apply null_endpoint_null_momentum
    ((brokenAction_smooth τ ε z he ha hK hZ).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hm hc hp hR
  · filter_upwards [hes,has,hKs,hZs,hshort,hgauss] with s hes has hks hzs hss hgs
    rw [brokenAction_fderiv τ ε s z hes has hks hzs (1,0),hss]
    simp only [one_mul,one_smul,← Prod.zero_eq_mk,map_zero,zero_sub,
      mul_neg,neg_div,mul_div_cancel_left₀ _ hε,zero_div,add_zero]
    linarith
  · filter_upwards [hes,has,hKs,hZs,hshort] with s hes has hks hzs hss
    intro w
    rw [brokenAction_fderiv τ ε s z hes has hks hzs (0,w),hss]
    simp only [zero_mul,zero_smul,map_zero,sub_zero,
      mul_div_cancel_left₀ _ hε,R,smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,smul_eq_mul]
    ring

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
