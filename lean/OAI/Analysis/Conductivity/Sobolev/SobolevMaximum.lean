import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevTraceChain

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

lemma energy_integrable (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C) (u v : H1) :
    Integrable (fun x => a x*inner ℝ (weakGradient u x) (weakGradient v x)) ballMeasure := by
  apply (L2.integrable_inner (boundedMultiplier ballMeasure a ha C hC hb (weakGradientL u))
    (weakGradientL v)).congr
  filter_upwards [boundedMultiplier_apply_ae ballMeasure a ha C hC hb (weakGradientL u),
    weakGradientL_apply_ae u,weakGradientL_apply_ae v] with x hx hy hz
  rw [hx,hy,hz,real_inner_smul_left]

lemma zero_of_weakGradient_zero {u : H1} (hu : u∈H10)
    (hg : weakGradient u =ᵐ[ballMeasure] 0) : u=0 := by
  have he : weakGradientL u=0 := by
    apply Lp.ext
    filter_upwards [weakGradientL_apply_ae u,hg,Lp.coeFn_zero R3 2 ballMeasure] with x hx hy hz
    rw [hx,hy,hz]
  have hn := H10_norm_le_weakGradientL (⟨u,hu⟩ : H10)
  rw [he,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg u))

lemma chain_zero (F : SmoothLipZero) {v : H1}
    (hv : ∀ᵐ x ∂ballMeasure, F (weakValue v x)=0)
    (hd : ∀ᵐ x ∂ballMeasure, deriv F (weakValue v x)=0) : F.onH1 v=0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [F.onLp_ae v.val,hv,hd,Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx hy hd hz
  change F.onLp v.val x=(0:JetSpace) x
  rw [hx,hz]
  unfold jetSuperposition
  rw [hy,hd,zero_smul,map_zero,map_zero,add_zero]
  rfl

def upperTransitionFun (M r : ℝ) : ℝ := smoothTransition (r-M)

lemma upperTransitionFun_smooth (M : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (upperTransitionFun M) :=
  smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma upperTransitionFun_deriv (M r : ℝ) :
    deriv (upperTransitionFun M) r=deriv smoothTransition (r-M) := by
  change deriv (fun s => smoothTransition (s-M)) r=_
  have hs : ContDiff ℝ (1:ℕ) smoothTransition := smoothTransition.contDiff
  simpa only [mul_one,upperTransitionFun,Function.comp_def,id_eq] using (((hs.differentiable (by simp) (r-M)).hasDerivAt).comp r
    ((hasDerivAt_id r).sub_const M)).deriv

def upperTransition (M : ℝ) (hM : 0≤M) : SmoothLipZero := by
  let C := Classical.choose exists_transition_derivative_bound
  have hc := Classical.choose_spec exists_transition_derivative_bound
  refine ⟨upperTransitionFun M,upperTransitionFun_smooth M,?_,C,by linarith [hc.1],?_⟩
  · exact smoothTransition.zero_of_nonpos (by linarith)
  · intro r
    rw [upperTransitionFun_deriv,Real.norm_eq_abs]
    exact (hc.2 (r-M)).1

lemma upperTransition_nonneg (M : ℝ) (hM : 0≤M) (r : ℝ) : 0≤upperTransition M hM r :=
  smoothTransition.nonneg _

lemma upperTransition_zero_iff (M : ℝ) (hM : 0≤M) (r : ℝ) :
    upperTransition M hM r=0 ↔ r≤M := by
  change smoothTransition (r-M)=0 ↔ r≤M
  rw [smoothTransition.zero_iff_nonpos,sub_nonpos]

lemma upperTransition_deriv_nonneg (M : ℝ) (hM : 0≤M) (r : ℝ) :
    0≤deriv (upperTransition M hM) r := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact smoothTransition.monotone (sub_le_sub_right hxy M)

lemma upperTransition_deriv_zero {M r : ℝ} (hM : 0≤M) (hr : r≤M) :
    deriv (upperTransition M hM) r=0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro s
  rw [(upperTransition_zero_iff M hM r).mpr hr]
  exact upperTransition_nonneg M hM s

theorem harmonic_le_of_trace_le (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    (hp : ∀ᵐ x ∂ballMeasure, 0<a x) {u v : H1}
    (hu : Harmonic a u) (ht : trace u=trace v) {M : ℝ} (hM : 0≤M)
    (hv : ∀ᵐ x ∂ballMeasure, weakValue v x≤M) :
    ∀ᵐ x ∂ballMeasure, weakValue u x≤M := by
  let F := upperTransition M hM
  have hv0 : F.onH1 v=0 := by
    apply chain_zero F
    · filter_upwards [hv] with x hx
      exact (upperTransition_zero_iff M hM _).mpr hx
    · filter_upwards [hv] with x hx
      exact upperTransition_deriv_zero hM hx
  have ht0 : trace (F.onH1 u)=trace (0:H1) := by
    rw [←hv0]; exact chain_trace_eq F ht
  have hh0 : F.onH1 u∈H10 := by
    have hh := (Submodule.Quotient.eq H10).mp ht0
    simpa only [sub_zero] using hh
  have he := hu (F.onH1 u) hh0
  have hg := F.onH1_gradient u
  have hnonneg : 0 ≤ᵐ[ballMeasure] fun x => a x*inner ℝ (weakGradient u x) (weakGradient (F.onH1 u) x) := by
    filter_upwards [hp,hg] with x ha hx
    rw [hx,real_inner_smul_right]
    exact mul_nonneg ha.le (mul_nonneg (upperTransition_deriv_nonneg M hM _) real_inner_self_nonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (energy_integrable a ha C hC hb u (F.onH1 u))).mp he
  have hhg : weakGradient (F.onH1 u) =ᵐ[ballMeasure] 0 := by
    filter_upwards [hp,hg,hzero] with x ha hx hz
    rw [hx,real_inner_smul_right] at hz
    have hh : deriv F (weakValue u x)*inner ℝ (weakGradient u x) (weakGradient u x)=0 :=
      (mul_eq_zero.mp hz).resolve_left ha.ne'
    rcases mul_eq_zero.mp hh with hd | hd
    · rw [hx,hd,zero_smul]; rfl
    · rw [hx,inner_self_eq_zero.mp hd,smul_zero]; rfl
  have hF0 := zero_of_weakGradient_zero hh0 hhg
  have hval := F.onH1_value u
  filter_upwards [hval,Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx hz
  apply (upperTransition_zero_iff M hM _).mp
  rw [←hx,hF0]
  change jetValue ((0:JetSpace) x)=0
  rw [hz]; rfl

lemma harmonic_neg (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {u : H1} (hu : Harmonic a u) : Harmonic a (-u) := by
  intro h hh
  rw [←energyForm_apply a ha C hC hb,map_neg,neg_apply,
    energyForm_apply a ha C hC hb,hu h hh,neg_zero]

lemma weakValue_neg (u : H1) : weakValue (-u) =ᵐ[ballMeasure] -weakValue u := by
  filter_upwards [Lp.coeFn_neg u.val] with point hneg
  change jetValue ((-u.val) point) = -jetValue (u.val point)
  rw [hneg,Pi.neg_apply,map_neg]

theorem harmonic_bounded_of_trace_bounded (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    (hp : ∀ᵐ x ∂ballMeasure, 0<a x) {u v : H1}
    (hu : Harmonic a u) (ht : trace u=trace v) {M : ℝ} (hM : 0≤M)
    (hv : ∀ᵐ x ∂ballMeasure, |weakValue v x|≤M) :
    ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M := by
  have hup := harmonic_le_of_trace_le a ha C hC hb hp hu ht hM
    (hv.mono (fun x hx => (abs_le.mp hx).2))
  have hvneg : ∀ᵐ x ∂ballMeasure, weakValue (-v) x≤M := by
    filter_upwards [hv,weakValue_neg v] with x hx hy
    rw [hy]; exact (neg_le_iff_add_nonneg).mpr (by linarith [(abs_le.mp hx).1])
  have htneg : trace (-u)=trace (-v) := by
    change H10.mkQ (-u)=H10.mkQ (-v)
    simpa only [map_neg,trace] using congrArg Neg.neg ht
  have hlo := harmonic_le_of_trace_le a ha C hC hb hp
    (harmonic_neg a ha C hC hb hu) htneg hM hvneg
  filter_upwards [hup,hlo,weakValue_neg u] with x hx hy hz
  apply abs_le.mpr
  rw [hz,Pi.neg_apply] at hy
  exact ⟨by linarith,hx⟩

end ScalarConductivity

end
end

end OAI
