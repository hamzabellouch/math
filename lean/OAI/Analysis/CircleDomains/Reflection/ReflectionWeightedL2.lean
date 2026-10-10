import OAI.Analysis.CircleDomains.Reflection.RoundReflectionMeasure
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The antiholomorphic Jacobian of circular reflection gives an exact
L2 isometry for its weighted pullback. The one pole is a null set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

def roundReflectionWeight (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  -(r:ℂ)^2/(star (z-c))^2

lemma roundReflectionWeight_measurable (c : ℂ) (r : ℝ) :
    Measurable (roundReflectionWeight c r) :=
  measurable_const.div ((Complex.continuous_conj.measurable.comp (measurable_id.sub_const c)).pow_const 2)

lemma roundReflection_abs_det {c z : ℂ} {r : ℝ} (hz : z≠c) :
    |(fderiv ℝ (roundReflectionPlane c r) z).det|=‖roundReflectionWeight c r z‖^2 := by
  rw [realCLM_det_wirtinger _ _ _ (fderiv_wirtinger _ z),
    (roundReflectionPlane_partials hz).1,(roundReflectionPlane_partials hz).2]
  simp [roundReflectionWeight]

lemma roundReflectionWeighted_memLp (c : ℂ) {r : ℝ} (hr : r≠0)
    {e : ℂ → ℂ} (he : MemLp e 2 volume) :
    MemLp (fun z => e (roundReflectionPlane c r z)*star (roundReflectionWeight c r z)) 2 volume ∧
      (∫z,‖e (roundReflectionPlane c r z)*star (roundReflectionWeight c r z)‖^2)=∫z,‖e z‖^2 := by
  let R := roundReflectionPlane c r
  let A := ({c} : Set ℂ)ᶜ
  have ha : MeasurableSet A := (measurableSet_singleton c).compl
  have ha0 : volume.restrict A=volume :=
    Measure.restrict_eq_self_of_ae_mem (by simpa [A] using volume.ae_ne c)
  have hR := roundReflectionPlane_involutive c hr
  have himage : R '' A=A := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact roundReflectionPlane_ne_center c hr hw
    · intro hz
      exact ⟨R z,roundReflectionPlane_ne_center c hr hz,hR z⟩
  have hd (z : ℂ) (hz : z∈A) : HasFDerivWithinAt R (fderiv ℝ R z) A z :=
    (roundReflectionPlane_differentiable hz).hasFDerivAt.hasFDerivWithinAt
  have hi : IntegrableOn (fun z => ‖e z‖^2) (R '' A) :=
    (he.integrable_norm_pow (p:=2) (by norm_num)).integrableOn
  have hj := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume ha hd
    hR.injective.injOn (fun z => ‖e z‖^2)).mp hi
  let q := fun z => e (R z)*star (roundReflectionWeight c r z)
  have heq : (fun z => |(fderiv ℝ R z).det| • ‖e (R z)‖^2) =ᵐ[volume.restrict A]
      fun z => ‖q z‖^2 := by
    filter_upwards [ae_restrict_mem ha] with z hz
    rw [roundReflection_abs_det hz]
    simp only [q,norm_mul,norm_star,mul_pow,smul_eq_mul,mul_comm]
  have hqi : Integrable (fun z => ‖q z‖^2) volume := by
    have hh := hj.congr heq
    rwa [ha0] at hh
  have hm : AEStronglyMeasurable q volume :=
    (he.aestronglyMeasurable.comp_quasiMeasurePreserving
      (roundReflectionPlane_quasiMeasurePreserving c hr)).mul
      (Complex.continuous_conj.measurable.comp (roundReflectionWeight_measurable c r)).aestronglyMeasurable
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hqi,?_⟩
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume ha hd
    hR.injective.injOn (fun z => ‖e z‖^2)
  rw [himage,ha0] at hh
  rw [←integral_congr_ae (by simpa only [ha0] using heq)]
  exact hh.symm

lemma exists_strong_reflection_pullback (c : ℂ) {r : ℝ} (hr : r≠0)
    (e : ℕ → PlaneL2) (he : Tendsto e atTop (𝓝 0)) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧ ∀n,∀ᵐz ∂volume,
      q n z=e n (roundReflectionPlane c r z)*star (roundReflectionWeight c r z) := by
  let f (n : ℕ) (z : ℂ) := e n (roundReflectionPlane c r z)*star (roundReflectionWeight c r z)
  have hf (n : ℕ) := roundReflectionWeighted_memLp c hr (Lp.memLp (e n))
  let q (n : ℕ) := (hf n).1.toLp (f n)
  have hnorm (n : ℕ) : ‖q n‖=‖e n‖ := by
    have hq : (∫z,‖f n z‖^2)=‖q n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hf n).1.coeFn_toLp] with z hz
      rw [hz,real_inner_self_eq_norm_sq]
    have heq : (∫z,‖e n z‖^2)=‖e n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      exact integral_congr_ae (.of_forall fun z => (real_inner_self_eq_norm_sq (e n z)).symm)
    have hh := (hf n).2
    change (∫z,‖f n z‖^2)=_ at hh
    rw [hq,heq] at hh
    nlinarith [norm_nonneg (q n),norm_nonneg (e n)]
  refine ⟨q,?_,fun n => (hf n).1.coeFn_toLp⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero,hnorm]
  simpa only [norm_zero] using he.norm

end CircleDomainRigidity

end

end OAI
