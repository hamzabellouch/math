import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevSmoothTests

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smooth_ball_integration_by_parts {f ψ : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball) (v : R3) :
    (∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure)=
      -(∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := ψ) (g := f) (v := v)
    ((hdψ.mul hf.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
    ((hψ.continuous.mul hdf).integrable_of_hasCompactSupport hc.mul_right)
    ((hψ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  have hl : (∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure)=∫ x, ψ x*fderiv ℝ f x v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)),zero_mul]
  have hr : (∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure)=∫ x, fderiv ℝ ψ x v*f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hs hh))]
    simp
  rw [hl,hr]; exact he

def weakValueL : H1 →L[ℝ] Lp ℝ 2 ballMeasure :=
  (jetValue.compLpL 2 ballMeasure).comp H1Space.subtypeL

lemma weakValueL_apply_ae (u : H1) :
    (weakValueL u : R3 → ℝ) =ᵐ[ballMeasure] weakValue u := jetValue.coeFn_compLp u.val

def weakDirectionL (v : R3) : H1 →L[ℝ] Lp ℝ 2 ballMeasure :=
  ((innerSL ℝ v).compLpL 2 ballMeasure).comp weakGradientL

lemma weakDirectionL_apply_ae (u : H1) (v : R3) :
    (weakDirectionL v u : R3 → ℝ) =ᵐ[ballMeasure] fun x => inner ℝ v (weakGradient u x) := by
  filter_upwards [(innerSL ℝ v).coeFn_compLp (weakGradientL u),weakGradientL_apply_ae u]
    with x hx hy
  exact hx.trans (congrArg (inner ℝ v) hy)

lemma weak_integration_by_parts (u : H1) {ψ : R3 → ℝ}
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆ball) (v : R3) :
    inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v u)=
      -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL u) := by
  have hd {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
      (weakDirectionL v (smoothH1 f hf) : R3 → ℝ) =ᵐ[ballMeasure]
        fun x => fderiv ℝ f x v := by
    filter_upwards [weakDirectionL_apply_ae (smoothH1 f hf) v,smoothH1_gradient f hf]
      with x hx hy
    simp only [hx,hy,inner_gradient_right,RCLike.conj_to_real]
  have hv {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
      (weakValueL (smoothH1 f hf) : R3 → ℝ) =ᵐ[ballMeasure] f :=
    (weakValueL_apply_ae _).trans (smoothH1_value f hf)
  have hsmooth : {z : H1 | z.val∈smoothJets} ⊆
      {z | inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v z)=
        -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL z)} := by
    rintro z ⟨f,hf,hm,he⟩
    have hz : z=smoothH1 f hf := Subtype.ext he
    change inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v z)=
      -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL z)
    rw [hz,L2.inner_def,L2.inner_def]
    have hl : (∫ x, inner ℝ (weakValueL (smoothH1 ψ hψ) x)
        (weakDirectionL v (smoothH1 f hf) x) ∂ballMeasure)=
        ∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hv hψ,hd hf] with x hx hy
      simp only [hx,hy,Real.inner_apply]
    have hr : (∫ x, inner ℝ (weakDirectionL v (smoothH1 ψ hψ) x)
        (weakValueL (smoothH1 f hf) x) ∂ballMeasure)=
        ∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hd hψ,hv hf] with x hx hy
      simp only [hx,hy,Real.inner_apply]
    rw [hl,hr]
    exact smooth_ball_integration_by_parts hf hψ hc hs v

  exact (closure_minimal hsmooth (isClosed_eq
    (continuous_const.inner (weakDirectionL v).continuous)
    ((continuous_const.inner weakValueL.continuous).neg))) (smoothH1_dense u)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma weakDirection_zero_of_value_zero (u : H1)
    (hu : weakValue u =ᵐ[ballMeasure] 0) (v : R3) : weakDirectionL v u=0 := by
  have huv : weakValueL u=0 := Lp.ext (((weakValueL_apply_ae u).trans hu).trans (Lp.coeFn_zero ℝ 2 ballMeasure).symm)
  have hi : Integrable (weakDirectionL v u : R3 → ℝ) ballMeasure :=
    (Lp.memLp _).integrable (by norm_num)
  have hz := (Metric.isOpen_ball : IsOpen ball).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hi.locallyIntegrable.locallyIntegrableOn ball) (fun ψ hψ hc hs => ?_)
  · apply Lp.ext
    filter_upwards [hz,ae_restrict_mem (Metric.isOpen_ball.measurableSet : MeasurableSet ball),
      Lp.coeFn_zero ℝ 2 ballMeasure] with x hx hb hzero
    exact (hx hb).trans hzero.symm
  · have h := weak_integration_by_parts u hψ hc hs v
    rw [huv,inner_zero_right,neg_zero,L2.inner_def] at h
    rw [←h]
    apply integral_congr_ae
    filter_upwards [(weakValueL_apply_ae _).trans (smoothH1_value ψ hψ)] with x hx
    simp only [hx,Real.inner_apply,smul_eq_mul]

lemma h1_eq_zero_of_value_zero (u : H1) (hu : weakValue u =ᵐ[ballMeasure] 0) : u=0 := by
  have hg (i : Fin 3) : ∀ᵐ x ∂ballMeasure, weakGradient u x i=0 := by
    have he := weakDirection_zero_of_value_zero u hu (EuclideanSpace.single i 1)
    filter_upwards [weakDirectionL_apply_ae u (EuclideanSpace.single i 1),
      ((Lp.ext_iff.mp he).trans (Lp.coeFn_zero ℝ 2 ballMeasure))] with x hx hy
    have hh : inner ℝ (EuclideanSpace.single i 1) (weakGradient u x)=0 := hx.symm.trans hy
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using hh
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hu,ae_all_iff.mpr hg,Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx hy hzero
  change weakValue u x=0 at hx
  change (0 : JetSpace) x=0 at hzero
  have hwg : weakGradient u x=0 := by ext i; exact hy i
  calc
    u.val x = jetLiftValue (jetValue (u.val x)) + jetLiftGradient (jetGradient (u.val x)) :=
      jetFiber_decomposition _
    _ = 0 := by change jetLiftValue (weakValue u x)+jetLiftGradient (weakGradient u x)=0
                rw [hx,hwg,map_zero,map_zero,add_zero]
    _ = (0 : JetSpace) x := hzero.symm

lemma weakValueL_injective : Function.Injective weakValueL := by
  intro u v huv
  have he : weakValueL (u-v)=0 := by rw [map_sub,huv,sub_self]
  have hz : weakValue (u-v) =ᵐ[ballMeasure] 0 :=
    (weakValueL_apply_ae _).symm.trans ((Lp.ext_iff.mp he).trans (Lp.coeFn_zero ℝ 2 ballMeasure))
  exact sub_eq_zero.mp (h1_eq_zero_of_value_zero _ hz)

lemma nonzero_h1_positive_value_measure {u : H1} (hu : u≠0) :
    0<ballMeasure {x | weakValue u x≠0} := by
  by_contra h
  have hz : ballMeasure {x | weakValue u x≠0}=0 := le_zero_iff.mp (not_lt.mp h)
  have he : weakValue u =ᵐ[ballMeasure] 0 := by
    rw [Filter.EventuallyEq,ae_iff]
    exact hz
  exact hu (h1_eq_zero_of_value_zero u he)

end ScalarConductivity

end
end

end OAI
