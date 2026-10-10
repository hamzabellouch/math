import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.MarkedMomentBound

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.KernelSimilarity
open ExactSLEMain ExactSLEGenerator ExactSLEGreen ExactSLEKernel

lemma pi_restrict_mono {K L : Set ℂ} (h : K⊆L) (m : ℕ) :
    Measure.pi (fun _ : Fin m=>volume.restrict K) ≤
      Measure.pi (fun _ : Fin m=>volume.restrict L) := by
  rw [←Measure.restrict_pi_pi,←Measure.restrict_pi_pi]
  exact Measure.restrict_mono (Set.pi_mono (fun _ _=>h)) le_rfl

lemma normalization_cancel (α C B : ℝ) (hC : 0≤C) (hB : 0≤B)
    {y r : ℝ} (hy : 0<y) (hr : 0<r) (m : ℕ) :
    ENNReal.ofReal (C*(2*(y*r))^α)*
      ((ENNReal.ofReal (B*y^(α-2)))^m*
        (ENNReal.ofReal y)^(2*(m:ℝ)-α*((m:ℝ)+1)))=
      ENNReal.ofReal (C*2^α)*(ENNReal.ofReal B)^m*ENNReal.ofReal (r^α) := by
  have hy0 : ENNReal.ofReal y≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr hy)
  have hypow : (ENNReal.ofReal y)^α*
      (((ENNReal.ofReal y)^(α-2))^m*
        (ENNReal.ofReal y)^(2*(m:ℝ)-α*((m:ℝ)+1)))=1 := by
    rw [←ENNReal.rpow_natCast,←ENNReal.rpow_mul,
      ←ENNReal.rpow_add _ _ hy0 ENNReal.ofReal_ne_top,
      ←ENNReal.rpow_add _ _ hy0 ENNReal.ofReal_ne_top,
      show α+((α-2)*(m:ℝ)+(2*(m:ℝ)-α*((m:ℝ)+1)))=0 by ring,
      ENNReal.rpow_zero]
  rw [show 2*(y*r)=y*(2*r) by ring,
    Real.mul_rpow hy.le (by positivity),Real.mul_rpow (by norm_num : (0:ℝ)≤2) hr.le,
    ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _),
    ENNReal.ofReal_mul hB,mul_pow,
    ENNReal.ofReal_mul hC]
  simp_rw [←ENNReal.ofReal_rpow_of_pos hy]
  calc
    _ = (ENNReal.ofReal (C)*ENNReal.ofReal (2^α)*(ENNReal.ofReal B)^m*
        ENNReal.ofReal (r^α))*
      ((ENNReal.ofReal y)^α*(((ENNReal.ofReal y)^(α-2))^m*
        (ENNReal.ofReal y)^(2*(m:ℝ)-α*((m:ℝ)+1)))) := by ring
    _ = _ := by rw [hypow,mul_one]

lemma affine_im_real (x : ℝ) {y : ℝ} (hy : 0<y) (z : ℂ) :
    (affine (x:ℂ) y hy z).im=y*z.im := by
  simp [Complex.mul_im]

 

theorem actual_normalized_hit_moment_bound (a : ℝ) (ha : 1/4<a)
    (m : ℕ) (hm : 1 ≤ m) (K : Set ℂ) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (c : ℝ) (hc : 0<c) (hc2 : c≤2)
    (hcK : ∀z∈K,c≤2*z.im) (B : ℝ) (hB : 0≤B) :
    ∃D : ℝ≥0∞,D<∞ ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W →
      ∀(x y : ℝ) (hy : 0<y) (f : C_c(UpperPlane,ℝ)),
      (Subtype.val '' tsupport f ⊆ affine (x:ℂ) y hy '' K) →
      (∀z : UpperPlane,‖f z‖≤B*y^(alpha a-2)) →
      ∀(s : ℕ→Finset ℕ) (coeff : ℕ→ℕ→ℝ),
      (∀k j,j∈s k→0≤coeff k j) → (∀k,∑j∈s k,coeff k j=1) →
      ∀(t : ℝ≥0∞) (μ : ExactSLEGenerator.Driver→Measure UpperPlane),
      (∀ᵐ b∂W,Tendsto (fun k=>∑j∈s k,coeff k j*
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) t b)
          atTop (𝓝 (∫z,f z∂μ b))) →
      ∀r : ℝ,0<r → r≤1 →
        (∫⁻b in {b | radialTime a b.1 (affine (x:ℂ) y hy Complex.I) (y*r)<∞},
          ‖∫z,f z∂μ b‖ₑ^m∂W)≤D*ENNReal.ofReal (r^(alpha a)) := by
  obtain ⟨C,hC,hCb⟩ := actual_hit_radon_moment_bound a ha m hm
  have halpha : alpha a<1 := by
    have ha0 : 0<a := by linarith
    have hp : 0<1/(4*a) := by positivity
    dsimp [alpha]; linarith
  obtain ⟨D₀,hD₀,hD₀b⟩ := capped_distance_fixed_center (alpha a) c
    (alpha_pos ha) halpha hc m K {Complex.I} hK hKb isCompact_singleton.isBounded
  let I := ∫⁻z : Fin m→ℂ,kernel (alpha a) c (Fin.cons Complex.I z)
    ∂Measure.pi (fun _=>volume.restrict K)
  have hI : I<∞ := (hD₀b Complex.I (mem_singleton _)).trans_lt hD₀
  refine ⟨ENNReal.ofReal (C*2^(alpha a))*(ENNReal.ofReal B)^m*I,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) hI,?_⟩
  intro W hprob hW x y hy f hsupport hf s coeff hcoeff hsum t μ hlim r hr hr1
  let T := affine (x:ℂ) y hy
  let Kf := Subtype.val '' tsupport f
  let ν := Measure.pi (fun _ : Fin m=>volume.restrict Kf)
  have hKf : IsCompact Kf := f.hasCompactSupport.image continuous_subtype_val
  have hcap (z : UpperPlane) (hz : z∈tsupport f) : y*c≤2*z.1.im := by
    obtain ⟨w,hw,hew⟩ := hsupport ⟨z,hz,rfl⟩
    have hi := hcK w hw
    rw [←hew,affine_im_real]
    nlinarith
  have hzc : y*c≤2*(T Complex.I).im := by
    simp only [T,affine_im_real,Complex.I_im,mul_one]
    nlinarith
  obtain ⟨_,hbound⟩ := hCb W hW f (y*c) (mul_pos hy hc) hcap (T Complex.I) hzc
  have hmker : Measurable (fun z : Fin m→ℂ=>kernel (alpha a) (y*c)
      (Fin.cons (T Complex.I) z)) :=
    (measurable_kernel (alpha_pos ha).le _).comp (by fun_prop)
  have hKae : ∀ᵐ z∂ν,∀i,z i∈Kf := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin m=>volume.restrict Kf) (i:=i)).eventually
      (ae_restrict_mem hKf.measurableSet)
  have hA :
      (∫⁻z : Fin m→ℂ,(∏i,ENNReal.ofReal ‖upperExtension f (z i)‖)*
        kernel (alpha a) (y*c) (Fin.cons (T Complex.I) z)∂ν)≤
      (ENNReal.ofReal (B*y^(alpha a-2)))^m*
        ((ENNReal.ofReal y)^(2*(m:ℝ)-alpha a*((m:ℝ)+1))*I) := by
    calc
      _ ≤ ∫⁻z : Fin m→ℂ,(ENNReal.ofReal (B*y^(alpha a-2)))^m*
          kernel (alpha a) (y*c) (Fin.cons (T Complex.I) z)∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hKae] with z hz
        apply mul_le_mul' _ le_rfl
        have hprod : (∏i : Fin m,ENNReal.ofReal ‖upperExtension f (z i)‖)≤
            ∏i : Fin m,ENNReal.ofReal (B*y^(alpha a-2)) := by
          apply Finset.prod_le_prod₀ (fun _ _ => bot_le)
          intro i hi
          obtain ⟨w,hw,hew⟩ := hz i
          exact ENNReal.ofReal_le_ofReal (by rw [←hew,upperExtension_apply]; exact hf w)
        simpa using hprod
      _ = (ENNReal.ofReal (B*y^(alpha a-2)))^m*
          ∫⁻z : Fin m→ℂ,kernel (alpha a) (y*c) (Fin.cons (T Complex.I) z)∂ν :=
        lintegral_const_mul _ hmker
      _ ≤ (ENNReal.ofReal (B*y^(alpha a-2)))^m*
          ∫⁻z : Fin m→ℂ,kernel (alpha a) (y*c) (Fin.cons (T Complex.I) z)
          ∂Measure.pi (fun _=>volume.restrict (T '' K)) := by
        apply mul_le_mul' le_rfl
        exact lintegral_mono' (pi_restrict_mono hsupport m) le_rfl
      _ = _ := by rw [fixed_center_integral_affine (alpha a) c (alpha_pos ha).le (x:ℂ) Complex.I hy hK]
  calc
    _ ≤ ENNReal.ofReal (C*(2*(y*r))^(alpha a))*
        ∫⁻z : Fin m→ℂ,(∏i,ENNReal.ofReal ‖upperExtension f (z i)‖)*
          kernel (alpha a) (y*c) (Fin.cons (T Complex.I) z)∂ν :=
      hbound s coeff hcoeff hsum t μ hlim (y*r) (mul_pos hy hr) (by
        simp only [T,affine_im_real,Complex.I_im,mul_one]
        exact mul_le_of_le_one_right hy.le hr1)
    _ ≤ ENNReal.ofReal (C*(2*(y*r))^(alpha a))*
        ((ENNReal.ofReal (B*y^(alpha a-2)))^m*
          ((ENNReal.ofReal y)^(2*(m:ℝ)-alpha a*((m:ℝ)+1))*I)) :=
      mul_le_mul' le_rfl hA
    _ = (ENNReal.ofReal (C*(2*(y*r))^(alpha a))*
        ((ENNReal.ofReal (B*y^(alpha a-2)))^m*
          (ENNReal.ofReal y)^(2*(m:ℝ)-alpha a*((m:ℝ)+1))))*I := by ring
    _ = _ := by rw [normalization_cancel (alpha a) C B hC.le hB hy hr m]; ring

end SLEExactGauge.KernelSimilarity
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen KernelSimilarity

lemma radialWeight_measurable (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (r : ℝ) (hr : 0<r) (hr1 : r≤1) :
    Measurable (fun b : ExactSLEGenerator.Driver => radialWeight a b.1 z (z.im*r)) :=
  (joint_radialWeight_measurable a ha r hr hr1).comp
    (measurable_id.prodMk (measurable_const (a:= (⟨z,hz⟩ : UpperPlane))))

 

lemma radialLaw_lintegral_le_hit (W : Measure ExactSLEGenerator.Driver)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (r : ℝ) (hr : 0<r) (hr1 : r≤1)
    (g : ExactSLEGenerator.Driver→ℝ≥0∞) (hg : Measurable g) :
    (∫⁻b,g b∂radialLaw W a z (z.im*r))≤
      ENNReal.ofReal ((z.im*r)^(-alpha a)/physicalGreen a (z,0))*
        ∫⁻b in {b | radialTime a b.1 z (z.im*r)<∞},g b∂W := by
  have hρ : 0<z.im*r := mul_pos hz hr
  have hρz : z.im*r≤z.im := mul_le_of_le_one_right hz.le hr1
  have hG : 0<physicalGreen a (z,0) := Real.exp_pos _
  have hm := ((radialWeight_measurable a ha z hz r hr hr1).div_const
    (physicalGreen a (z,0))).ennreal_ofReal
  have hS := radialTime_stopping a (by linarith) z hz _ hρ hρz
  have hmT : Measurable (fun b : ExactSLEGenerator.Driver => radialTime a b.1 z (z.im*r)) := hS.measurable'
  have hE : MeasurableSet {b : ExactSLEGenerator.Driver | radialTime a b.1 z (z.im*r)<∞} :=
    measurableSet_lt hmT measurable_const
  rw [radialLaw,lintegral_withDensity_eq_lintegral_mul W hm hg,
    ←lintegral_indicator hE,←lintegral_const_mul _ (hg.indicator hE)]
  apply lintegral_mono
  intro b
  change _*g b≤_
  by_cases hb : radialTime a b.1 z (z.im*r)<∞
  · simp only [Set.indicator,Set.mem_ofPred_eq,hb,ite_true]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ hG.le
    have h := (radialWeight_bound a ha z hz _ hρ hρz b).2
    calc
      _ ≤ Real.exp (-alpha a*Real.log (z.im*r)) := h
      _ = _ := by rw [Real.rpow_def_of_pos hρ]; congr 1; ring
  · simp only [Set.indicator,Set.mem_ofPred_eq,hb,ite_false,mul_zero]
    have ht : radialTime a b.1 z (z.im*r)=∞ := top_le_iff.mp (not_lt.mp hb)
    simp [radialWeight,ht]

lemma center_affine (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) :
    fromDisk θ 0=affine (Real.cos θ:ℂ) (Real.sin θ)
      (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) Complex.I := by
  rw [fromDisk_zero,mul_comm Complex.I,Complex.exp_ofReal_mul_I]
  rfl

lemma tilt_cancel (α p : ℝ) {y r : ℝ} (hy : 0<y) (hr : 0<r) :
    ENNReal.ofReal ((y*r)^(-α)/(y^(-α)*y^p))*ENNReal.ofReal (r^α)=
      ENNReal.ofReal (y^(-p)) := by
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow hy.le hr.le,Real.rpow_neg hy.le p,
    show y^(-α)*r^(-α)/(y^(-α)*y^p)*r^α=(r^(-α)*r^α)/(y^p) by
      have h : y^(-α)≠0 := (Real.rpow_pos_of_pos hy _).ne'
      field_simp,
    ←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero,one_div]

 

theorem actual_normalized_tilted_moment_bound (a : ℝ) (ha : 1/4<a)
    (m : ℕ) (hm : 1 ≤ m) (K : Set ℂ) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (c : ℝ) (hc : 0<c) (hc2 : c≤2)
    (hcK : ∀z∈K,c≤2*z.im) (B : ℝ) (hB : 0≤B) :
    ∃D : ℝ≥0∞,D<∞ ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W →
      ∀(θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (f : C_c(UpperPlane,ℝ)),
      (Subtype.val '' tsupport f ⊆ affine (Real.cos θ:ℂ) (Real.sin θ)
        (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) '' K) →
      (∀z : UpperPlane,‖f z‖≤B*(Real.sin θ)^(alpha a-2)) →
      ∀(s : ℕ→Finset ℕ) (coeff : ℕ→ℕ→ℝ),
      (∀k j,j∈s k→0≤coeff k j) → (∀k,∑j∈s k,coeff k j=1) →
      ∀(t : ℝ≥0∞) (μ : ExactSLEGenerator.Driver→Measure UpperPlane),
      Measurable (fun b=> ∫z,f z∂μ b) →
      (∀ᵐ b∂W,Tendsto (fun k=>∑j∈s k,coeff k j*
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) t b)
          atTop (𝓝 (∫z,f z∂μ b))) →
      ∀l : ℕ,(∫⁻b,‖∫z,f z∂μ b‖ₑ^m∂radialLaw W a (fromDisk θ 0)
          (Real.sin θ*Real.exp (-2*a*l)))≤D*ENNReal.ofReal ((Real.sin θ)^(-p a)) := by
  obtain ⟨D,hD,hbound⟩ := actual_normalized_hit_moment_bound a ha m hm K hK hKb c hc hc2 hcK B hB
  refine ⟨D,hD,?_⟩
  intro W hprob hW θ hθ hθπ f hsupport hf s coeff hcoeff hsum t μ hμ hlim l
  have hy := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hz : 0<(fromDisk θ 0).im := by rw [fromDisk_zero_im]; exact hy
  let r : ℝ := Real.exp (-2*a*l)
  have hr : 0<r := Real.exp_pos _
  have hr1 : r≤1 := Real.exp_le_one_iff.mpr (by
    have h : 0≤2*a*(l:ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg l)
    nlinarith)
  have hhit := hbound W hW (Real.cos θ) (Real.sin θ) hy f hsupport hf s coeff
    hcoeff hsum t μ hlim r hr hr1
  rw [←center_affine θ hθ hθπ] at hhit
  have ht := radialLaw_lintegral_le_hit W a ha (fromDisk θ 0) hz r hr hr1
    (fun b=>‖∫z,f z∂μ b‖ₑ^m) (hμ.enorm.pow_const m)
  rw [fromDisk_zero_im,radial_initial_green a θ hθ hθπ] at ht
  refine ht.trans ((mul_le_mul' le_rfl hhit).trans_eq ?_)
  rw [←mul_left_comm D,tilt_cancel (alpha a) (p a) hy hr]

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGreen KernelSimilarity

 
def upperAffine (x y : ℝ) (hy : 0<y) : UpperPlane ≃ₜ UpperPlane where
  toFun z := ⟨(x:ℂ)+(y:ℂ)*z.1,by simpa [Complex.mul_im] using mul_pos hy z.2⟩
  invFun z := ⟨((y:ℂ)⁻¹)*(z.1-(x:ℂ)),by
    simpa [←Complex.ofReal_inv,Complex.mul_im] using mul_pos (inv_pos.mpr hy) z.2⟩
  left_inv z := by
    apply Subtype.ext
    simp only [add_sub_cancel_left,←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hy.ne'),one_mul]
  right_inv z := by
    apply Subtype.ext
    simp only [←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hy.ne'),one_mul,add_sub_cancel]
  continuous_toFun := (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
  continuous_invFun := (continuous_const.mul (continuous_subtype_val.sub continuous_const)).subtype_mk _

@[simp] lemma upperAffine_apply (x y : ℝ) (hy : 0<y) (z : UpperPlane) :
    (upperAffine x y hy z).1=affine (x:ℂ) y hy z.1 := rfl

 
def normalizedTest (a x y : ℝ) (hy : 0<y) (f : C_c(UpperPlane,ℝ)) : C_c(UpperPlane,ℝ) where
  toFun z := y^(alpha a-2)*f ((upperAffine x y hy).symm z)
  continuous_toFun := continuous_const.mul (f.continuous.comp (upperAffine x y hy).symm.continuous)
  hasCompactSupport' := (f.hasCompactSupport.comp_homeomorph (upperAffine x y hy).symm).mul_left

lemma normalizedTest_support (a x y : ℝ) (hy : 0<y) (f : C_c(UpperPlane,ℝ)) :
    Subtype.val '' tsupport (normalizedTest a x y hy f) ⊆
      affine (x:ℂ) y hy '' (Subtype.val '' tsupport f) := by
  rintro z ⟨w,hw,rfl⟩
  have hsup : tsupport (normalizedTest a x y hy f) ⊆
      tsupport (f ∘ (upperAffine x y hy).symm) := tsupport_mul_subset_right
  have hh := tsupport_comp_subset_preimage f (upperAffine x y hy).symm.continuous (hsup hw)
  refine ⟨((upperAffine x y hy).symm w).1,⟨_,hh,rfl⟩,?_⟩
  exact congrArg Subtype.val ((upperAffine x y hy).apply_symm_apply w)

lemma normalizedTest_nonneg (a x y : ℝ) (hy : 0<y) (f : C_c(UpperPlane,ℝ))
    (hf : ∀z,0≤f z) (z : UpperPlane) : 0≤normalizedTest a x y hy f z :=
  mul_nonneg (Real.rpow_nonneg hy.le _) (hf _)

lemma normalizedTest_bound (a x y : ℝ) (hy : 0<y) (f : C_c(UpperPlane,ℝ))
    {B : ℝ} (hf : ∀z,‖f z‖≤B) (z : UpperPlane) :
    ‖normalizedTest a x y hy f z‖≤B*y^(alpha a-2) := by
  change ‖y^(alpha a-2)*f _‖≤_
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hy.le _),mul_comm]
  exact mul_le_mul_of_nonneg_right (hf _) (Real.rpow_nonneg hy.le _)

lemma disk_negative_endpoint (θ : ℝ) :
    Complex.exp (-Complex.I*θ)=(Real.cos θ:ℂ)-(Real.sin θ:ℂ)*Complex.I := by
  rw [show -Complex.I*(θ:ℂ)=((-θ:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg]
  push_cast
  ring

lemma disk_denominator_ne (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (z : UpperPlane) :
    z.1-Complex.exp (-Complex.I*θ)≠0 := by
  intro he
  have hi := congrArg Complex.im he
  rw [disk_negative_endpoint] at hi
  have hs:=Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_sub,sub_neg_eq_add,Complex.zero_im] at hi
  linarith [z.2]

lemma diskMap_affine (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (z : ℂ) :
    diskMap θ (affine (Real.cos θ:ℂ) (Real.sin θ)
      (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) z)=(z-Complex.I)/(z+Complex.I) := by
  have hy : (Real.sin θ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne'
  rw [diskMap,affine_apply,mul_comm Complex.I,Complex.exp_ofReal_mul_I,disk_negative_endpoint]
  rw [show (Real.cos θ:ℂ)+(Real.sin θ:ℂ)*z-((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I)=
      (Real.sin θ:ℂ)*(z-Complex.I) by ring,
    show (Real.cos θ:ℂ)+(Real.sin θ:ℂ)*z-((Real.cos θ:ℂ)-(Real.sin θ:ℂ)*Complex.I)=
      (Real.sin θ:ℂ)*(z+Complex.I) by ring,mul_div_mul_left _ _ hy]

lemma disk_deriv (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (z : UpperPlane) :
    deriv (diskMap θ) z.1=((2*Real.sin θ:ℝ):ℂ)*Complex.I/
      (z.1-Complex.exp (-Complex.I*θ))^2 := by
  have hd := (((hasDerivAt_id z.1).sub_const (Complex.exp (Complex.I*θ))).div
    ((hasDerivAt_id z.1).sub_const (Complex.exp (-Complex.I*θ)))
      (disk_denominator_ne θ hθ hθπ z)).deriv
  change deriv (diskMap θ) z.1=_ at hd
  rw [hd]
  simp only [id_eq,one_mul,mul_one]
  rw [show z.1-Complex.exp (-Complex.I*θ)-(z.1-Complex.exp (Complex.I*θ))=
    Complex.exp (Complex.I*θ)-Complex.exp (-Complex.I*θ) by ring,
    disk_endpoints_difference]

lemma disk_deriv_bound (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (z : UpperPlane) :
    ‖deriv (diskMap θ) z.1‖≤2/(Real.sin θ) := by
  have hy := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hn : Real.sin θ≤‖z.1-Complex.exp (-Complex.I*θ)‖ := by
    apply le_trans _ (Complex.im_le_norm _)
    rw [disk_negative_endpoint]
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_sub,sub_neg_eq_add]
    linarith [z.2]
  have hn0 : 0<‖z.1-Complex.exp (-Complex.I*θ)‖ := hy.trans_le hn
  rw [disk_deriv θ hθ hθπ z,norm_div,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (by positivity : 0<2*Real.sin θ),Complex.norm_I,mul_one]
  apply (div_le_div_iff₀ (sq_pos_of_pos hn0) hy).mpr
  nlinarith

lemma cayley_inner (z : UpperPlane) (hz : ‖(z.1-Complex.I)/(z.1+Complex.I)‖≤1/4) :
    dist z.1 Complex.I≤2/3 := by
  have hn0 : 0<‖z.1+Complex.I‖ := by
    apply lt_of_lt_of_le _ (Complex.im_le_norm _)
    simpa only [Complex.add_im,Complex.I_im] using add_pos z.2 (by norm_num : (0:ℝ)<1)
  rw [norm_div] at hz
  have h := (div_le_iff₀ hn0).mp hz
  have hn : ‖z.1+Complex.I‖≤‖z.1-Complex.I‖+2 := by
    calc
      _ = ‖(z.1-Complex.I)+(Complex.I+Complex.I)‖ := by congr 1; ring
      _ ≤ ‖z.1-Complex.I‖+‖Complex.I+Complex.I‖ := norm_add_le _ _
      _ ≤ ‖z.1-Complex.I‖+2 := by
        have := norm_add_le Complex.I Complex.I
        simp only [Complex.norm_I] at this
        linarith
  rw [dist_eq_norm]
  nlinarith

 

lemma disk_preimage_inner (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (z : UpperPlane)
    (hz : diskMap θ z.1∈Metric.closedBall (0:ℂ) (1/4)) :
    dist ((upperAffine (Real.cos θ) (Real.sin θ)
      (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)).symm z).1 Complex.I≤2/3 := by
  apply cayley_inner
  have he := diskMap_affine θ hθ hθπ
    (((upperAffine (Real.cos θ) (Real.sin θ) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)).symm z).1)
  rw [←upperAffine_apply,Homeomorph.apply_symm_apply] at he
  simpa only [Metric.mem_closedBall,dist_zero_right,he] using hz

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen KernelSimilarity

lemma height_of_ball {z : ℂ} {r : ℝ} (hz : dist z Complex.I≤r) : 1-r≤z.im := by
  have h : 1-z.im≤dist z Complex.I := by
    simpa only [Complex.sub_im,Complex.I_im,dist_eq_norm,norm_sub_rev] using
      Complex.im_le_norm (Complex.I-z)
  linarith

lemma upper_inner_compact : IsCompact {z : UpperPlane | dist z.1 Complex.I≤2/3} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : (Subtype.val : UpperPlane→ℂ) '' {z | dist z.1 Complex.I≤2/3}=
      Metric.closedBall Complex.I (2/3) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩; exact hw
    · intro hz
      have hi := height_of_ball hz
      exact ⟨⟨z,by linarith⟩,hz,rfl⟩
  rw [he]
  exact isCompact_closedBall _ _

lemma cutoff_exists : ∃f : C_c(UpperPlane,ℝ),
    (∀z,0≤f z ∧ f z≤1) ∧
    (∀z : UpperPlane, dist z.1 Complex.I≤2/3 → f z=1) ∧
    (∀z∈tsupport f,dist z.1 Complex.I<3/4) := by
  obtain ⟨f,hf,hfc,hfs,h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    upper_inner_compact (Metric.isOpen_ball.preimage (continuous_subtype_val (p:=fun z : ℂ=>0<z.im)))
    (show {z : UpperPlane | dist z.1 Complex.I≤2/3} ⊆
        (Subtype.val : UpperPlane→ℂ) ⁻¹' Metric.ball Complex.I (3/4) from fun z hz=>by
      change dist z.1 Complex.I<3/4
      exact lt_of_le_of_lt hz (by norm_num))
  exact ⟨⟨f,hfc⟩,h01,fun z hz=>hf hz,fun z hz=>hfs hz⟩

def diskCutoff : C_c(UpperPlane,ℝ) := Classical.choose cutoff_exists

lemma diskCutoff_nonneg (z : UpperPlane) : 0≤diskCutoff z :=
  (Classical.choose_spec cutoff_exists).1 z |>.1
lemma diskCutoff_le_one (z : UpperPlane) : diskCutoff z≤1 :=
  (Classical.choose_spec cutoff_exists).1 z |>.2
lemma diskCutoff_one (z : UpperPlane) (hz : dist z.1 Complex.I≤2/3) : diskCutoff z=1 :=
  (Classical.choose_spec cutoff_exists).2.1 z hz
lemma diskCutoff_support (z : UpperPlane) (hz : z∈tsupport diskCutoff) :
    dist z.1 Complex.I<3/4 := (Classical.choose_spec cutoff_exists).2.2 z hz

 

def diskWeight (a θ : ℝ) (z : UpperPlane) : ℝ := ‖deriv (diskMap θ) z.1‖^(2-alpha a)

def diskMass (a θ : ℝ) (ν : Measure UpperPlane) : Measure ℂ :=
  (ν.withDensity (fun z=>ENNReal.ofReal (diskWeight a θ z))).map (fun z=>diskMap θ z.1)

lemma diskMap_measurable (θ : ℝ) : Measurable (fun z : UpperPlane=>diskMap θ z.1) := by
  unfold diskMap
  fun_prop

lemma diskWeight_measurable (a θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) :
    Measurable (diskWeight a θ) := by
  have he : diskWeight a θ=fun z : UpperPlane=>
      ‖((2*Real.sin θ:ℝ):ℂ)*Complex.I/(z.1-Complex.exp (-Complex.I*θ))^2‖^(2-alpha a) := by
    funext z; rw [diskWeight,disk_deriv θ hθ hθπ z]
  rw [he]
  fun_prop

lemma dimension_pos (a : ℝ) (ha : 1/4<a) : 0<2-alpha a := by
  have ha0 : 0<a := by linarith
  have hp : 0<1/(4*a) := by positivity
  dsimp [alpha]
  linarith

 
def diskTest (a θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) : C_c(UpperPlane,ℝ) :=
  (2^(2-alpha a):ℝ) • normalizedTest a (Real.cos θ) (Real.sin θ)
    (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) diskCutoff

lemma diskTest_nonneg (a θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (z : UpperPlane) :
    0≤diskTest a θ hθ hθπ z :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (normalizedTest_nonneg a _ _ _ diskCutoff diskCutoff_nonneg z)

lemma diskTest_bound (a θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) (z : UpperPlane) :
    ‖diskTest a θ hθ hθπ z‖≤2^(2-alpha a)*(Real.sin θ)^(alpha a-2) := by
  change ‖(2^(2-alpha a):ℝ)*normalizedTest a _ _ _ diskCutoff z‖≤_
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  simpa only [one_mul] using normalizedTest_bound a _ _ _ diskCutoff (B:=1)
    (fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (diskCutoff_nonneg z)]; exact diskCutoff_le_one z) z

lemma diskTest_support (a θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) :
    Subtype.val '' tsupport (diskTest a θ hθ hθπ) ⊆
      affine (Real.cos θ:ℂ) (Real.sin θ) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) ''
        (Subtype.val '' tsupport diskCutoff) := by
  apply (image_mono (tsupport_smul_subset_right (fun _ : UpperPlane => (2^(2-alpha a):ℝ))
    (normalizedTest a (Real.cos θ) (Real.sin θ) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) diskCutoff))).trans
  exact normalizedTest_support a _ _ _ diskCutoff

lemma diskWeight_le_diskTest (a θ : ℝ) (ha : 1/4<a) (hθ : 0<θ) (hθπ : θ<Real.pi)
    (z : UpperPlane) (hz : diskMap θ z.1∈Metric.closedBall (0:ℂ) (1/4)) :
    diskWeight a θ z≤diskTest a θ hθ hθπ z := by
  have hy := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have he := diskCutoff_one _ (disk_preimage_inner θ hθ hθπ z hz)
  change ‖deriv (diskMap θ) z.1‖^(2-alpha a)≤
    2^(2-alpha a)*((Real.sin θ)^(alpha a-2)*diskCutoff _)
  rw [he,mul_one]
  calc
    _ ≤ (2/(Real.sin θ))^(2-alpha a) := Real.rpow_le_rpow (norm_nonneg _)
      (disk_deriv_bound θ hθ hθπ z) (dimension_pos a ha).le
    _ = _ := by
      rw [div_eq_mul_inv,Real.mul_rpow (by norm_num : (0:ℝ)≤2) (inv_nonneg.mpr hy.le),
        Real.inv_rpow hy.le,←Real.rpow_neg hy.le,neg_sub]

lemma diskMass_inner_le_test (a θ : ℝ) (ha : 1/4<a) (hθ : 0<θ) (hθπ : θ<Real.pi)
    (ν : Measure UpperPlane) [IsFiniteMeasureOnCompacts ν] :
    diskMass a θ ν (Metric.closedBall (0:ℂ) (1/4))≤
      ENNReal.ofReal (∫z,diskTest a θ hθ hθπ z∂ν) := by
  rw [diskMass,Measure.map_apply (diskMap_measurable θ) Metric.isClosed_closedBall.measurableSet,
    withDensity_apply _ ((diskMap_measurable θ) Metric.isClosed_closedBall.measurableSet),
    ofReal_integral_eq_lintegral_ofReal (diskTest a θ hθ hθπ).integrable
      (Eventually.of_forall (diskTest_nonneg a θ hθ hθπ)),
    ←lintegral_indicator ((diskMap_measurable θ) Metric.isClosed_closedBall.measurableSet)]
  apply lintegral_mono
  intro z
  by_cases hz : diskMap θ z.1∈Metric.closedBall (0:ℂ) (1/4)
  · simp only [Set.indicator, Set.mem_preimage, hz, ite_true]
    exact ENNReal.ofReal_le_ofReal (diskWeight_le_diskTest a θ ha hθ hθπ z hz)
  · simp only [Set.indicator, Set.mem_preimage, hz, ite_false]; positivity

end SLEExactGauge.CenteredMoments
end
end

end OAI
