import Mathlib
import OAI.Geometry.CubicTorus.Reflection.AxialSectionCorner

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_closedCentralArc {K : ℝ} (hK : K∈Ico 0 (1/2)) (f : AxisCircle →ℝ) :
    (∫ z in closedCentralArc K,f z)=∫ t in (-K)..K,f (t : AxisCircle) := by
  have hsub : Icc (-K) K ⊆ Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2,hK.2]
  have he (t : ℝ) (ht : t∈Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1)) :
      (t : AxisCircle)∈closedCentralArc K ↔t∈Icc (-K) K := by
    constructor
    · rintro ⟨s,hs,hst⟩
      have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub hs) ht).mp hst
      rwa [←hh]
    · intro ht
      exact ⟨t,ht,rfl⟩
  calc
    _=∫ z : AxisCircle,(closedCentralArc K).indicator f z :=
      (integral_indicator (closedCentralArc_isCompact K).measurableSet).symm
    _=∫ t in Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1),(closedCentralArc K).indicator f (t : AxisCircle) :=
      (AddCircle.integral_preimage (1 : ℝ) (-(1/2 : ℝ)) _).symm
    _=∫ t in Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1),(Icc (-K) K).indicator
        (fun t : ℝ ↦ f (t : AxisCircle)) t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      by_cases htk : t∈Icc (-K) K
      · simp only [indicator_of_mem htk,indicator_of_mem ((he t ht).mpr htk)]
      · simp only [indicator_of_notMem htk,indicator_of_notMem (mt (he t ht).mp htk)]
    _=∫ t in Icc (-K) K,f (t : AxisCircle) := by
      rw [setIntegral_indicator measurableSet_Icc,inter_eq_right.mpr hsub]
    _=∫ t in (-K)..K,f (t : AxisCircle) := by
      rw [intervalIntegral.integral_of_le (by linarith [hK.1]),integral_Icc_eq_integral_Ioc]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_scaled_semicircle {L : ℝ} (hL : 0<L) :
    (∫ t in (-L)..L,Real.sqrt (1-(t/L)^2))=Real.pi*L/2 := by
  have hi := intervalIntegral.integral_comp_div (fun t : ℝ ↦ Real.sqrt (1-t^2))
    (a := -L) (b := L) hL.ne'
  rw [neg_div,div_self hL.ne',integral_sqrt_one_sub_sq] at hi
  calc
    _=L*(Real.pi/2) := hi
    _=Real.pi*L/2 := by ring

theorem planarTorusPerimeter_ge_semicircle_calibration
    {A : Set TransverseProduct} (hA : IsOpen A) {L : ℝ} (hL : L∈Ioo 0 (1/2))
    (hband : ∀ y∈A,∃ t : ℝ,|t|<L ∧(t : AxisCircle)=y 1)
    (hin : ∀ t : ℝ,|t|<L →∀ y : TransverseProduct,y 0=0 →y 1=(t : AxisCircle) →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A) :
    ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  let f : ℝ →ℝ := fun t ↦ Real.sqrt (1-(t/L)^2)
  have hf : Continuous f := (continuous_const.sub ((continuous_id.div_const L).pow 2)).sqrt
  have hb (q : ℝ) (hq : q∈Ioo 0 1) :
      ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))≤planarTorusPerimeter A := by
    obtain ⟨u,v,hu,hv,pu,pv,hu0,huv,huBand,hvBand⟩ := exists_planar_affine_band_field hL hq
    have hqL : 0<q*L := mul_pos hq.1 hL.1
    have hqLL : q*L<L := by nlinarith [hq.2,hL.1]
    have hKhalf : q*L<1/2 := hqLL.trans hL.2
    have hbound := planarTorusPerimeter_ge_corner_calibration hA (closedCentralArc_isCompact (q*L))
      hu hv pu pv hu0 (fun t ↦ (huv t).le) (a := 0) (c := 1/2) (by norm_num) (by norm_num)
      (fun y hy0 hyT ↦ ?_) hout (k := q/L) (fun y hy ↦ ?_)
    · have hInt : (∫ t in (-(q*L))..(q*L),f t)≤∫ z in closedCentralArc (q*L),pu.lift z := by
        rw [integral_closedCentralArc ⟨hqL.le,hKhalf⟩]
        change (∫ t in (-(q*L))..(q*L),f t)≤∫ t in (-(q*L))..(q*L),u t
        apply intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _) (hu.continuous.intervalIntegrable _ _)
        intro t ht
        have htL : |t|≤L := (abs_le.mpr ht).trans hqLL.le
        rw [huBand t htL]
        apply Real.sqrt_le_sqrt
        have hq2 : q^2≤1 := by nlinarith [hq.1,hq.2]
        have hmul := mul_nonneg (sq_nonneg (t/L)) (sub_nonneg.mpr hq2)
        have he : (q/L*t)^2=q^2*(t/L)^2 := by ring
        rw [he]
        nlinarith
      exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hbound
    · obtain ⟨t,ht,he⟩ := hyT
      have htt : |t|<L := (abs_le.mpr ht).trans_lt hqLL
      exact hin t htt y (by simpa using hy0) he.symm
    · obtain ⟨t,ht,he⟩ := hband y hy
      rw [←he]
      exact hvBand t ht
  have hp : Continuous (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z,f t) :=
    intervalIntegral.continuous_primitive (fun _ _ ↦ hf.intervalIntegrable _ _) 0
  have hI : Continuous (fun q : ℝ ↦ ∫ t in (-(q*L))..(q*L),f t) := by
    have he (q : ℝ) : (∫ t in (-(q*L))..(q*L),f t)=
        (∫ t in (0 : ℝ)..(q*L),f t)-(∫ t in (0 : ℝ)..(-(q*L)),f t) :=
      (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
    simp_rw [he]
    exact (hp.comp (continuous_id.mul_const L)).sub (hp.comp (continuous_id.mul_const L).neg)
  have hc : Continuous (fun q : ℝ ↦ ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))) :=
    ENNReal.continuous_ofReal.comp (((continuous_id.div_const L).mul_const _).add (continuous_const.mul hI))
  have hs : IsClosed {q : ℝ | ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))≤planarTorusPerimeter A} :=
    isClosed_le hc continuous_const
  have h1 : (1 : ℝ)∈closure (Ioo (0 : ℝ) 1) := by rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]; exact ⟨by norm_num,le_rfl⟩
  have hh := closure_minimal (fun q hq ↦ hb q hq) hs h1
  change ENNReal.ofReal (1/L*volume.real A+2*(∫ t in (-(1*L))..(1*L),f t))≤planarTorusPerimeter A at hh
  simp only [one_mul] at hh
  change ENNReal.ofReal (1/L*volume.real A+2*(∫ t in (-L)..L,Real.sqrt (1-(t/L)^2)))≤_ at hh
  rw [integral_scaled_semicircle hL.1] at hh
  convert hh using 1
  congr 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def PlanarRadialDownset (A : Set TransverseProduct) : Prop :=
  ∀ y z : TransverseProduct,(∀ j,‖y j‖≤‖z j‖) →z∈A →y∈A

def planarAxisPoint (t : ℝ) : TransverseProduct := ![0,(t : AxisCircle)]

lemma planarAxisPoint_continuous : Continuous planarAxisPoint := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_const
  · exact AddCircle.continuous_mk' (1 : ℝ)

lemma planar_axis_can_grow {A : Set TransverseProduct} (hA : IsOpen A)
    {t : ℝ} (ht : t<1/2) (hm : planarAxisPoint t∈A) :
    ∃ s : ℝ,t<s ∧ s<1/2 ∧ planarAxisPoint s∈A := by
  have ho : IsOpen (planarAxisPoint ⁻¹' A ∩ Iio (1/2 : ℝ)) :=
    (hA.preimage planarAxisPoint_continuous).inter isOpen_Iio
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho t ⟨hm,ht⟩
  have he : t+ε/2∈Metric.ball t ε := by
    rw [Metric.mem_ball,Real.dist_eq]
    have hp : 0<ε/2 := half_pos hε
    rw [show t+ε/2-t=ε/2 by ring,abs_of_pos hp]
    linarith
  exact ⟨t+ε/2,by linarith,(hball he).2,(hball he).1⟩

lemma axisCircle_norm_le_half (z : AxisCircle) : ‖z‖≤1/2 := by
  simpa using AddCircle.norm_le_half_period 1 (x := z) (by norm_num)

lemma axisCircle_norm_coe_small {t : ℝ} (ht : |t|≤1/2) : ‖(t : AxisCircle)‖=|t| := by
  apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
  simpa using ht

theorem planar_radial_extent {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout : planarAxisPoint (1/2)∉closure A) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y 1‖<L) ∧
      (∀ t : ℝ,|t|<L →∀ y : TransverseProduct,y 0=0 →y 1=(t : AxisCircle) →y∈A) := by
  let T : Set ℝ := {t | t∈Icc 0 (1/2) ∧ planarAxisPoint t∈A}
  have he0 : planarAxisPoint 0=(0 : TransverseProduct) := by ext j; fin_cases j <;> simp [planarAxisPoint]
  have hzero : planarAxisPoint 0∈A := he0 ▸ h0
  have hne : T.Nonempty := ⟨0,⟨by constructor <;> norm_num,hzero⟩⟩
  have hb : BddAbove T := ⟨1/2,fun t ht ↦ ht.1.2⟩
  let L : ℝ := sSup T
  have hLhalf : L≤1/2 := csSup_le hne (fun t ht ↦ ht.1.2)
  have hcl : planarAxisPoint L∈closure A := by
    exact closure_minimal (s := T) (t := planarAxisPoint ⁻¹' closure A)
      (fun t ht ↦ subset_closure ht.2)
      (isClosed_closure.preimage planarAxisPoint_continuous) (csSup_mem_closure hne hb)
  have hLlt : L<1/2 := lt_of_le_of_ne hLhalf (fun he ↦ hout (he ▸ hcl))
  obtain ⟨s,hs,hsH,hsA⟩ := planar_axis_can_grow hA (by norm_num : (0 : ℝ)<1/2) hzero
  have hsL : s≤L := le_csSup hb ⟨⟨hs.le,hsH.le⟩,hsA⟩
  refine ⟨L,⟨hs.trans_le hsL,hLlt⟩,?_,?_⟩
  · intro y hy
    have hp : planarAxisPoint ‖y 1‖∈A := by
      apply hd _ y _ hy
      intro j
      fin_cases j
      · simp [planarAxisPoint]
      · change ‖((‖y 1‖ : ℝ) : AxisCircle)‖≤‖y 1‖
        rw [axisCircle_norm_coe_small (by simpa only [abs_norm] using axisCircle_norm_le_half (y 1)),abs_norm]
    have hrL : ‖y 1‖≤L := le_csSup hb ⟨⟨norm_nonneg _,axisCircle_norm_le_half _⟩,hp⟩
    obtain ⟨s,hs,hsH,hsA⟩ := planar_axis_can_grow hA (hrL.trans_lt hLlt) hp
    exact hs.trans_le (le_csSup hb ⟨⟨(norm_nonneg _).trans hs.le,hsH.le⟩,hsA⟩)
  · intro t ht y hy0 hy1
    obtain ⟨s,hs,hst⟩ := exists_lt_of_lt_csSup hne ht
    apply hd y (planarAxisPoint s) _ hs.2
    intro j
    fin_cases j
    · simp [planarAxisPoint,hy0]
    · change ‖y 1‖≤‖(s : AxisCircle)‖
      rw [hy1,axisCircle_norm_coe_small (ht.le.trans hLhalf),
        axisCircle_norm_coe_small (by simpa [abs_of_nonneg hs.1.1] using hs.1.2),abs_of_nonneg hs.1.1]
      exact hst.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircle_exists_centered_rep (z : AxisCircle) :
    ∃ t : ℝ,(t : AxisCircle)=z ∧ |t|=‖z‖ := by
  let t := (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) z : ℝ)
  have ht := (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) z).property
  have hbound : |t|≤1/2 := abs_le.mpr ⟨ht.1,by dsimp [t]; linarith [ht.2]⟩
  have he : (t : AxisCircle)=z := AddCircle.coe_equivIco
  exact ⟨t,he,by rw [←he,axisCircle_norm_coe_small hbound]⟩

def planarFirstAxisPoint (t : ℝ) : TransverseProduct := ![(t : AxisCircle),0]

lemma planar_radial_empty_fiber {A : Set TransverseProduct} (hd : PlanarRadialDownset A)
    (hout : planarFirstAxisPoint (1/2)∉closure A) :
    ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A := by
  let f : TransverseProduct →TransverseProduct := fun y ↦ ![y 0,0]
  have hc : Continuous f := by
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 0
    · exact continuous_const
  have hm : A⊆f ⁻¹' closure A := by
    intro y hy
    apply subset_closure
    apply hd (f y) y _ hy
    intro j
    fin_cases j <;> simp [f]
  have hcl := closure_minimal hm (isClosed_closure.preimage hc)
  intro y hy hya
  apply hout
  have he : f y=planarFirstAxisPoint (1/2) := by
    ext j
    fin_cases j <;> simp [f,planarFirstAxisPoint,hy]
  exact he ▸ hcl hya

theorem planar_radial_calibration {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y 1‖<L) ∧
      ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  obtain ⟨L,hL,hband,hin⟩ := planar_radial_extent hA hd h0 hout1
  refine ⟨L,hL,hband,planarTorusPerimeter_ge_semicircle_calibration hA hL ?_ hin
    (planar_radial_empty_fiber hd hout0)⟩
  intro y hy
  obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep (y 1)
  exact ⟨t,ht ▸ hband y hy,he⟩

theorem planar_radial_isoperimetric {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) :
    ENNReal.ofReal (2*Real.sqrt (Real.pi*volume.real A))≤planarTorusPerimeter A := by
  obtain ⟨L,hL,hband,hp⟩ := planar_radial_calibration hA hd h0 hout0 hout1
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hp
  have ha : 0≤volume.real A := measureReal_nonneg
  have hs : (Real.sqrt (Real.pi*volume.real A))^2=Real.pi*volume.real A :=
    Real.sq_sqrt (mul_nonneg Real.pi_pos.le ha)
  have hq := sq_nonneg (Real.sqrt (volume.real A/L)-Real.sqrt (Real.pi*L))
  have hu : (Real.sqrt (volume.real A/L))^2=volume.real A/L := Real.sq_sqrt (div_nonneg ha hL.1.le)
  have hv : (Real.sqrt (Real.pi*L))^2=Real.pi*L := Real.sq_sqrt (mul_nonneg Real.pi_pos.le hL.1.le)
  have he : Real.sqrt (volume.real A/L)*Real.sqrt (Real.pi*L)=Real.sqrt (Real.pi*volume.real A) := by
    rw [←Real.sqrt_mul (div_nonneg ha hL.1.le)]
    congr 1
    field_simp [hL.1.ne']
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarQuotient (x : Plane) : TransverseProduct := fun j ↦ (x j : AxisCircle)

@[simp] lemma planarQuotient_representative (y : TransverseProduct) :
    planarQuotient (planarRepresentative y)=y := by
  ext j
  exact AddCircle.coe_equivIco

@[simp] lemma planarQuotient_add (x y : Plane) : planarQuotient (x+y)=planarQuotient x+planarQuotient y := by
  ext j
  change ((x j+y j : ℝ) : AxisCircle)=(x j : AxisCircle)+(y j : AxisCircle)
  simp only [AddCircle.coe_add]
@[simp] lemma planarQuotient_neg (x : Plane) : planarQuotient (-x)=-planarQuotient x := by
  ext j
  change ((-x j : ℝ) : AxisCircle)=-(x j : AxisCircle)
  simp only [AddCircle.coe_neg]

lemma planar_same_quotient_lattice {x y : Plane} (h : planarQuotient x=planarQuotient y) :
    ∃ n : Fin 2 →ℤ,x=y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)) := by
  have hh : ∀ j : Fin 2,∃ n : ℤ,(n : ℝ)=x j-y j := by
    intro j
    have hi : ((x j-y j : ℝ) : AxisCircle)=0 := by
      have he := congrFun h j
      simpa only [planarQuotient,AddCircle.coe_sub] using sub_eq_zero.mpr he
    simpa only [zsmul_eq_mul,mul_one] using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi)
  choose n hn using hh
  refine ⟨n,?_⟩
  ext j
  change x j=y j+(n j : ℝ)
  linarith [hn j]

lemma planeDivergence_translate (F : Plane →Plane) (a y : Plane) :
    planeDivergence (fun z ↦ F (z+a)) y=planeDivergence F (y+a) := by
  simp only [planeDivergence,fderiv_comp_add_right]

lemma planeDivergence_periodic {F : Plane →Plane}
    (hF : ∀ (n : Fin 2 →ℤ) y,F (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=F y)
    (n : Fin 2 →ℤ) (y : Plane) :
    planeDivergence F (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=planeDivergence F y := by
  have he : (fun y : Plane ↦ F (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ))))=F := funext (hF n)
  rw [←planeDivergence_translate,he]

lemma planarAdmissibleField_translate {F : Plane →Plane} (hF : PlanarAdmissibleField F) (a : Plane) :
    PlanarAdmissibleField (fun y ↦ F (y+a)) := by
  refine ⟨hF.1.comp (contDiff_id.add contDiff_const),?_,fun y ↦ hF.2.2 _⟩
  intro n y
  change F ((y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))+a)=F (y+a)
  rw [add_right_comm,hF.2.1]

lemma planar_flux_translation {F : Plane →Plane} (hF : PlanarAdmissibleField F)
    (a : Plane) (A : Set TransverseProduct) :
    (∫ y in (fun z : TransverseProduct ↦ z+planarQuotient a) ⁻¹' A,
      planeDivergence F (planarRepresentative y))=
    ∫ y in A,planeDivergence (fun z ↦ F (z-a)) (planarRepresentative y) := by
  have he : (fun y : TransverseProduct ↦ planeDivergence F (planarRepresentative y))=
      (fun y ↦ planeDivergence (fun z ↦ F (z-a)) (planarRepresentative (y+planarQuotient a))) := by
    funext y
    simp only [sub_eq_add_neg,planeDivergence_translate]
    have hq : planarQuotient (planarRepresentative (y+planarQuotient a)+-a)=
        planarQuotient (planarRepresentative y) := by simp
    obtain ⟨n,hn⟩ := planar_same_quotient_lattice hq
    rw [hn,planeDivergence_periodic hF.2.1]
  rw [he]
  exact (measurePreserving_add_right (volume : Measure TransverseProduct) (planarQuotient a)).setIntegral_preimage_emb
    (Homeomorph.addRight (planarQuotient a)).measurableEmbedding
    (fun y ↦ planeDivergence (fun z ↦ F (z-a)) (planarRepresentative y)) A

lemma planarTorusPerimeter_translation_le (A : Set TransverseProduct) (a : Plane) :
    planarTorusPerimeter ((fun y : TransverseProduct ↦ y+planarQuotient a) ⁻¹' A)≤planarTorusPerimeter A := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [planar_flux_translation hF a A]
  have hG : PlanarAdmissibleField (fun y ↦ F (y-a)) := by
    simpa only [sub_eq_add_neg] using planarAdmissibleField_translate hF (-a)
  exact le_iSup_of_le (fun y ↦ F (y-a)) (le_iSup_of_le hG le_rfl)

theorem planarTorusPerimeter_translation (A : Set TransverseProduct) (a : TransverseProduct) :
    planarTorusPerimeter ((fun y : TransverseProduct ↦ y+a) ⁻¹' A)=planarTorusPerimeter A := by
  have ha := planarQuotient_representative a
  refine le_antisymm (by simpa only [ha] using planarTorusPerimeter_translation_le A (planarRepresentative a)) ?_
  have hh := planarTorusPerimeter_translation_le ((fun y : TransverseProduct ↦ y+a) ⁻¹' A) (-planarRepresentative a)
  have he : (fun y : TransverseProduct ↦ y+planarQuotient (-planarRepresentative a)) ⁻¹'
      ((fun y : TransverseProduct ↦ y+a) ⁻¹' A)=A := by
    ext y
    simp
  rwa [he] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircle_norm_add_half (z : AxisCircle) :
    ‖z+((1/2 : ℝ) : AxisCircle)‖=1/2-‖z‖ := by
  obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep z
  have hb : |t|≤1/2 := ht.trans_le (axisCircle_norm_le_half z)
  rw [←he,←AddCircle.coe_add,axisCircle_norm_coe_small hb]
  by_cases hpos : 0≤t
  · rw [circle_norm_upper ⟨by linarith,(by linarith [(le_abs_self t).trans hb])⟩,abs_of_nonneg hpos]
    ring
  · have ht0 := le_of_not_ge hpos
    have hp : 0≤t+1/2 := by linarith [neg_le_of_abs_le hb]
    rw [axisCircle_norm_coe_small (by rw [abs_of_nonneg hp]; linarith),abs_of_nonneg hp,abs_of_nonpos ht0]
    ring

def axialSectionCenter (b : Fin 3 →Bool) (i : Fin 3) : TransverseProduct :=
  fun j ↦ if b (i.succAbove j) then ((1/2 : ℝ) : AxisCircle) else 0

def centeredAxialSlice (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) : Set TransverseProduct :=
  (fun y ↦ y+axialSectionCenter b i) ⁻¹' axialSlice O i t

lemma upperFold_centered_slice (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle)
    (y : TransverseProduct) (j : Fin 2) :
    upperFold ((torusAxialSplit i).symm (t,y+axialSectionCenter b i)) (i.succAbove j)=
      if b (i.succAbove j) then 1/2+‖y j‖ else 1-‖y j‖ := by
  rw [upperFold_slice_succAbove]
  change 1-‖y j+(if b (i.succAbove j) then ((1/2 : ℝ) : AxisCircle) else 0)‖=_
  cases b (i.succAbove j) <;> simp only [Bool.false_eq_true,ite_false,ite_true,add_zero]
  rw [axisCircle_norm_add_half]
  ring

lemma centeredAxialSlice_isOpen {O : Set Torus} (hO : IsOpen O) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    IsOpen (centeredAxialSlice O b i t) :=
  (axialSlice_isOpen hO i t).preimage (continuous_add_const _)

lemma centeredAxialSlice_closure_subset (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    closure (centeredAxialSlice O b i t)⊆centeredAxialSlice (closure O) b i t := by
  apply closure_minimal
  · exact preimage_mono (preimage_mono subset_closure)
  · exact (isClosed_closure.preimage ((torusAxialSplit_symm_continuous i).comp
      (continuous_const.prodMk (continuous_add_const (axialSectionCenter b i)))))

theorem isMinimizerAt_centered_section_radial {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : AxisCircle) :
    PlanarRadialDownset (centeredAxialSlice (openRepresentative E) b i t) := by
  intro y z hyz hz
  let Y := (torusAxialSplit i).symm (t,y+axialSectionCenter b i)
  let Z := (torusAxialSplit i).symm (t,z+axialSectionCenter b i)
  change Y∈openRepresentative E
  have hre := reflection_invariant_openRepresentative hmin.1.1 hR
  apply (upperFold_phase hre Y).mp
  apply isMinimizerAt_closed_octant_order hV hmin hR hd (upperFold_mem Y) (upperFold_mem Z) _
    ((upperFold_phase hre Z).mpr hz)
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨j,rfl⟩
  · subst k
    change if b i then 1-‖Y i‖≤1-‖Z i‖ else 1-‖Z i‖≤1-‖Y i‖
    simp only [Y,Z,torusAxialSplit_symm_same,le_refl,ite_self]
  · dsimp only [Y,Z]
    rw [upperFold_centered_slice,upperFold_centered_slice]
    cases b (i.succAbove j) <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith [hyz j]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarSquareCorner (n : Fin 2 →Bool) : TransverseProduct :=
  fun j ↦ if n j then ((1/2 : ℝ) : AxisCircle) else 0

lemma centered_section_corner (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 →Bool) :
    (torusAxialSplit i).symm ((t : AxisCircle),planarSquareCorner n+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t n) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨j,rfl⟩
  · subst k
    simp [quotientMap]
  · simp only [torusAxialSplit_symm_succAbove,Pi.add_apply,planarSquareCorner,axialSectionCenter]
    simp only [quotientMap,axialSectionCorner,Fin.insertNth_apply_succAbove]
    change (if n j then ((1/2 : ℝ) : AxisCircle) else 0)+
      (if b (i.succAbove j) then ((1/2 : ℝ) : AxisCircle) else 0)=
        (octantHeight b (i.succAbove j) (if n j then 1 else 0) : AxisCircle)
    cases hn : n j <;> cases hb : b (i.succAbove j) <;>
      norm_num [octantHeight,hn,hb,AddCircle.coe_period]
    rw [←AddCircle.coe_add]
    norm_num [AddCircle.coe_period]

lemma centered_section_zero (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) :
    (torusAxialSplit i).symm ((t : AxisCircle),(0 : TransverseProduct)+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t (fun _ ↦ false)) := by
  have he : planarSquareCorner (fun _ ↦ false)=(0 : TransverseProduct) := by ext j; simp [planarSquareCorner]
  simpa only [he] using centered_section_corner b i t (fun _ ↦ false)

lemma centered_section_first_axis (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) :
    (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t (fun j ↦ j==0)) := by
  have he : planarFirstAxisPoint (1/2)=planarSquareCorner (fun j ↦ j==0) := by
    ext j; fin_cases j <;> simp [planarFirstAxisPoint,planarSquareCorner]
  rw [he,centered_section_corner]

lemma centered_section_second_axis (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) :
    (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t (fun j ↦ j==1)) := by
  have he : planarAxisPoint (1/2)=planarSquareCorner (fun j ↦ j==1) := by
    ext j; fin_cases j <;> simp [planarAxisPoint,planarSquareCorner]
  rw [he,centered_section_corner]

lemma centeredAxialSlice_volume (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    volume.real (centeredAxialSlice O b i t)=volume.real (axialSlice O i t) := by
  apply congrArg ENNReal.toReal
  exact (measurePreserving_add_right (volume : Measure TransverseProduct) (axialSectionCenter b i)).measure_preimage_emb
    (Homeomorph.addRight (axialSectionCenter b i)).measurableEmbedding _

lemma centeredAxialSlice_perimeter (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    planarTorusPerimeter (centeredAxialSlice O b i t)=planarTorusPerimeter (axialSlice O i t) :=
  planarTorusPerimeter_translation _ _

theorem isMinimizerAt_section_disk_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hin : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E)
    (hout0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∉closure (openRepresentative E))
    (hout1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∉closure (openRepresentative E)) :
    ENNReal.ofReal (2*Real.sqrt (Real.pi*volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
      planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hzero : (0 : TransverseProduct)∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle) := by
    change (torusAxialSplit i).symm ((t : AxisCircle),0+axialSectionCenter b i)∈openRepresentative E
    rwa [centered_section_zero]
  have hv0 : planarFirstAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_first_axis] at hz
    exact hout0 hz
  have hv1 : planarAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_second_axis] at hz
    exact hout1 hz
  have hp := planar_radial_isoperimetric (centeredAxialSlice_isOpen (isOpen_openRepresentative E) b i _)
    (isMinimizerAt_centered_section_radial hV hmin hR hd i _) hzero hv0 hv1
  simpa only [centeredAxialSlice_volume,centeredAxialSlice_perimeter] using hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_descended_divergence_continuous {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    Continuous (fun y : TransverseProduct ↦ planeDivergence F (planarRepresentative y)) := by
  have hLF := liftPlanarField_admissible (0 : Fin 3) hF
  have hc := continuous_periodic_descent (continuous_divergence hLF.1) (divergence_periodic hLF.2.1)
  have hh := hc.comp ((torusAxialSplit_symm_continuous 0).comp
    ((continuous_const : Continuous (fun _ : TransverseProduct ↦ (0 : AxisCircle))).prodMk (continuous_id : Continuous (fun y : TransverseProduct ↦ y))))
  convert hh using 1
  funext y
  dsimp only [Function.comp_apply,id_eq]
  rw [divergence_liftPlanarField 0 hF.1,planeAxisProjection_representative]

lemma planar_integral_divergence_zero {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    (∫ y : TransverseProduct,planeDivergence F (planarRepresentative y))=0 := by
  have hLF := liftPlanarField_admissible (0 : Fin 3) hF
  have hc := continuous_periodic_descent (continuous_divergence hLF.1) (divergence_periodic hLF.2.1)
  have hz : (∫ z : Torus,divergence (liftPlanarField 0 F) (representative z) ∂torusVolume)=0 := by
    have hh := setIntegral_lift (continuous_divergence hLF.1) (divergence_periodic hLF.2.1) (E := univ) MeasurableSet.univ
    simpa only [setIntegral_univ,preimage_univ,inter_univ,integral_divergence_fundamentalCube hLF] using hh
  have hh := axialSliceIntegral_pairing (E := univ) MeasurableSet.univ (0 : Fin 3) hc
    (ψ := fun _ ↦ (1 : ℝ)) continuous_const
  simp only [one_mul,setIntegral_univ] at hh
  rw [hz] at hh
  simp only [axialSliceIntegral,axialSlice,mem_univ,ofPred_true,
    divergence_liftPlanarField 0 hF.1,planeAxisProjection_representative,setIntegral_univ] at hh
  simpa using hh

lemma planarAdmissibleField_neg {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    PlanarAdmissibleField (fun y ↦ -F y) := by
  refine ⟨hF.1.neg,fun n y ↦ congrArg Neg.neg (hF.2.1 n y),?_⟩
  intro y
  simpa only [norm_neg] using hF.2.2 y

lemma planeDivergence_neg (F : Plane →Plane) (y : Plane) :
    planeDivergence (fun z ↦ -F z) y=-planeDivergence F y := by
  simp [planeDivergence]
  ring

lemma planar_integral_divergence_compl {A : Set TransverseProduct} (hA : NullMeasurableSet A volume)
    {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    (∫ y in Aᶜ,planeDivergence F (planarRepresentative y))=
      -(∫ y in A,planeDivergence F (planarRepresentative y)) := by
  have hi := integral_add_compl₀ hA
    ((planar_descended_divergence_continuous hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [planar_integral_divergence_zero hF] at hi
  linarith

theorem planarTorusPerimeter_compl {A : Set TransverseProduct} (hA : NullMeasurableSet A volume) :
    planarTorusPerimeter Aᶜ=planarTorusPerimeter A := by
  have hle : ∀ B : Set TransverseProduct,NullMeasurableSet B volume →
      planarTorusPerimeter Bᶜ≤planarTorusPerimeter B := by
    intro B hB
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply le_iSup_of_le (fun y ↦ -F y)
    apply le_iSup_of_le (planarAdmissibleField_neg hF)
    rw [planar_integral_divergence_compl hB hF]
    simp only [planeDivergence_neg,integral_neg,le_refl]
  exact le_antisymm (hle A hA) (by simpa only [compl_compl] using hle Aᶜ hA.compl)

lemma planarTorusPerimeter_congr_ae {A B : Set TransverseProduct} (h : A=ᵐ[volume]B) :
    planarTorusPerimeter A=planarTorusPerimeter B := by
  unfold planarTorusPerimeter
  congr 1
  funext F
  congr 1
  funext hF
  rw [setIntegral_congr_set h]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_complement_octant_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E) :
    ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE (fun i ↦ !b i) x y →
      quotientMap y∈openRepresentative Eᶜ →quotientMap x∈openRepresentative Eᶜ := by
  have hcl := isMinimizerAt_closure_openRepresentative_null hV hmin
  intro u hu v hv huv hvO
  simp only [openRepresentative,compl_compl,mem_compl_iff] at hvO ⊢
  intro hucl
  have hur : u∈closedUpperOctant := fun i ↦ ⟨(hu i).1.le,(hu i).2.le⟩
  have hvr : v∈closedUpperOctant := fun i ↦ ⟨(hv i).1.le,(hv i).2.le⟩
  have hh := octant_downset_closure (isOpen_openRepresentative E)
    (reflection_invariant_openRepresentative hmin.1.1 hR) hd hvr hur
    ((orientedCoordinateLE_reverse b u v).mp huv) (by rwa [hcl])
  rw [hcl] at hh
  exact hvO (by simpa only [compl_compl] using hh)

lemma axialSectionCorner_reverse (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 →Bool) :
    axialSectionCorner (fun k ↦ !b k) i t n=axialSectionCorner b i t (fun j ↦ !n j) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨j,rfl⟩
  · subst k; simp [axialSectionCorner]
  · simp only [axialSectionCorner,Fin.insertNth_apply_succAbove]
    dsimp only [octantHeight]
    by_cases hn : n j=true <;> by_cases hb : b (i.succAbove j)=true <;> norm_num [hn,hb]

lemma openRepresentative_compl_eq {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    openRepresentative Eᶜ=(closure (openRepresentative E))ᶜ := by
  rw [isMinimizerAt_closure_openRepresentative_null hV hmin]
  simp only [openRepresentative,compl_compl]

lemma closure_openRepresentative_compl_eq {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    closure (openRepresentative Eᶜ)=(openRepresentative E)ᶜ := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  rw [isMinimizerAt_closure_openRepresentative_null hVc ((isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin)]
  simp only [openRepresentative,compl_compl]

lemma axialSlice_openRepresentative_compl_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) (t : AxisCircle)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i t)=0) :
    axialSlice (openRepresentative Eᶜ) i t=ᵐ[volume]((axialSlice (openRepresentative E) i t)ᶜ : Set TransverseProduct) := by
  have hnb : ∀ᵐ y : TransverseProduct,y∉axialSlice (frontier (openRepresentative E)) i t := by
    rw [ae_iff]
    convert hn using 2
    ext y
    simp
  filter_upwards [hnb] with y hy
  rw [openRepresentative_compl_eq hV hmin]
  apply propext
  change ((torusAxialSplit i).symm (t,y)∉closure (openRepresentative E)) ↔
    (torusAxialSplit i).symm (t,y)∉openRepresentative E
  constructor
  · intro h hc; exact h (subset_closure hc)
  · intro h hc
    apply hy
    change (torusAxialSplit i).symm (t,y)∈frontier (openRepresentative E)
    rw [(isOpen_openRepresentative E).frontier_eq]
    exact ⟨hc,h⟩

lemma axialSlice_complement_volume {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) (t : AxisCircle)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i t)=0) :
    volume.real (axialSlice (openRepresentative Eᶜ) i t)=
      1-volume.real (axialSlice (openRepresentative E) i t) := by
  have hv : volume (axialSlice (openRepresentative E) i t)≤1 := by
    simpa using (measure_mono (subset_univ (axialSlice (openRepresentative E) i t)) : volume _≤volume univ)
  rw [measureReal_def,measure_congr (axialSlice_openRepresentative_compl_ae hV hmin i t hn)]
  rw [measure_compl (axialSlice_measurable (isOpen_openRepresentative E).measurableSet i t) (measure_ne_top _ _),
    measure_univ,ENNReal.toReal_sub_of_le hv ENNReal.one_ne_top,
    ENNReal.toReal_one]
  rfl

lemma axialSlice_complement_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) (t : AxisCircle)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i t)=0) :
    planarTorusPerimeter (axialSlice (openRepresentative Eᶜ) i t)=
      planarTorusPerimeter (axialSlice (openRepresentative E) i t) := by
  rw [planarTorusPerimeter_congr_ae (axialSlice_openRepresentative_compl_ae hV hmin i t hn),
    planarTorusPerimeter_compl (axialSlice_measurable (isOpen_openRepresentative E).measurableSet i t).nullMeasurableSet]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_extent_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hin : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E)
    (hout0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∉closure (openRepresentative E))
    (hout1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∉closure (openRepresentative E)) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle),‖y 1‖<L) ∧
      ENNReal.ofReal (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))/L+Real.pi*L)≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hzero : (0 : TransverseProduct)∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle) := by
    change (torusAxialSplit i).symm ((t : AxisCircle),0+axialSectionCenter b i)∈openRepresentative E
    rwa [centered_section_zero]
  have hv0 : planarFirstAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_first_axis] at hz
    exact hout0 hz
  have hv1 : planarAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_second_axis] at hz
    exact hout1 hz
  have hp := planar_radial_calibration (centeredAxialSlice_isOpen (isOpen_openRepresentative E) b i _)
    (isMinimizerAt_centered_section_radial hV hmin hR hd i _) hzero hv0 hv1
  simpa only [centeredAxialSlice_volume,centeredAxialSlice_perimeter] using hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_complement_calibration {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hout : quotientMap (axialSectionCorner b i t (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (t : AxisCircle),‖y 1‖<L) ∧
      ENNReal.ofReal ((1-volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))/L+Real.pi*L)≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) ∧
      ENNReal.ofReal (2*Real.sqrt (Real.pi*(1-volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
  have hRc (i : Fin 3) : Eᶜ=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' Eᶜ) := (hR i).compl
  have hdc := isMinimizerAt_complement_octant_downset hV hmin hR hd
  have hswap0 : (fun j : Fin 2 ↦ !(j==0))=(fun j ↦ j==1) := by funext j; fin_cases j <;> decide
  have hswap1 : (fun j : Fin 2 ↦ !(j==1))=(fun j ↦ j==0) := by funext j; fin_cases j <;> decide
  have hin : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun _ ↦ false))∈openRepresentative Eᶜ := by
    rw [openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse]
    exact hout
  have hv0 : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun j ↦ j==0))∉closure (openRepresentative Eᶜ) := by
    rw [closure_openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse,hswap0]
    simpa using hin1
  have hv1 : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun j ↦ j==1))∉closure (openRepresentative Eᶜ) := by
    rw [closure_openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse,hswap1]
    simpa using hin0
  obtain ⟨L,hL,hband,hp⟩ := isMinimizerAt_section_extent_perimeter hVc hmc hRc hdc i t hin hv0 hv1
  have hh := isMinimizerAt_section_disk_perimeter hVc hmc hRc hdc i t hin hv0 hv1
  rw [axialSlice_complement_volume hV hmin i _ hn,axialSlice_complement_perimeter hV hmin i _ hn] at hp hh
  exact ⟨L,hL,hband,hp,hh⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
