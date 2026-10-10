import Mathlib
import OAI.Geometry.CubicTorus.Reflection.AxialNormalCalibration

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

def sliceJensenCutoff : ℝ := Real.sqrt 48/7

def sliceJensenG (x : ℝ) : ℝ :=
  (1-(49/50 : ℝ)*(min x sliceJensenCutoff)^2)/
    Real.sqrt (1-(min x sliceJensenCutoff)^2)

lemma sliceJensenCutoff_pos : 0<sliceJensenCutoff := by
  dsimp [sliceJensenCutoff]
  positivity
lemma sliceJensenCutoff_sq : sliceJensenCutoff^2=(48/49 : ℝ) := by
  dsimp [sliceJensenCutoff]
  rw [div_pow,Real.sq_sqrt (by norm_num)]
  norm_num
lemma sliceJensenCutoff_lt_one : sliceJensenCutoff<1 := by
  nlinarith [sliceJensenCutoff_sq,sliceJensenCutoff_pos]
lemma sqrt_cutoff : Real.sqrt (1-sliceJensenCutoff^2)=(1/7 : ℝ) := by
  rw [sliceJensenCutoff_sq]
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ)≤1-48/49)
  have h0 := Real.sqrt_nonneg (1-(48/49 : ℝ))
  nlinarith

lemma sliceJensenG_cutoff (x : ℝ) (hx : sliceJensenCutoff≤x) :
    sliceJensenG x=(7/25 : ℝ) := by
  rw [sliceJensenG,min_eq_right hx,sqrt_cutoff,sliceJensenCutoff_sq]
  norm_num

theorem sliceJensenG_properties {x : ℝ} (hx : x∈Ioo (0 : ℝ) 1) :
    sliceJensenG x∈Icc (0 : ℝ) 1 ∧
      sliceJensenG x*Real.sqrt (1-x^2)≤1-(49/50 : ℝ)*x^2 := by
  have hs := sqrt_one_sub_sq_pos hx
  have hsq : (Real.sqrt (1-x^2))^2=1-x^2 := Real.sq_sqrt (by nlinarith [hx.1,hx.2])
  by_cases hxd : x≤ sliceJensenCutoff
  · have he : sliceJensenG x=(1-(49/50 : ℝ)*x^2)/Real.sqrt (1-x^2) := by
      rw [sliceJensenG,min_eq_left hxd]
    have hslow : (1/7 : ℝ)≤Real.sqrt (1-x^2) := by
      rw [← sqrt_cutoff]
      apply Real.sqrt_le_sqrt
      nlinarith [sliceJensenCutoff_pos,hx.1]
    have hsone : Real.sqrt (1-x^2)≤1 := by nlinarith [sq_nonneg x,Real.sqrt_nonneg (1-x^2)]
    rw [he]
    refine ⟨⟨div_nonneg (by nlinarith [sq_nonneg x,hx.1,hx.2]) hs.le,
      (div_le_one hs).mpr ?_⟩,?_⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hsone) (show 0≤49*Real.sqrt (1-x^2)-1 by linarith)]
    · rw [div_mul_cancel₀ _ (ne_of_gt hs)]
  · rw [sliceJensenG_cutoff x (le_of_not_ge hxd)]
    refine ⟨by norm_num,?_⟩
    nlinarith [sq_nonneg (7*Real.sqrt (1-x^2)-1)]

theorem slice_jensen_density_inequality {a p q r : ℝ} (hp : 0<p)
    (hm : q/p∈Ioo (0 : ℝ) 1)
    (hsupport : sliceSupportC (q/p) (sliceJensenG (q/p))*p+
      sliceSupportD (q/p) (sliceJensenG (q/p))*q+sliceJensenG (q/p)*r≤a) :
    sliceJensenG (q/p)*r≤a-(49/50 : ℝ)*q := by
  let m := q/p
  let J := sliceJensenG m
  have hm0 : m≠0 := ne_of_gt hm.1
  have he : q=p*m := by dsimp [m]; field_simp
  have hc := slice_support_contact (m := m) (J := J) hm
  have hG := (sliceJensenG_properties (x := m) hm).2
  have hpos : 0≤p/m := div_nonneg hp.le hm.1.le
  have hcan : sliceSupportC m J*p+sliceSupportD m J*q=
      (p/m)*(1-J*Real.sqrt (1-m^2)) := by
    rw [he,← hc]
    field_simp
  change sliceSupportC m J*p+sliceSupportD m J*q+J*r≤a at hsupport
  rw [hcan] at hsupport
  have hh := mul_le_mul_of_nonneg_left hG hpos
  have ee : (p/m)*((49/50 : ℝ)*m^2)=(49/50 : ℝ)*q := by
    rw [he]
    field_simp
  change J*r≤a-(49/50 : ℝ)*q
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace CubicTorus

theorem circle_jensen_supports_ae {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {h : α → AddCircle (1 : ℝ)}
    (hh : Continuous h) (hac : Measure.map h μ≪volume)
    {u : α → ℝ} (hu : Continuous u) (hu01 : ∀ x,u x∈Icc (0 : ℝ) 1)
    {a p q r : AddCircle (1 : ℝ) → ℝ}
    (ha : CircleSmoothDensity μ h (fun _ => 1) a)
    (hp : CircleSmoothDensity μ h u p)
    (hq : CircleSmoothDensity μ h (fun x => (u x)^2) q)
    (hr : CircleSmoothDensity μ h (fun x => Real.sqrt (1-(u x)^2)) r) :
    ∀ᵐ t,∀ m∈Ioo (0 : ℝ) 1,∀ J∈Icc (0 : ℝ) 1,
      sliceSupportC m J*p t+sliceSupportD m J*q t+J*r t≤a t := by
  let B := (Ioo (0 : ℝ) 1) × (Icc (0 : ℝ) 1)
  have : Nonempty B := ⟨(⟨1/2,by constructor <;> norm_num⟩,⟨0,by constructor <;> norm_num⟩)⟩
  have hmc : Continuous (fun b : B => (b.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hJc : Continuous (fun b : B => (b.2 : ℝ)) := continuous_subtype_val.comp continuous_snd
  have hsc : Continuous (fun b : B => Real.sqrt (1-(b.1 : ℝ)^2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hmc.pow 2))
  have hsl : Continuous (fun b : B => sliceHalfAngleSlope b.1) := by
    apply continuous_const.div (hsc.mul (continuous_const.add hsc))
    intro b
    exact mul_ne_zero (ne_of_gt (sqrt_one_sub_sq_pos b.1.property)) (by change 1+Real.sqrt (1-(b.1 : ℝ)^2)≠0; positivity)
  have hCc : Continuous (fun b : B => sliceSupportC b.1 b.2) := by
    exact (((continuous_const.sub hJc).mul continuous_const).div hmc
      (fun b => ne_of_gt b.1.property.1)).add
      (hJc.mul ((continuous_sliceHalfAngle.comp hmc).sub (hmc.mul hsl)))
  have hDc : Continuous (fun b : B => sliceSupportD b.1 b.2) := by
    exact (((continuous_const.sub hJc).neg).div (hmc.pow 2)
      (fun b => pow_ne_zero _ (ne_of_gt b.1.property.1))).add (hJc.mul hsl)
  have hf : ∀ᵐ t,∀ b : B,
      sliceSupportC b.1 b.2*p t+sliceSupportD b.1 b.2*q t+(b.2 : ℝ)*r t≤a t := by
    apply ae_forall_of_closed_parameters volume
    · intro t
      exact isClosed_le (((hCc.mul continuous_const).add (hDc.mul continuous_const)).add
        (hJc.mul continuous_const)) continuous_const
    intro b
    let C := sliceSupportC (b.1 : ℝ) (b.2 : ℝ)
    let D := sliceSupportD (b.1 : ℝ) (b.2 : ℝ)
    have hu2 := hu.pow 2
    have hur : Continuous (fun x => Real.sqrt (1-(u x)^2)) := Real.continuous_sqrt.comp (continuous_const.sub hu2)
    have hc := hu.const_mul C
    have hd := hu2.const_mul D
    have hj := hur.const_mul (b.2 : ℝ)
    have hw := ((hp.const_mul C).add (hq.const_mul D) hh hc hd).add
      (hr.const_mul (b.2 : ℝ)) hh (hc.add hd) hj
    exact hw.ae_le ha hh hac ((hc.add hd).add hj) continuous_const
      (fun x => slice_jensen_support b.1.property b.2.property (hu01 x))
  exact hf.mono fun t ht m hm J hJ => ht (⟨m,hm⟩,⟨J,hJ⟩)

theorem circle_conditional_jensen_ae {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {h : α → AddCircle (1 : ℝ)}
    (hh : Continuous h) (hac : Measure.map h μ≪volume)
    {u : α → ℝ} (hu : Continuous u) (hu01 : ∀ x,u x∈Icc (0 : ℝ) 1)
    {a p q r : AddCircle (1 : ℝ) → ℝ}
    (ha : CircleSmoothDensity μ h (fun _ => 1) a)
    (hp : CircleSmoothDensity μ h u p)
    (hq : CircleSmoothDensity μ h (fun x => (u x)^2) q)
    (hr : CircleSmoothDensity μ h (fun x => Real.sqrt (1-(u x)^2)) r) :
    ∀ᵐ t,0<p t → q t/p t∈Ioo (0 : ℝ) 1 →
      sliceJensenG (q t/p t)*r t≤a t-(49/50 : ℝ)*q t := by
  filter_upwards [circle_jensen_supports_ae hh hac hu hu01 ha hp hq hr] with t ht
  intro hpt hmt
  exact slice_jensen_density_inequality hpt hmt
    (ht _ hmt _ (sliceJensenG_properties hmt).1)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma sliceSupport_sum {m J : ℝ} (hm : m∈Ioo (0 : ℝ) 1) :
    sliceSupportC m J+sliceSupportD m J=
      (1-J)*(2/m-1/m^2)+J*(sliceHalfAngle m+
        Real.sqrt (1-m^2)/((1+m)*(1+Real.sqrt (1-m^2)))) := by
  have hs := sqrt_one_sub_sq_pos hm
  have he : (Real.sqrt (1-m^2))^2=1-m^2 := Real.sq_sqrt (by nlinarith [hm.1,hm.2])
  have hm0 : m≠0 := ne_of_gt hm.1
  have hs0 : Real.sqrt (1-m^2)≠0 := ne_of_gt hs
  have hm1 : 1+m≠0 := by linarith [hm.1]
  have hs1 : 1+Real.sqrt (1-m^2)≠0 := by positivity
  have heq : (1-m)*sliceHalfAngleSlope m=
      Real.sqrt (1-m^2)/((1+m)*(1+Real.sqrt (1-m^2))) := by
    dsimp [sliceHalfAngleSlope]
    field_simp
    nlinarith
  dsimp only [sliceSupportC,sliceSupportD]
  rw [← heq]
  ring

lemma slice_support_endpoint {a p r J : ℝ} (hJ : J∈Icc (0 : ℝ) 1)
    (hs : ∀ m∈Ioo (0 : ℝ) 1,sliceSupportC m J*p+sliceSupportD m J*p+J*r≤a) :
    p+J*r≤a := by
  let L : ℝ → ℝ := fun m => (1-J)*(2/m-1/m^2)+J*(sliceHalfAngle m+
    Real.sqrt (1-m^2)/((1+m)*(1+Real.sqrt (1-m^2))))
  have hLc : ContinuousAt L 1 := by
    dsimp [L,sliceHalfAngle]
    fun_prop (disch := norm_num)
  have hL1 : L 1=1 := by norm_num [L,sliceHalfAngle]
  have hlim : Tendsto (fun n : ℕ => 1-(J+1)/((n : ℝ)+1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_one_div,mul_zero,sub_zero] using tendsto_const_nhds.sub
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (J+1))
  have hlim' := (hLc.tendsto.comp hlim).mul_const p
  have hlim'' := hlim'.add_const (J*r)
  rw [hL1,one_mul] at hlim''
  apply le_of_tendsto hlim''
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn0 : (1 : ℝ)<(n : ℝ) := by exact_mod_cast (show 1<n by omega)
  have hmn : 1-(J+1)/((n : ℝ)+1)∈Ioo (0 : ℝ) 1 := by
    constructor
    · have := (div_lt_one (by positivity : (0 : ℝ)<(n : ℝ)+1)).mpr
        (by linarith [hJ.2] : J+1<(n : ℝ)+1)
      linarith
    · have : 0<(J+1)/((n : ℝ)+1) := div_pos (by linarith [hJ.1]) (by positivity)
      linarith
  dsimp only [Function.comp_apply]
  rw [show L (1-(J+1)/((n : ℝ)+1))=sliceSupportC (1-(J+1)/((n : ℝ)+1)) J+
    sliceSupportD (1-(J+1)/((n : ℝ)+1)) J from (sliceSupport_sum hmn).symm,add_mul]
  exact hs _ hmn

theorem slice_jensen_closed_cone {a p q r : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hqp : q≤p) (hra : r≤a)
    (hs : ∀ m∈Ioo (0 : ℝ) 1,∀ J∈Icc (0 : ℝ) 1,
      sliceSupportC m J*p+sliceSupportD m J*q+J*r≤a) :
    sliceJensenG (q/p)*r≤a-(49/50 : ℝ)*q := by
  by_cases hq0 : q=0
  · have hG0 : sliceJensenG 0=1 := by
      rw [sliceJensenG,min_eq_left sliceJensenCutoff_pos.le]
      norm_num
    simpa [hq0,hG0] using hra
  have hqpos : 0<q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hppos : 0<p := lt_of_le_of_ne hp (by intro hzero; linarith only [hzero,hqpos,hqp])
  rcases lt_or_eq_of_le hqp with hlt|heq
  · have hm : q/p∈Ioo (0 : ℝ) 1 := ⟨div_pos hqpos hppos,(div_lt_one hppos).mpr hlt⟩
    exact slice_jensen_density_inequality hppos hm (hs _ hm _ (sliceJensenG_properties hm).1)
  · subst q
    have hG1 : sliceJensenG 1=(7/25 : ℝ) := sliceJensenG_cutoff 1 sliceJensenCutoff_lt_one.le
    have hend := slice_support_endpoint (a := a) (p := p) (r := r)
      (J := 7/25) (by constructor <;> norm_num) (fun m hm => hs m hm _ (by constructor <;> norm_num))
    rw [div_self (ne_of_gt hppos),hG1]
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace CubicTorus

lemma circle_conditional_jensen_closed_ae {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {h : α → AddCircle (1 : ℝ)}
    (hh : Continuous h) (hac : Measure.map h μ≪volume)
    {u : α → ℝ} (hu : Continuous u) (hu01 : ∀ x,u x∈Icc (0 : ℝ) 1)
    {a p q r : AddCircle (1 : ℝ) → ℝ}
    (ha : CircleSmoothDensity μ h (fun _ => 1) a)
    (hp : CircleSmoothDensity μ h u p)
    (hq : CircleSmoothDensity μ h (fun x => (u x)^2) q)
    (hr : CircleSmoothDensity μ h (fun x => Real.sqrt (1-(u x)^2)) r) :
    ∀ᵐ t,sliceJensenG (q t/p t)*r t≤a t-(49/50 : ℝ)*q t := by
  have hz : CircleSmoothDensity μ h (fun _ => 0) (fun _ => 0) := by
    refine ⟨integrable_zero _ _ _ ,?_⟩
    intro f hf hper
    simp
  have hp0 := hz.ae_le hp hh hac continuous_const hu (fun x => (hu01 x).1)
  have hq0 := hz.ae_le hq hh hac continuous_const (hu.pow 2) (fun x => sq_nonneg (u x))
  have hqp := hq.ae_le hp hh hac (hu.pow 2) hu (fun x => by nlinarith [(hu01 x).1,(hu01 x).2])
  have hra := hr.ae_le ha hh hac (Real.continuous_sqrt.comp (continuous_const.sub (hu.pow 2)))
    continuous_const (fun x => by
      simpa using Real.sqrt_le_sqrt (show 1-(u x)^2≤(1 : ℝ) by nlinarith [sq_nonneg (u x)]))
  filter_upwards [hp0,hq0,hqp,hra,circle_jensen_supports_ae hh hac hu hu01 ha hp hq hr] with t ht1 ht2 ht3 ht4 ht5
  exact slice_jensen_closed_cone ht1 ht2 ht3 ht4 ht5

lemma sliceJensenG_measurable : Measurable sliceJensenG := by
  unfold sliceJensenG
  fun_prop

lemma sliceJensenG_mem_Icc {x : ℝ} (hx : x∈Icc (0 : ℝ) 1) :
    sliceJensenG x∈Icc (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le hx.1 with h|h
  · subst x
    rw [sliceJensenG,min_eq_left sliceJensenCutoff_pos.le]
    norm_num
  rcases lt_or_eq_of_le hx.2 with h'|h'
  · exact (sliceJensenG_properties ⟨h,h'⟩).1
  · subst x
    rw [sliceJensenG_cutoff 1 sliceJensenCutoff_lt_one.le]
    norm_num

lemma circle_jensen_integrable {p q r : AddCircle (1 : ℝ) → ℝ}
    (hp : Integrable p) (hq : Integrable q) (hr : Integrable r)
    (hp0 : ∀ᵐ t,0≤p t) (hq0 : ∀ᵐ t,0≤q t) (hqp : q≤ᵐ[volume]p) :
    Integrable (fun t => sliceJensenG (q t/p t)*r t) := by
  have hg : AEStronglyMeasurable (fun t => sliceJensenG (q t/p t)) :=
    (sliceJensenG_measurable.comp_aemeasurable
      (hq.aestronglyMeasurable.aemeasurable.div hp.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hb : ∀ᵐ t,‖sliceJensenG (q t/p t)‖≤(1 : ℝ) := by
    filter_upwards [hp0,hq0,hqp] with t ht1 ht2 ht3
    have hm : q t/p t∈Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg ht2 ht1,?_⟩
      by_cases he : p t=0
      · simp [he]
      · exact (div_le_one (lt_of_le_of_ne ht1 (Ne.symm he))).mpr ht3
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sliceJensenG_mem_Icc hm).1] using
      (sliceJensenG_mem_Icc hm).2
  simpa only [mul_comm] using hr.mul_bdd hg hb

theorem circle_integrated_jensen {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {h : α → AddCircle (1 : ℝ)}
    (hh : Continuous h) (hac : Measure.map h μ≪volume)
    {u : α → ℝ} (hu : Continuous u) (hu01 : ∀ x,u x∈Icc (0 : ℝ) 1)
    {a p q r : AddCircle (1 : ℝ) → ℝ}
    (ha : CircleSmoothDensity μ h (fun _ => 1) a)
    (hp : CircleSmoothDensity μ h u p)
    (hq : CircleSmoothDensity μ h (fun x => (u x)^2) q)
    (hr : CircleSmoothDensity μ h (fun x => Real.sqrt (1-(u x)^2)) r) :
    Integrable (fun t => sliceJensenG (q t/p t)*r t) ∧
    (∫ t,sliceJensenG (q t/p t)*r t)≤μ.real univ-(49/50 : ℝ)*(∫ x,(u x)^2 ∂μ) := by
  have hz : CircleSmoothDensity μ h (fun _ => 0) (fun _ => 0) := by
    refine ⟨integrable_zero _ _ _ ,?_⟩
    intro f hf hper
    simp
  have hp0 := hz.ae_le hp hh hac continuous_const hu (fun x => (hu01 x).1)
  have hq0 := hz.ae_le hq hh hac continuous_const (hu.pow 2) (fun x => sq_nonneg (u x))
  have hqp := hq.ae_le hp hh hac (hu.pow 2) hu (fun x => by nlinarith [(hu01 x).1,(hu01 x).2])
  have hgi := circle_jensen_integrable hp.1 hq.1 hr.1 hp0 hq0 hqp
  refine ⟨hgi,?_⟩
  have hle := integral_mono_ae hgi (ha.1.sub (hq.1.const_mul (49/50)))
    (circle_conditional_jensen_closed_ae hh hac hu hu01 ha hp hq hr)
  simp only [Pi.sub_apply] at hle
  rw [integral_sub ha.1 (hq.1.const_mul _),integral_const_mul] at hle
  have hper : Function.Periodic (fun _ : ℝ => (1 : ℝ)) 1 := fun _ => rfl
  have hpm : hper.lift=(fun _ => (1 : ℝ)) := by
    funext t
    obtain ⟨x,rfl⟩ := Quotient.exists_rep t
    rfl
  have ham := ha.2 (fun _ => 1) contDiff_const hper
  have hqm := hq.2 (fun _ => 1) contDiff_const hper
  simp only [hpm,mul_one,integral_const,smul_eq_mul,mul_one] at ham hqm
  rwa [ham,hqm] at hle

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace
namespace CubicTorus

def axialJensenFlux (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H V : ℝ)
    (i : Fin 3) (t : AddCircle (1 : ℝ)) : ℝ :=
  (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V)

lemma axialTangentialSpeed_mem_Icc (i : Fin 3) (z : NormalBundle) :
    axialTangentialSpeed i z∈Icc (0 : ℝ) 1 := by
  refine ⟨norm_nonneg _,?_⟩
  have hh := axialTangentialSpeed_sq i z
  have hu := axialNormalWeight_le_one i z
  nlinarith [norm_nonneg (axialTangentPart i (z.2 : Cover))]

lemma sqrt_one_sub_axialTangentialSpeed_sq (i : Fin 3) (z : NormalBundle) :
    Real.sqrt (1-(axialTangentialSpeed i z)^2)=|((z.2 : Cover) i)| := by
  rw [axialTangentialSpeed_sq,axialNormalWeight,sub_sub_cancel,Real.sqrt_sq_eq_abs]

lemma axial_flux_smooth_density {V : ℝ} {E : Set Torus} (hE : MeasurableSet E)
    (hvol : torusVolume.real E=V) {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hc : Continuous (axialSectionArea E i)) :
    CircleSmoothDensity (μ : Measure NormalBundle) (axialBundleHeight i)
      (fun z => (axialTangentialSpeed i z)^2) (axialJensenFlux E μ H V i) := by
  have hvc : Continuous (axialCircleArea E i) :=
    continuous_periodic_lift (axialSectionArea_periodic E i) hc
  refine ⟨circle_continuous_integrable (continuous_const.add
    (continuous_const.mul (hvc.sub continuous_const))),?_⟩
  intro f hf hp
  change (∫ t,((μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V))*hp.lift t)=_
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
  simp only [zero_add,axialCircleArea_coe,Function.Periodic.lift_coe]
  rw [axial_density_moment hE hvol hH i hc hf hp]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change axialNormalWeight i z * f (z.1.1 i) =
      (axialTangentialSpeed i z)^2 * hp.lift (axialBundleHeight i z)
    rw [axialTangentialSpeed_sq]
    rfl

theorem axial_integrated_jensen {V : ℝ} {E : Set Torus} (hE : MeasurableSet E)
    (hvol : torusVolume.real E=V) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (i : Fin 3) (hc : Continuous (axialSectionArea E i))
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0)
    (hac : Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume) :
    ∃ r : AddCircle (1 : ℝ) → ℝ,Integrable r ∧ (∀ t,0≤r t) ∧
      (∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f →
        (∫ t,r t*f t)=∫ z,|((z.2 : Cover) i)| * f (axialBundleHeight i z) ∂(μ : Measure NormalBundle)) ∧
      Integrable (fun t => sliceJensenG (axialJensenFlux E μ H V i t/
        (axialCirclePerimeter E i t).toReal)*r t) ∧
      (∫ t,sliceJensenG (axialJensenFlux E μ H V i t/
        (axialCirclePerimeter E i t).toReal)*r t)≤
        (μ.mass : ℝ)-(49/50 : ℝ)*(μ.mass : ℝ)*axialFluxWeight μ i := by
  have hhc := continuous_axialBundleHeight i
  have huc := continuous_axialTangentialSpeed i
  obtain ⟨a,hai,ha0,ham⟩ := circle_nonneg_weighted_density (μ : Measure NormalBundle)
    hhc hac (w := fun _ => 1) continuous_const (fun _ => by norm_num)
  obtain ⟨r,hri,hr0,hrm⟩ := circle_nonneg_weighted_density (μ : Measure NormalBundle)
    hhc hac (w := fun z => Real.sqrt (1-(axialTangentialSpeed i z)^2))
    (Real.continuous_sqrt.comp (continuous_const.sub (huc.pow 2)))
    (fun _ => Real.sqrt_nonneg _)
  obtain ⟨_,_,hpi,hpm⟩ := axial_bv_coarea hE hμ hN hpN haN i hz hac
  have had : CircleSmoothDensity (μ : Measure NormalBundle) (axialBundleHeight i) (fun _ => 1) a :=
    ⟨hai,fun f hf hp => ham hp.lift (continuous_periodic_lift hp hf.continuous).measurable⟩
  have hpd : CircleSmoothDensity (μ : Measure NormalBundle) (axialBundleHeight i)
      (axialTangentialSpeed i) (fun t => (axialCirclePerimeter E i t).toReal) :=
    ⟨hpi,fun f hf hp => hpm hp.lift (continuous_periodic_lift hp hf.continuous).measurable⟩
  have hrd : CircleSmoothDensity (μ : Measure NormalBundle) (axialBundleHeight i)
      (fun z => Real.sqrt (1-(axialTangentialSpeed i z)^2)) r :=
    ⟨hri,fun f hf hp => hrm hp.lift (continuous_periodic_lift hp hf.continuous).measurable⟩
  obtain ⟨hJi,hJ⟩ := circle_integrated_jensen hhc hac huc (axialTangentialSpeed_mem_Icc i)
    had hpd (axial_flux_smooth_density hE hvol hH i hc) hrd
  refine ⟨r,hri,hr0,?_,hJi,?_⟩
  · intro f hf
    simpa only [sqrt_one_sub_axialTangentialSpeed_sq] using hrm f hf
  have hweight : (μ.mass : ℝ)*axialFluxWeight μ i=
      ∫ z,(axialTangentialSpeed i z)^2 ∂(μ : Measure NormalBundle) := by
    simp_rw [axialTangentialSpeed_sq]
    by_cases hm : (μ.mass : ℝ)=0
    · have hzμ : μ=0 := (FiniteMeasure.mass_zero_iff μ).mp (NNReal.coe_eq_zero.mp hm)
      simp [hzμ,axialFluxWeight]
    · dsimp [axialFluxWeight]
      field_simp
  have hmass : (μ : Measure NormalBundle).real univ=(μ.mass : ℝ) := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
  rw [hmass,← hweight] at hJ
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_unsigned_normal_density {μ : FiniteMeasure NormalBundle} (i : Fin 3) (b : Bool)
    {r g : AddCircle (1 : ℝ) → ℝ} (hr : Integrable r) (hg : Integrable g)
    (hrm : ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f →
      (∫ t,r t*f t)=∫ z,|((z.2 : Cover) i)| * f (axialBundleHeight i z) ∂(μ : Measure NormalBundle))
    (hgm : ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f → (∃ M : ℝ,∀ t,‖f t‖≤M) →
      (∫ t,g t*f t)=∫ z,-((z.2 : Cover) i)*f (axialBundleHeight i z) ∂(μ : Measure NormalBundle))
    (hsign : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ((z.2 : Cover) i)*chamberHeightSign b (axialBundleHeight i z)=|((z.2 : Cover) i)|) :
    r =ᵐ[volume] (fun t => -g t*chamberHeightSign b t) := by
  have hgi : Integrable (fun t => -g t*chamberHeightSign b t) :=
    hg.neg.mul_bdd (measurable_chamberHeightSign b).aestronglyMeasurable
      (Eventually.of_forall fun t => (norm_chamberHeightSign b t).le)
  apply circle_ae_eq_of_smooth_moments hr hgi
  intro f hf hp
  have hfc := continuous_periodic_lift hp hf.continuous
  obtain ⟨M,_,hM⟩ := (isCompact_univ.image hfc).isBounded.exists_pos_norm_le
  have htest := hgm (fun t => chamberHeightSign b t*hp.lift t)
    ((measurable_chamberHeightSign b).mul hfc.measurable)
    ⟨M,fun t => by rw [norm_mul,norm_chamberHeightSign,one_mul]; exact hM _ ⟨t,mem_univ _,rfl⟩⟩
  rw [hrm hp.lift hfc.measurable]
  have he : (∫ t,(-g t*chamberHeightSign b t)*hp.lift t)=
      -(∫ t,g t*(chamberHeightSign b t*hp.lift t)) := by
    simp only [neg_mul,mul_assoc,integral_neg]
  rw [he,htest,← integral_neg]
  apply integral_congr_ae
  filter_upwards [hsign] with z hz
  rw [← hz]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalComponent_integral_sq (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    (∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle))=
      (μ.mass : ℝ)*(1-axialFluxWeight μ i) := by
  by_cases hm : (μ.mass : ℝ)=0
  · have hz : μ=0 := by
      apply (FiniteMeasure.mass_zero_iff μ).mp
      exact NNReal.coe_eq_zero.mp hm
    simp [hz,axialFluxWeight]
  have hi : Integrable (fun z : NormalBundle => ((z.2 : Cover) i)^2) (μ : Measure NormalBundle) :=
    (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))=
      (μ.mass : ℝ)-(∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle)) := by
    change (∫ z,1-((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle))=_
    rw [integral_sub (integrable_const _) hi,normalMeasure_integral_one]
  rw [axialFluxWeight,he]
  field_simp; ring

lemma axialProjection_bound (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    (∫ z,|((z.2 : Cover) i)| ∂(μ : Measure NormalBundle))≤
      (μ.mass : ℝ)*Real.sqrt (1-axialFluxWeight μ i) := by
  by_cases hm : (μ.mass : ℝ)=0
  · have hz : μ=0 := by
      apply (FiniteMeasure.mass_zero_iff μ).mp
      exact NNReal.coe_eq_zero.mp hm
    simp [hz,axialFluxWeight]
  have hmpos : 0<(μ.mass : ℝ) := lt_of_le_of_ne μ.mass.coe_nonneg (Ne.symm hm)
  let f : NormalBundle → ℝ := fun z => |((z.2 : Cover) i)|
  have hc : Continuous f :=
    ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).abs
  have hi : Integrable f (μ : Measure NormalBundle) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have his : Integrable (fun z => f z^2) (μ : Measure NormalBundle) :=
    (hc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L := ∫ z,f z ∂(μ : Measure NormalBundle)
  let M : ℝ := μ.mass
  let c := L/M
  have hv : 0≤(∫ z,(f z-c)^2 ∂(μ : Measure NormalBundle)) :=
    integral_nonneg (fun z => sq_nonneg (f z-c))
  have hi2 : Integrable (fun z => 2*c*f z) (μ : Measure NormalBundle) := hi.const_mul (2*c)
  have hex : (∫ z,(f z-c)^2 ∂(μ : Measure NormalBundle))=
      (∫ z,f z^2 ∂(μ : Measure NormalBundle))-2*c*L+c^2*M := by
    have hia := integral_add (his.sub hi2) (integrable_const (c^2) : Integrable (fun _ : NormalBundle => c^2) (μ : Measure NormalBundle))
    change (∫ z,f z^2-2*c*f z+c^2 ∂(μ : Measure NormalBundle))=
      (∫ z,f z^2-2*c*f z ∂(μ : Measure NormalBundle))+(∫ _ : NormalBundle,c^2 ∂(μ : Measure NormalBundle)) at hia
    have hisub := integral_sub his hi2
    change (∫ z,f z^2-2*c*f z ∂(μ : Measure NormalBundle))=
      (∫ z,f z^2 ∂(μ : Measure NormalBundle))-(∫ z,2*c*f z ∂(μ : Measure NormalBundle)) at hisub
    rw [show (fun z => (f z-c)^2)=(fun z => f z^2-2*c*f z+c^2) from by funext z; ring,
      hia,hisub,integral_const_mul]
    simp only [integral_const,smul_eq_mul,L,M,Measure.real,← FiniteMeasure.ennreal_mass,
      ENNReal.coe_toReal]
    ring
  rw [hex] at hv
  have hsq : L^2≤M*(∫ z,f z^2 ∂(μ : Measure NormalBundle)) := by
    have hv' := mul_nonneg hv (le_of_lt hmpos)
    change 0≤(_-2*c*L+c^2*M)*M at hv'
    dsimp only [c] at hv'
    have hm' : M≠0 := hm
    field_simp at hv'
    nlinarith
  have hid : (∫ z,f z^2 ∂(μ : Measure NormalBundle))=M*(1-axialFluxWeight μ i) := by
    simpa only [f,sq_abs,M] using normalComponent_integral_sq μ i
  rw [hid] at hsq
  have hb : 0≤1-axialFluxWeight μ i := sub_nonneg.mpr (axialFluxWeight_le_one μ i hmpos)
  have hsqrt := Real.sq_sqrt hb
  change L≤M*Real.sqrt (1-axialFluxWeight μ i)
  have hright : 0≤M*Real.sqrt (1-axialFluxWeight μ i) := mul_nonneg hmpos.le (Real.sqrt_nonneg _)
  have hsquare : (M*Real.sqrt (1-axialFluxWeight μ i))^2=M*(M*(1-axialFluxWeight μ i)) := by
    rw [mul_pow,hsqrt]
    ring
  have hLL : L^2≤(M*Real.sqrt (1-axialFluxWeight μ i))^2 := by rwa [hsquare]
  nlinarith only [hLL,hright]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma chamber_corner_coordinate_twice (s : Fin 3 → Bool) (i : Fin 3) :
    2*chamberCorner s i = ((if s i then 1 else 0 : ℤ) : ℝ) := by
  cases hs : s i <;> norm_num [chamberCorner,hs]

lemma chamber_reflected_coordinate (s : Fin 3 → Bool) (i : Fin 3) (x : Cover) :
    (coverCoordinateReflection i x+latticeVector
      (fun j => if j=i then (if s i then 1 else 0 : ℤ) else 0)) i=
      2*chamberCorner s i-x i := by
  simp only [PiLp.add_apply,coverCoordinateReflection_apply,ite_true,latticeVector]
  rw [← chamber_corner_coordinate_twice]
  ring

theorem isMinimizerAt_chamber_support_positive {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E))
    (hbox : ∀ i : Fin 3,|x i-chamberCorner s i|<1/2)
    (hne : x≠chamberCorner s) : 0<⟪N x,x-chamberCorner s⟫ := by
  have hsign (i : Fin 3) : x i≠chamberCorner s i → 0<N x i*(x i-chamberCorner s i) := by
    intro hi
    rcases lt_or_gt_of_ne hi with hlt|hgt
    · let m : Fin 3 → ℤ := fun j => if j=i then (if s i then 1 else 0) else 0
      let y := coverCoordinateReflection i x+latticeVector m
      have hy : quotientMap y∈frontier (openRepresentative E) := by
        rw [show quotientMap y=coordinateReflection i (quotientMap x) by
          change quotientMap (coverCoordinateReflection i x+latticeVector m)=_
          rw [quotientMap_add,quotientMap_latticeVector,add_zero,quotientMap_coordinateReflection]]
        change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
        rwa [frontier_reflection_invariant hE i (hs i)]
      have hcoord : y i=2*chamberCorner s i-x i := chamber_reflected_coordinate s i x
      have hb := abs_lt.mp (hbox i)
      have hyhalf := mem_coordinateHalf_of_chamber_interval s y i
        (show chamberCorner s i<y i ∧ y i<chamberCorner s i+1/2 by
          rw [hcoord]; constructor <;> linarith [hb.1])
      have hNy := hsg y i ⟨hy,hyhalf⟩
      have hNr := congrArg (fun v : Cover => v i)
        (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hx)
      simp only [coverCoordinateReflection_apply,ite_true] at hNr
      have hNp : N y i=N (coverCoordinateReflection i x) i := congrArg (fun v : Cover => v i) (hp m _)
      rw [hNp] at hNy
      apply mul_pos_of_neg_of_neg
      · linarith
      · exact sub_neg.mpr hlt
    · have hb := abs_lt.mp (hbox i)
      exact mul_pos (hsg x i ⟨hx,mem_coordinateHalf_of_chamber_interval s x i
        ⟨hgt,by linarith [hb.2]⟩⟩) (sub_pos.mpr hgt)
  have hex : ∃ i : Fin 3,x i≠chamberCorner s i := by
    by_contra hn
    push Not at hn
    exact hne (by ext i; exact hn i)
  obtain ⟨i,hi⟩ := hex
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial,PiLp.sub_apply]
  apply Finset.sum_pos'
  · intro j _
    by_cases hj : x j=chamberCorner s j
    · simp [hj]
    · simpa only [mul_comm] using (hsign j hj).le
  · exact ⟨i,Finset.mem_univ i,by simpa only [mul_comm] using hsign i hi⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma inner_tangent_projection {n : Cover} (hn : ‖n‖=1) (v w : Cover) :
    ⟪v-⟪n,v⟫ • n,w-⟪n,w⟫ • n⟫=⟪v,w⟫-⟪n,v⟫*⟪n,w⟫ := by
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,real_inner_comm v n]
  ring

lemma normal_position_gradient_trace {N X : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpX : ∀ m x,X (x+latticeVector m)=X x)
    (z : NormalBundle) (hd : fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover) :
    (∑ i : Fin 3,⟪smoothScalarGradient (normalComponentScalar N hN hpN i) z,
      smoothScalarGradient (normalComponentScalar X hX hpX i) z⟫)=
        tangentialDivergence N z.1 z.2 := by
  have hg (i : Fin 3) : gradient (normalComponentScalar X hX hpX i).val z.1=
      EuclideanSpace.single i 1 := by
    rw [show (normalComponentScalar X hX hpX i).val=(fun y => ⟪EuclideanSpace.single i 1,X y⟫) from rfl,
      gradient_normal_component hX,hd]
    rw [ContinuousLinearMap.adjoint_id]
    rfl
  have hn (i : Fin 3) : gradient (normalComponentScalar N hN hpN i).val z.1=
      (fderiv ℝ N z.1).adjoint (EuclideanSpace.single i 1) := gradient_normal_component hN _ _
  change (∑ i : Fin 3,⟪gradient (normalComponentScalar N hN hpN i).val z.1-
      ⟪(z.2 : Cover),gradient (normalComponentScalar N hN hpN i).val z.1⟫ • (z.2 : Cover),
    gradient (normalComponentScalar X hX hpX i).val z.1-
      ⟪(z.2 : Cover),gradient (normalComponentScalar X hX hpX i).val z.1⟫ • (z.2 : Cover)⟫)=_
  simp_rw [hg,hn,inner_tangent_projection z.2.property,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
  rw [Finset.sum_sub_distrib]
  unfold tangentialDivergence
  congr 1
  · simp [divergence,EuclideanSpace.inner_single_left]
  · simp [PiLp.inner_apply,mul_comm]

theorem translation_jacobi_position_identity {μ : FiniteMeasure NormalBundle}
    {N X : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpX : ∀ m x,X (x+latticeVector m)=X x)
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hpN i)) w=0)
    (hd : ∀ᵐ z ∂(μ : Measure NormalBundle),fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover) :
    (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*⟪N z.1,X z.1⟫
      ∂(μ : Measure NormalBundle))=
      ∫ z,tangentialDivergence N z.1 z.2 ∂(μ : Measure NormalBundle) := by
  let f (i : Fin 3) := normalComponentScalar N hN hpN i
  let g (i : Fin 3) := normalComponentScalar X hX hpX i
  let J (i : Fin 3) (z : NormalBundle) := ⟪smoothScalarGradient (f i) z,smoothScalarGradient (g i) z⟫-
    coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*(f i).val z.1*(g i).val z.1
  have hi (i : Fin 3) : Integrable (J i) (μ : Measure NormalBundle) := by
    exact (((smoothScalarGradient (f i)).continuous.inner (𝕜 := ℝ) (smoothScalarGradient (g i)).continuous).sub
      ((((normal_curvature_continuous hN).comp normalEmbedding_continuous.fst).mul
        (smoothScalarValue (f i)).continuous).mul (smoothScalarValue (g i)).continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hzero (i : Fin 3) : (∫ z,J i z ∂(μ : Measure NormalBundle))=0 := by
    rw [← surfaceSmoothJet_bilinear]
    exact hj i _ (subset_closure ⟨g i,rfl⟩)
  have hsum : (∫ z,∑ i : Fin 3,J i z ∂(μ : Measure NormalBundle))=0 := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    simp_rw [hzero]; simp
  have he : (fun z : NormalBundle => ∑ i : Fin 3,J i z)=ᵐ[(μ : Measure NormalBundle)]
      (fun z => tangentialDivergence N z.1 z.2-
        coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*⟪N z.1,X z.1⟫) := by
    filter_upwards [hd] with z hdz
    simp only [J,Finset.sum_sub_distrib]
    rw [normal_position_gradient_trace hN hX hpN hpX z hdz]
    congr 1
    simp only [f,g,normalComponentScalar_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [integral_congr_ae he] at hsum
  have hni : Integrable (fun z : NormalBundle => tangentialDivergence N z.1 z.2) (μ : Measure NormalBundle) :=
    (continuous_tangentialDivergence hN).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hui : Integrable (fun z : NormalBundle =>
      coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*⟪N z.1,X z.1⟫) (μ : Measure NormalBundle) :=
    (((normal_curvature_continuous hN).comp normalEmbedding_continuous.fst).mul
      ((hN.continuous.comp normalEmbedding_continuous.fst).inner (𝕜 := ℝ)
        (hX.continuous.comp normalEmbedding_continuous.fst))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hni hui] at hsum
  exact (sub_eq_zero.mp hsum).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_periodic_position_box (c : Cover) {r : ℝ} (hr : 0<r) (hr' : r<1/2) :
    ∃ X : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) X ∧
      (∀ m x,X (x+latticeVector m)=X x) ∧
      ∀ x : Cover,(∀ i : Fin 3,|x i-c i|≤r) →
        X=ᶠ[𝓝 x](fun y => y-c) := by
  let b : ContDiffBump (1/2 : ℝ) :=
    ⟨(r+1/2)/2,(r+3/2)/4,by positivity,by linarith⟩
  let χ : Cover → ℝ := fun x => ∏ i : Fin 3,b (x i)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := contDiff_prod fun i _ =>
    b.contDiff.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  let g : Cover → Cover := fun x => χ x • (x-cubeCenter)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hχ.smul (contDiff_id.sub contDiff_const)
  let K : Set Cover := {x | ∀ i : Fin 3,|x i-1/2|≤b.rOut}
  have hK : IsClosed K := by
    change IsClosed {x : Cover | ∀ i : Fin 3,|x i-1/2|≤b.rOut}
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le
      (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.sub continuous_const).abs) continuous_const
  have hsK : tsupport g⊆K := by
    apply closure_minimal _ hK
    intro x hx i
    have hc : χ x≠0 := by
      intro hz
      exact hx (by simp only [g,hz,zero_smul])
    have hi : b (x i)≠0 := (Finset.prod_ne_zero_iff.mp hc) i (Finset.mem_univ i)
    have hmem : x i∈tsupport (b : ℝ → ℝ) := subset_closure hi
    rw [b.tsupport_eq] at hmem
    simpa only [Metric.mem_closedBall,Real.dist_eq] using hmem
  have hsO : tsupport g⊆{x : Cover | ∀ i,0<x i ∧ x i<1} := by
    intro x hx i
    have hh := abs_le.mp (hsK hx i)
    change -((r+3/2)/4)≤x i-1/2 ∧ x i-1/2≤(r+3/2)/4 at hh
    constructor <;> linarith [hh.1,hh.2]
  have hcomp : HasCompactSupport g := isCompact_closedFundamentalCube.of_isClosed_subset isClosed_closure (by
    intro x hx
    refine ⟨WithLp.ofLp x,?_,by simp⟩
    exact ⟨fun i => (hsO hx i).1.le,fun i => (hsO hx i).2.le⟩)
  let P := latticePeriodize g
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := latticePeriodize_contDiff hg hcomp
  let X : Cover → Cover := fun x => P (x-c+cubeCenter)
  refine ⟨X,hP.comp ((contDiff_id.sub contDiff_const).add contDiff_const),?_,?_⟩
  · intro m x
    change P (x+latticeVector m-c+cubeCenter)=P (x-c+cubeCenter)
    rw [show x+latticeVector m-c+cubeCenter=(x-c+cubeCenter)+latticeVector m by abel]
    exact latticePeriodize_periodic g m _
  · intro x hx
    let y := x-c+cubeCenter
    have hy (i : Fin 3) : 0≤y i ∧ y i≤1 := by
      have hh := abs_le.mp (hx i)
      change 0≤x i-c i+1/2 ∧ x i-c i+1/2≤1
      constructor <;> linarith [hh.1,hh.2]
    have hb (i : Fin 3) : ∀ᶠ z in 𝓝 y,b (z i)=1 := by
      have hh : y i∈Metric.ball (1/2 : ℝ) b.rIn := by
        change |(x i-c i+1/2)-1/2|<(r+1/2)/2
        simp only [add_sub_cancel_right]
        exact (hx i).trans_lt (by linarith)
      exact (b.eventuallyEq_one_of_mem_ball hh).comp_tendsto
        (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.continuousAt
    have hb' : ∀ᶠ z in 𝓝 y,χ z=1 := by
      filter_upwards [Filter.eventually_all.mpr hb] with z hz
      dsimp [χ]
      simp_rw [hz]
      simp
    have he : P=ᶠ[𝓝 y](fun z => z-cubeCenter) := by
      filter_upwards [latticePeriodize_eventuallyEq hcomp hsO hy,hb'] with z hz hχz
      change latticePeriodize g z=_
      rw [hz]
      simp only [g,hχz,one_smul]
    have ht : Tendsto (fun z : Cover => z-c+cubeCenter) (𝓝 x) (𝓝 y) :=
      ((continuous_id.sub continuous_const).add continuous_const).continuousAt
    filter_upwards [he.comp_tendsto ht] with z hz
    simpa only [X,Function.comp_apply,add_sub_cancel_right] using hz

end CubicTorus

end
end

end OAI
