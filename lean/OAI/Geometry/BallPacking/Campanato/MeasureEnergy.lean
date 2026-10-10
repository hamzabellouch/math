import Mathlib
import OAI.Geometry.BallPacking.Energy.CircularEnergy

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

lemma integral_stdDot_variance {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (v : Phase n) :
    (∫ x, stdDot n (f x-v) (f x-v) ∂μ)=
      (∫ x, stdDot n (f x) (f x) ∂μ)-2*stdDot n (∫ x,f x ∂μ) v+
        μ.real univ*stdDot n v v := by
  have hi : Integrable (fun x => 2*stdDot n (f x) v) μ :=
    (((stdDot n).flip v).integrable_comp hf).const_mul 2
  have hsub : Integrable (fun x => stdDot n (f x) (f x)-2*stdDot n (f x) v) μ := he.sub hi
  have hint : (∫ x,stdDot n (f x) v ∂μ)=stdDot n (∫ x,f x ∂μ) v :=
    ((stdDot n).flip v).integral_comp_comm hf
  simp_rw [stdDot_sub_self]
  rw [integral_add hsub (integrable_const _),integral_sub he hi,integral_const_mul,
    hint,integral_const,smul_eq_mul]

lemma stdDot_integral_sq_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) :
    stdDot n (∫ x,f x ∂μ) (∫ x,f x ∂μ)≤μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ) := by
  let v : Phase n := (μ.real univ)⁻¹ • (∫ x,f x ∂μ)
  have hn : 0≤(∫ x,stdDot n (f x-v) (f x-v) ∂μ) :=
    integral_nonneg (fun x => stdDot_nonneg (f x-v))
  rw [integral_stdDot_variance hf he] at hn
  have hm := mul_nonneg hμ.le hn
  have hid : μ.real univ*((∫ x,stdDot n (f x) (f x) ∂μ)-
      2*stdDot n (∫ x,f x ∂μ) v+μ.real univ*stdDot n v v)=
      μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ)-stdDot n (∫ x,f x ∂μ) (∫ x,f x ∂μ) := by
    dsimp only [v]
    simp only [map_smul,smul_apply,smul_eq_mul]
    field_simp
    ring
  rw [hid] at hm
  linarith

lemma stdDot_average_sq_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) :
    stdDot n ((μ.real univ)⁻¹ • (∫ x,f x ∂μ)) ((μ.real univ)⁻¹ • (∫ x,f x ∂μ))≤
      (μ.real univ)⁻¹*(∫ x,stdDot n (f x) (f x) ∂μ) := by
  have hh := mul_le_mul_of_nonneg_left (stdDot_integral_sq_le hf he hμ) (sq_nonneg ((μ.real univ)⁻¹))
  simp only [map_smul,smul_apply,smul_eq_mul]
  have hid : ((μ.real univ)⁻¹)^2*(μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ))=
      (μ.real univ)⁻¹*(∫ x,stdDot n (f x) (f x) ∂μ) := by field_simp
  rw [hid] at hh
  nlinarith only [hh]

lemma norm_sq_le_stdDot (v : Phase n) : ‖v‖^2≤ stdDot n v v := by
  have hroot : ‖v‖≤Real.sqrt (stdDot n v v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (stdDot_nonneg v)).mpr
    have hle : (v i).re*(v i).re+(v i).im*(v i).im≤ stdDot n v v := by
      rw [stdDot_apply]
      exact Finset.single_le_sum (f := fun j : Fin n => (v j).re*(v j).re+(v j).im*(v j).im)
        (fun j _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Finset.mem_univ i)
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    exact hle
  nlinarith [Real.sq_sqrt (stdDot_nonneg v),norm_nonneg v,Real.sqrt_nonneg (stdDot n v v)]


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

def phaseAverage (μ : Measure X) (f : X → Phase n) : Phase n :=
  (μ.real univ)⁻¹ • (∫ x,f x ∂μ)

lemma integrable_stdDot_const_sub {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (v : Phase n) :
    Integrable (fun x => stdDot n (v-f x) (v-f x)) μ := by
  have hvf : Integrable (fun x => 2*stdDot n v (f x)) μ :=
    (((stdDot n) v).integrable_comp hf).const_mul 2
  have hi : Integrable (fun x => stdDot n v v-2*stdDot n v (f x)+stdDot n (f x) (f x)) μ :=
    ((integrable_const _).sub hvf).add he
  simpa only [stdDot_sub_self] using hi

lemma phaseAverage_const_sub {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ) (hμ : 0<μ.real univ) (v : Phase n) :
    phaseAverage μ (fun x => v-f x)=v-phaseAverage μ f := by
  rw [phaseAverage,integral_sub (integrable_const _) hf,integral_const,smul_sub,inv_smul_smul₀ hμ.ne']
  rfl

lemma phaseAverage_deviation_energy_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) (v : Phase n) :
    stdDot n (v-phaseAverage μ f) (v-phaseAverage μ f)≤
      (μ.real univ)⁻¹*(∫ x,stdDot n (v-f x) (v-f x) ∂μ) := by
  have hh := stdDot_average_sq_le ((integrable_const v).sub hf) (integrable_stdDot_const_sub hf he v) hμ
  change stdDot n (phaseAverage μ (fun x => v-f x)) (phaseAverage μ (fun x => v-f x))≤_ at hh
  rw [phaseAverage_const_sub hf hμ v] at hh
  exact hh


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma stdDot_sub_self_le (v w : Phase n) :
    stdDot n (v-w) (v-w)≤2*stdDot n v v+2*stdDot n w w := by
  simpa only [map_neg,neg_apply,neg_neg,sub_eq_add_neg] using stdDot_add_self_le v (-w)

lemma curve_pair_energy_le {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v) {a b s t : ℝ}
    (hs : s∈Icc a b) (ht : t∈Icc a b) :
    stdDot n (v s-v t) (v s-v t)≤4*(b-a)*
      (∫ r in a..b,stdDot n (deriv v r) (deriv v r)) := by
  have h1 := curve_chord_energy_le hv hs.1 hs.2
  have h2 := curve_chord_energy_le hv ht.1 ht.2
  have h3 := stdDot_sub_self_le (v s-v a) (v t-v a)
  rw [sub_sub_sub_cancel_right] at h3
  nlinarith only [h1,h2,h3]

lemma horizontal_curve_deriv {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (y x : ℝ) :
    deriv (fun s : ℝ => v (s,y)) x=fderiv ℝ v (x,y) (1,0) := by
  have hh := (hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  change HasDerivAt (fun s : ℝ => v (s,y)) _ x at hh
  exact hh.deriv

lemma vertical_curve_deriv {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (x y : ℝ) :
    deriv (fun s : ℝ => v (x,s)) y=fderiv ℝ v (x,y) (0,1) := by
  have hh := (hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  change HasDerivAt (fun s : ℝ => v (x,s)) _ y at hh
  exact hh.deriv

def horizontalEnergy (v : Plane → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ v z (1,0)) (fderiv ℝ v z (1,0))

def verticalEnergy (v : Plane → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ v z (0,1)) (fderiv ℝ v z (0,1))

lemma horizontalEnergy_continuous {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (horizontalEnergy v) := by
  have hh := (hv.fderiv_right (m := ∞) (by simp)).continuous.clm_apply (continuous_const (y := ((1,0):Plane)))
  exact ((stdDot n).continuous.comp hh).clm_apply hh

lemma verticalEnergy_continuous {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (verticalEnergy v) := by
  have hh := (hv.fderiv_right (m := ∞) (by simp)).continuous.clm_apply (continuous_const (y := ((0,1):Plane)))
  exact ((stdDot n).continuous.comp hh).clm_apply hh

lemma rectangle_pair_energy_bound {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} {p q : Plane} (hp : p∈(Icc a b) ×ˢ (Icc a b)) (hq : q∈(Icc a b) ×ˢ (Icc a b)) :
    stdDot n (v p-v q) (v p-v q)≤
      8*(b-a)*((∫ x in a..b,horizontalEnergy v (x,p.2))+
        (∫ y in a..b,verticalEnergy v (q.1,y))) := by
  have hx := curve_pair_energy_le (v := fun x => v (x,p.2)) (hv.comp (contDiff_id.prodMk (contDiff_const (c := p.2)))) hp.1 hq.1
  have hy := curve_pair_energy_le (v := fun y => v (q.1,y)) (hv.comp ((contDiff_const (c := q.1)).prodMk contDiff_id)) hp.2 hq.2
  change stdDot n (v (p.1,p.2)-v (q.1,p.2)) (v (p.1,p.2)-v (q.1,p.2))≤_ at hx
  change stdDot n (v (q.1,p.2)-v (q.1,q.2)) (v (q.1,p.2)-v (q.1,q.2))≤_ at hy
  simp only [horizontal_curve_deriv hv] at hx
  simp only [vertical_curve_deriv hv] at hy
  have hh := stdDot_add_self_le (v p-v (q.1,p.2)) (v (q.1,p.2)-v q)
  rw [sub_add_sub_cancel] at hh
  change stdDot n (v p-v (q.1,p.2)) (v p-v (q.1,p.2))≤
    4*(b-a)*(∫ x in a..b,horizontalEnergy v (x,p.2)) at hx
  change stdDot n (v (q.1,p.2)-v q) (v (q.1,p.2)-v q)≤
    4*(b-a)*(∫ y in a..b,verticalEnergy v (q.1,y)) at hy
  nlinarith only [hx,hy,hh]


def squareMeasure (a b : ℝ) : Measure Plane :=
  (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))

lemma squareMeasure_eq (a b : ℝ) :
    squareMeasure a b=volume.restrict ((Icc a b) ×ˢ (Icc a b)) := by
  rw [squareMeasure,Measure.prod_restrict,←Measure.volume_eq_prod]

instance squareMeasure_finite (a b : ℝ) : IsFiniteMeasure (squareMeasure a b) := by
  unfold squareMeasure
  infer_instance

lemma squareMeasure_mass {a b : ℝ} (hab : a≤b) :
    (squareMeasure a b).real univ=(b-a)^2 := by
  rw [squareMeasure,Measure.real,←univ_prod_univ,Measure.prod_prod]
  simp [Real.volume_Icc,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),pow_two]

lemma intervalMeasure_mass {a b : ℝ} (hab : a≤b) :
    (volume.restrict (Icc a b)).real univ=b-a := by
  simp [Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma continuous_square_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Continuous f) (a b : ℝ) : Integrable f (squareMeasure a b) := by
  rw [squareMeasure_eq]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma square_ae_mem (a b : ℝ) : ∀ᵐ z ∂squareMeasure a b,z∈(Icc a b) ×ˢ (Icc a b) := by
  rw [squareMeasure_eq]
  exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)

lemma square_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f : Plane → E} (hf : Integrable f (squareMeasure a b)) :
    (∫ z,f z ∂squareMeasure a b)=∫ x in Icc a b,∫ y in Icc a b,f (x,y) :=
  integral_prod f hf

lemma square_integral_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f : Plane → E} (hf : Integrable f (squareMeasure a b)) :
    (∫ z,f z ∂squareMeasure a b)=∫ y in Icc a b,∫ x in Icc a b,f (x,y) :=
  integral_prod_symm f hf

lemma integral_Icc_eq_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a≤b) :
    (∫ x in Icc a b,f x)=∫ x in a..b,f x := by
  rw [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc]


def horizontalSlice (v : Plane → Phase n) (a b y : ℝ) : ℝ :=
  ∫ x in Icc a b,horizontalEnergy v (x,y)
def verticalSlice (v : Plane → Phase n) (a b x : ℝ) : ℝ :=
  ∫ y in Icc a b,verticalEnergy v (x,y)

lemma horizontalSlice_integrable {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    Integrable (horizontalSlice v a b) (volume.restrict (Icc a b)) :=
  (continuous_square_integrable (horizontalEnergy_continuous hv) a b).integral_prod_right

lemma verticalSlice_integrable {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    Integrable (verticalSlice v a b) (volume.restrict (Icc a b)) :=
  (continuous_square_integrable (verticalEnergy_continuous hv) a b).integral_prod_left

lemma square_point_deviation_bound {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a<b) {p : Plane} (hp : p∈(Icc a b) ×ˢ (Icc a b)) :
    stdDot n (v p-phaseAverage (squareMeasure a b) v) (v p-phaseAverage (squareMeasure a b) v)≤
      8*(b-a)*horizontalSlice v a b p.2+8*(∫ z,verticalEnergy v z ∂squareMeasure a b) := by
  have hvi := continuous_square_integrable hv.continuous a b
  have hve := continuous_square_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) a b
  have hm : 0<(squareMeasure a b).real univ := by rw [squareMeasure_mass hab.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (v p)
  have hvsi : Integrable (fun q : Plane => verticalSlice v a b q.1) (squareMeasure a b) :=
    (verticalSlice_integrable hv a b).comp_fst _
  have hright : Integrable (fun q : Plane => 8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1))
      (squareMeasure a b) :=
    ((integrable_const _).add hvsi).const_mul _
  have hcomp : (∫ q,stdDot n (v p-v q) (v p-v q) ∂squareMeasure a b)≤
      ∫ q,8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1) ∂squareMeasure a b := by
    apply integral_mono_ae (integrable_stdDot_const_sub hvi hve (v p)) hright
    filter_upwards [square_ae_mem a b] with q hq
    have hh := rectangle_pair_energy_bound hv hp hq
    simpa only [horizontalSlice,verticalSlice,integral_Icc_eq_interval hab.le] using hh
  have hmass := intervalMeasure_mass hab.le
  have hfub := square_integral (continuous_square_integrable (verticalEnergy_continuous hv) a b)
  have hrightVal : (∫ q,8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1) ∂squareMeasure a b)=
      8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
        (b-a)*(∫ z,verticalEnergy v z ∂squareMeasure a b)) := by
    rw [integral_const_mul,integral_add (integrable_const _) hvsi,
      integral_const,squareMeasure_mass hab.le]
    change 8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
      (∫ q,verticalSlice v a b q.1 ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))))=_
    rw [integral_fun_fst,hmass]
    rw [hfub]
    rfl
  rw [hrightVal] at hcomp
  have hh := hj.trans (mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hm.le))
  rw [squareMeasure_mass hab.le] at hh
  have hid : ((b-a)^2)⁻¹*(8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
      (b-a)*(∫ z,verticalEnergy v z ∂squareMeasure a b)))=
      8*(b-a)*horizontalSlice v a b p.2+8*(∫ z,verticalEnergy v z ∂squareMeasure a b) := by
    field_simp [(sub_pos.mpr hab).ne']
  rwa [hid] at hh

lemma square_poincare {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a<b) :
    (∫ z,stdDot n (v z-phaseAverage (squareMeasure a b) v) (v z-phaseAverage (squareMeasure a b) v)
      ∂squareMeasure a b)≤
      8*(b-a)^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
  have hleft : Integrable (fun z => stdDot n (v z-phaseAverage (squareMeasure a b) v)
      (v z-phaseAverage (squareMeasure a b) v)) (squareMeasure a b) := continuous_square_integrable
    (((stdDot n).continuous.comp (hv.continuous.sub continuous_const)).clm_apply
      (hv.continuous.sub continuous_const)) a b
  have hxsi : Integrable (fun p : Plane => horizontalSlice v a b p.2) (squareMeasure a b) :=
    (horizontalSlice_integrable hv a b).comp_snd _
  have hright : Integrable (fun p : Plane => 8*(b-a)*horizontalSlice v a b p.2+
      8*(∫ z,verticalEnergy v z ∂squareMeasure a b)) (squareMeasure a b) :=
    (hxsi.const_mul _).add (integrable_const _)
  have hcomp := integral_mono_ae hleft hright (by
    filter_upwards [square_ae_mem a b] with p hp
    exact square_point_deviation_bound hv hab hp)
  have hx := continuous_square_integrable (horizontalEnergy_continuous hv) a b
  have hy := continuous_square_integrable (verticalEnergy_continuous hv) a b
  have hfub := square_integral_swap hx
  rw [integral_add (hxsi.const_mul _) (integrable_const _)] at hcomp
  rw [integral_const_mul,integral_const] at hcomp
  change _≤8*(b-a)*(∫ p,horizontalSlice v a b p.2 ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b)))+
    (squareMeasure a b).real univ*(8*(∫ z,verticalEnergy v z ∂squareMeasure a b)) at hcomp
  rw [integral_fun_snd,intervalMeasure_mass hab.le,squareMeasure_mass hab.le] at hcomp
  change _≤8*(b-a)*((b-a)*(∫ y in Icc a b,∫ x in Icc a b,horizontalEnergy v (x,y)))+_ at hcomp
  rw [←hfub] at hcomp
  rw [integral_add hx hy]
  nlinarith only [hcomp]


lemma stdDot_sub_swap (v w : Phase n) : stdDot n (v-w) (v-w)=stdDot n (w-v) (w-v) := by
  have h : w-v=-(v-w) := by abel
  rw [h]
  simp only [map_neg,neg_apply,neg_neg]

lemma square_energy_mono {f : Plane → ℝ} (hf : Continuous f) (hn : ∀ z,0≤f z)
    {a b c d : ℝ} (hac : a≤c) (hdb : d≤b) :
    (∫ z,f z ∂squareMeasure c d)≤∫ z,f z ∂squareMeasure a b := by
  simp only [squareMeasure_eq]
  apply setIntegral_mono_set (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (Eventually.of_forall hn)
  exact Eventually.of_forall (fun z hz =>
    ⟨⟨hac.trans hz.1.1,hz.1.2.trans hdb⟩,⟨hac.trans hz.2.1,hz.2.2.trans hdb⟩⟩)

lemma square_means_energy {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b c d : ℝ} (hab : a<b) (hcd : c<d) (hac : a≤c) (hdb : d≤b) :
    stdDot n (phaseAverage (squareMeasure a b) v-phaseAverage (squareMeasure c d) v)
      (phaseAverage (squareMeasure a b) v-phaseAverage (squareMeasure c d) v)≤
      ((d-c)^2)⁻¹*(8*(b-a)^2)*
        (∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
  have hvi := continuous_square_integrable hv.continuous c d
  have hve := continuous_square_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) c d
  have hm : 0<(squareMeasure c d).real univ := by rw [squareMeasure_mass hcd.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (phaseAverage (squareMeasure a b) v)
  rw [squareMeasure_mass hcd.le] at hj
  have hm' : 0≤((d-c)^2)⁻¹ := by positivity
  have hmono := square_energy_mono
    (((stdDot n).continuous.comp (continuous_const.sub hv.continuous)).clm_apply
      (continuous_const.sub hv.continuous))
    (fun z => stdDot_nonneg (phaseAverage (squareMeasure a b) v-v z)) hac hdb
  have hs : (∫ z,stdDot n (phaseAverage (squareMeasure a b) v-v z)
      (phaseAverage (squareMeasure a b) v-v z) ∂squareMeasure a b)≤
      8*(b-a)^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
    simp_rw [stdDot_sub_swap (phaseAverage (squareMeasure a b) v)]
    exact square_poincare hv hab
  have hh := hj.trans (mul_le_mul_of_nonneg_left (hmono.trans hs) hm')
  simpa only [mul_assoc] using hh

lemma quarter_square_mean_norm {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {r : ℝ} (hr : 0<r) :
    ‖phaseAverage (squareMeasure (-r) r) v-phaseAverage (squareMeasure (-(r/4)) (r/4)) v‖^2≤
      128*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-r) r) := by
  have hh := square_means_energy hv (a := -r) (b := r) (c := -(r/4)) (d := r/4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hid : ((r/4-(-(r/4)))^2)⁻¹*(8*(r-(-r))^2)=(128:ℝ) := by
    field_simp [hr.ne']
    ring
  rw [hid] at hh
  exact (norm_sq_le_stdDot _).trans hh

lemma square_dirichlet_le_radial {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {r A : ℝ} (hr : 0≤r) (hA : 0<A) (hrA : 2*r^2≤A) :
    (∫ z,horizontalEnergy (realCurve u) z+verticalEnergy (realCurve u) z ∂squareMeasure (-r) r)≤
      radialCurveEnergy u A := by
  change (∫ z,dirichletEnergy u z ∂squareMeasure (-r) r)≤_
  rw [squareMeasure_eq]
  have heq : (∫ z in (Icc (-r) r) ×ˢ (Icc (-r) r),dirichletEnergy u z)=
      ∫ z in (Icc (-r) r) ×ˢ (Icc (-r) r),sourceRadialCutoff A z*dirichletEnergy u z := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro z hz
    have h1 : z.1^2≤r^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg z.1) hr).mpr (abs_le.mpr hz.1)
    have h2 : z.2^2≤r^2 := sq_le_sq' hz.2.1 hz.2.2
    have hrad : radiusSq z≤A := by dsimp [radiusSq]; nlinarith
    change dirichletEnergy u z=sourceRadialCutoff A z*dirichletEnergy u z
    rw [show sourceRadialCutoff A z=1 from
      outerProfile_one_before (radiusSq_nonneg z) hrad hA,one_mul]
  rw [heq]
  exact setIntegral_le_integral (smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu))
    (Eventually.of_forall (fun z => mul_nonneg (sourceRadialCutoff_nonneg A z) (dirichletEnergy_nonneg u z)))


lemma phaseAverage_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hμ : 0<μ.real univ) {C : ℝ} (hf : ∀ᵐ x ∂μ,‖f x‖≤C) :
    ‖phaseAverage μ f‖≤C := by
  rw [phaseAverage,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hμ.le)]
  have hh := mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hf) (inv_nonneg.mpr hμ.le)
  have hid : (μ.real univ)⁻¹*(C*μ.real univ)=C := by field_simp
  rwa [hid] at hh

lemma plane_norm_le_square {r : ℝ} {z : Plane} (hz : z∈(Icc (-r) r) ×ˢ (Icc (-r) r)) : ‖z‖≤r := by
  rw [Prod.norm_def]
  exact max_le (abs_le.mpr hz.1) (abs_le.mpr hz.2)

lemma squareAverage_tendsto {v : Plane → Phase n} (hv : Continuous v)
    {r : ℕ → ℝ} (hr : ∀ k,0<r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => phaseAverage (squareMeasure (-(r k)) (r k)) v) atTop (𝓝 (v 0)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδv⟩ := Metric.continuousAt_iff.mp hv.continuousAt (ε/2) (by positivity)
  have hev : ∀ᶠ k in atTop,r k<δ := hr0.eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,?_⟩
  intro k hk
  have hm : 0<(squareMeasure (-(r k)) (r k)).real univ := by
    rw [squareMeasure_mass (by linarith [hr k])]
    exact sq_pos_of_pos (by linarith [hr k])
  have hb : ∀ᵐ z ∂squareMeasure (-(r k)) (r k),‖v 0-v z‖≤ε/2 := by
    filter_upwards [square_ae_mem (-(r k)) (r k)] with z hz
    have hzδ : dist z 0<δ := by simpa only [dist_zero_right] using (plane_norm_le_square hz).trans_lt (hN k hk)
    have hh := hδv hzδ
    simpa only [dist_eq_norm,norm_sub_rev] using hh.le
  have hh := phaseAverage_norm_le hm hb
  rw [phaseAverage_const_sub (continuous_square_integrable hv _ _) hm] at hh
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt (by linarith)


def campRadius (k : ℕ) : ℝ := (1/2)*(1/4)^k

lemma campRadius_pos (k : ℕ) : 0<campRadius k := by unfold campRadius; positivity

lemma campRadius_succ (k : ℕ) : campRadius (k+1)=campRadius k/4 := by
  unfold campRadius
  rw [pow_succ]
  ring

lemma campRadius_sq (k : ℕ) : 2*(campRadius k)^2≤(1/16)^k := by
  unfold campRadius
  have hid : ((1/4:ℝ)^k)^2=(1/16:ℝ)^k := by
    rw [←pow_mul,Nat.mul_comm k 2,pow_mul]
    norm_num
  rw [mul_pow,hid]
  have hh : 0≤(1/16:ℝ)^k := by positivity
  nlinarith

lemma campRadius_tendsto : Tendsto campRadius atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (1/2:ℝ)*(1/4)^k) atTop (𝓝 0)
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).const_mul (1/2:ℝ)
  simpa only [campRadius,mul_zero] using hh

lemma geometric_sqrt_norm_bound {v : Phase n} {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (k : ℕ)
    (hv : ‖v‖^2≤128*B*θ^k) : ‖v‖≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by
  have hc : 0≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hc).mp
  have hid : (Real.sqrt (128*B)*(Real.sqrt θ)^k)^2=128*B*θ^k := by
    rw [mul_pow,Real.sq_sqrt (by positivity),←pow_mul,Nat.mul_comm k 2,pow_mul,Real.sq_sqrt hθ]
  rwa [hid]

lemma campanato_point_mean {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ k : ℕ,radialCurveEnergy u ((1/16)^k)≤B*θ^k) (k : ℕ) :
    ‖phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)-u 0‖≤
      Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  let f : ℕ → Phase n := fun j => phaseAverage (squareMeasure (-(campRadius j)) (campRadius j)) (realCurve u)
  have hf : Tendsto f atTop (𝓝 (u 0)) := by
    have hh := squareAverage_tendsto (realCurve_smooth hu).continuous campRadius_pos campRadius_tendsto
    simpa only [f,realCurve,Function.comp_apply,map_zero] using hh
  have hs (j : ℕ) : dist (f j) (f (j+1))≤Real.sqrt (128*B)*(Real.sqrt θ)^j := by
    rw [dist_eq_norm]
    apply geometric_sqrt_norm_bound hB hθ j
    have hq := quarter_square_mean_norm (realCurve_smooth hu) (campRadius_pos j)
    have hr := square_dirichlet_le_radial hu (campRadius_pos j).le
      (by positivity : (0:ℝ)<(1/16)^j) (campRadius_sq j)
    change ‖phaseAverage (squareMeasure (-(campRadius j)) (campRadius j)) (realCurve u)-
      phaseAverage (squareMeasure (-(campRadius (j+1))) (campRadius (j+1))) (realCurve u)‖^2≤_
    rw [campRadius_succ]
    exact hq.trans ((mul_le_mul_of_nonneg_left (hr.trans (he j)) (by norm_num)).trans_eq (by ring))
  have hsqrt : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  simpa only [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto (Real.sqrt θ) (Real.sqrt (128*B)) hsqrt hs hf k



end HigherDimensionalBallPacking.Rigidity
end

end OAI
