import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeVolterraKernel

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelSeries
open MeasureTheory Set Filter VolterraKernel VolterraBounds
open scoped Topology
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [SFinite μ]

lemma integrable_tsum_bound (F : ℕ → X → B) (a : ℕ → ℝ)
    (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n)
    (hF : ∀ n, StronglyMeasurable (F n))
    (hFi : ∀ n, Integrable (F n) μ)
    (hFa : ∀ n, (∫ x, ‖F n x‖ ∂μ) ≤ a n)
    (hFs : ∀ x, Summable (fun n => ‖F n x‖)) :
    Integrable (fun x => ∑' n, F n x) μ ∧
    (∫ x, ‖∑' n, F n x‖ ∂μ) ≤ ∑' n, a n := by
  have hai : Integrable a Measure.count := integrable_count_iff.mpr (by
    simpa only [Real.norm_of_nonneg (ha0 _)] using ha)
  have hm : StronglyMeasurable (Function.uncurry F) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun _ => continuous_of_discreteTopology) hF
  have hb := SchurIntegration.integral_row_bound Measure.count μ hai F hm hFi hFa
  have he (x : X) : (∫ n, F n x ∂Measure.count) = ∑' n, F n x := by
    rw [integral_countable (integrable_count_iff.mpr (hFs x))]
    simp
  have hea : (∫ n, a n ∂Measure.count) = ∑' n, a n := by
    rw [integral_countable hai]
    simp
  simpa only [he, hea] using hb.2

omit [NormedAlgebra ℝ B] [CompleteSpace B] in

lemma tsum_stronglyMeasurable (F : ℕ → X → B)
    (hF : ∀ n, StronglyMeasurable (F n)) (hs : ∀ x, Summable (fun n => F n x)) :
    StronglyMeasurable (fun x => ∑' n, F n x) := by
  refine stronglyMeasurable_of_tendsto (f := fun n : ℕ => fun x => ∑ i ∈ Finset.range n, F i x)
    atTop (fun n => ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum (Finset.range n) (fun i _ => hF i)
  · exact tendsto_pi_nhds.mpr (fun x => (hs x).hasSum.tendsto_sum_nat)

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

def clip (T : ℝ) (K : Kernel (X := X) (B := B)) : Kernel (X := X) (B := B) :=
  fun t x y => if t ∈ Ioc 0 T then K t x y else 0

omit [NormedAlgebra ℝ B] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma clip_measurable (T : ℝ) (K : Kernel (X := X) (B := B)) (hK : MeasurableKernel K) :
    MeasurableKernel (clip T K) := by
  exact hK.piecewise (measurableSet_Ioc.preimage measurable_fst) stronglyMeasurable_const

omit [MeasurableSpace X] [NormedAlgebra ℝ B] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
@[simp] lemma clip_of_mem (T : ℝ) (K : Kernel (X := X) (B := B)) {t : ℝ}
    (ht : t ∈ Ioc 0 T) (x y : X) : clip T K t x y = K t x y := ite_eq_left ht

omit [MeasurableSpace X] [NormedAlgebra ℝ B] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
@[simp] lemma clip_of_not_mem (T : ℝ) (K : Kernel (X := X) (B := B)) {t : ℝ}
    (ht : t ∉ Ioc 0 T) (x y : X) : clip T K t x y = 0 := ite_eq_right ht

omit [SFinite μ] [CompleteSpace B] [NormedAlgebra ℝ B] [BorelSpace X] [SecondCountableTopology X] in
lemma heatBound_clip (N : ℕ) {T A : ℝ} (K : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) : HeatBound μ N T A (clip T K) := by
  refine ⟨clip_measurable T K hK.measurable, hK.nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x y; simpa only [clip_of_mem T K ht] using hK.sup t ht x y
  · intro t ht x; simpa only [clip_of_mem T K ht] using hK.row_int t ht x
  · intro t ht x; simpa only [clip_of_mem T K ht] using hK.row t ht x
  · intro t ht y; simpa only [clip_of_mem T K ht] using hK.col_int t ht y
  · intro t ht y; simpa only [clip_of_mem T K ht] using hK.col t ht y

omit [NormedAlgebra ℝ B] [CompleteSpace B] [SFinite μ] [BorelSpace X] [SecondCountableTopology X] in
lemma heatBound_neg (N : ℕ) {T A : ℝ} (K : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) : HeatBound μ N T A (fun t x y => - K t x y) := by
  exact ⟨hK.measurable.neg, hK.nonneg, by simpa only [norm_neg] using hK.sup,
    by simpa only [norm_neg] using hK.row_int, by simpa only [norm_neg] using hK.row,
    by simpa only [norm_neg] using hK.col_int, by simpa only [norm_neg] using hK.col⟩

def term (T : ℝ) (R : Kernel (X := X) (B := B)) : ℕ → Kernel (X := X) (B := B)
  | 0 => clip T (fun t x y => -R t x y)
  | n+1 => clip T (fun t x y => -convolution μ R (term T R n) t x y)

omit [CompleteSpace B] in
lemma term_heatBound (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R) (n : ℕ) :
    HeatBound μ N T (A*(4*T*A)^n) (term μ T R n) := by
  induction n with
  | zero => simpa only [term, pow_zero, mul_one] using
      heatBound_clip μ N _ (heatBound_neg μ N R hR)
  | succ n ih =>
    have h := heatBound_clip μ N _ (heatBound_neg μ N _
      (convolution_heatBound μ N hT R (term μ T R n) hR ih))
    convert h using 1
    · rw [pow_succ]; ring
    · rfl

omit [SFinite μ] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
@[simp] lemma term_outside (T : ℝ) (R : Kernel (X := X) (B := B))
    (n : ℕ) {t : ℝ} (ht : t ∉ Ioc 0 T) (x y : X) : term μ T R n t x y = 0 := by
  cases n <;> simp only [term, clip_of_not_mem T _ ht]

omit [CompleteSpace B] in
lemma term_norm_summable (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R)
    (hq : 4*T*A < 1) (t : ℝ) (x y : X) :
    Summable (fun n => ‖term μ T R n t x y‖) := by
  by_cases ht : t ∈ Ioc 0 T
  · have hq0 : 0 ≤ 4*T*A := by have hA := hR.nonneg; positivity
    have hs : Summable (fun n : ℕ => (A/t^2)*(4*T*A)^n) :=
      (summable_geometric_of_norm_lt_one (x := (4*T*A : ℝ)) (by rwa [Real.norm_of_nonneg hq0])).mul_left _
    apply hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    have hn := (term_heatBound μ N hT R hR n).sup t ht x y
    calc
      _ ≤ weight N t x y*‖term μ T R n t x y‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (weight_one_le N ht.1 x y)
      _ ≤ A*(4*T*A)^n/t^2 := hn
      _ = _ := by ring
  · simp only [term_outside μ T R _ ht, norm_zero, summable_zero]

omit [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma weighted_tsum_L1 (w : X → ℝ) (hw : StronglyMeasurable w) (hw0 : ∀ x, 0 ≤ w x)
    (F : ℕ → X → B) (a : ℕ → ℝ) (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n)
    (hF : ∀ n, StronglyMeasurable (F n))
    (hFi : ∀ n, Integrable (fun x => w x*‖F n x‖) μ)
    (hFa : ∀ n, (∫ x, w x*‖F n x‖ ∂μ) ≤ a n)
    (hFs : ∀ x, Summable (fun n => ‖F n x‖)) :
    Integrable (fun x => w x*‖∑' n, F n x‖) μ ∧
    (∫ x, w x*‖∑' n, F n x‖ ∂μ) ≤ ∑' n, a n := by
  have hn (n : ℕ) (x : X) : ‖w x • F n x‖ = w x*‖F n x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  have hs (x : X) : Summable (fun n => ‖w x • F n x‖) := by
    simpa only [hn] using (hFs x).mul_left (w x)
  have hi (n : ℕ) : Integrable (fun x => w x • F n x) μ :=
    (integrable_norm_iff (hw.smul (hF n)).aestronglyMeasurable).mp (by
      change Integrable (fun x => ‖w x • F n x‖) μ
      simpa only [hn] using hFi n)
  have hb := integrable_tsum_bound μ (fun n x => w x • F n x) a ha ha0
    (fun n => hw.smul (hF n)) hi (by simpa only [hn] using hFa) hs
  have he (x : X) : (∑' n, w x • F n x) = w x • ∑' n, F n x :=
    (hFs x).of_norm.tsum_const_smul _
  have hn' (x : X) : ‖w x • ∑' n, F n x‖ = w x*‖∑' n, F n x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  exact ⟨by simpa only [he, hn'] using hb.1.norm,
    by simpa only [he, hn'] using hb.2⟩

omit [SecondCountableTopology X] in
lemma heatBound_tsum (N : ℕ) {T : ℝ} (K : ℕ → Kernel (X := X) (B := B))
    (a : ℕ → ℝ) (ha : Summable a) (hK : ∀ n, HeatBound μ N T (a n) (K n))
    (hKs : ∀ t x y, Summable (fun n => ‖K n t x y‖)) :
    HeatBound μ N T (∑' n, a n) (fun t x y => ∑' n, K n t x y) := by
  have hm : MeasurableKernel (fun t x y => ∑' n, K n t x y) :=
    tsum_stronglyMeasurable (fun n (p : ℝ × X × X) => K n p.1 p.2.1 p.2.2)
      (fun n => (hK n).measurable) (fun p => (hKs _ _ _).of_norm)
  have hr (t : ℝ) (ht : t ∈ Ioc 0 T) (x : X) :
      Integrable (fun y => weight N t x y*‖∑' n, K n t x y‖) μ ∧
      (∫ y, weight N t x y*‖∑' n, K n t x y‖ ∂μ) ≤ ∑' n, a n := by
    exact weighted_tsum_L1 μ _ (weight_continuous N t x).stronglyMeasurable
      (fun y => (weight_pos N ht.1 x y).le) (fun n y => K n t x y) a ha
      (fun n => (hK n).nonneg)
      (fun n => (kernel_section (K n) (hK n).measurable t).comp_measurable
        (measurable_const.prodMk measurable_id))
      (fun n => (hK n).row_int t ht x) (fun n => (hK n).row t ht x) (hKs t x)
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) (y : X) :
      Integrable (fun x => weight N t x y*‖∑' n, K n t x y‖) μ ∧
      (∫ x, weight N t x y*‖∑' n, K n t x y‖ ∂μ) ≤ ∑' n, a n := by
    have hw : StronglyMeasurable (fun x => weight N t x y) := by
      simpa only [weight_symm N t] using (weight_continuous N t y).stronglyMeasurable
    exact weighted_tsum_L1 μ _ hw
      (fun x => (weight_pos N ht.1 x y).le) (fun n x => K n t x y) a ha
      (fun n => (hK n).nonneg)
      (fun n => (kernel_section (K n) (hK n).measurable t).comp_measurable
        (measurable_id.prodMk measurable_const))
      (fun n => (hK n).col_int t ht y) (fun n => (hK n).col t ht y) (fun x => hKs t x y)
  refine ⟨hm, tsum_nonneg (fun n => (hK n).nonneg), ?_,
    fun t ht x => (hr t ht x).1, fun t ht x => (hr t ht x).2,
    fun t ht y => (hc t ht y).1, fun t ht y => (hc t ht y).2⟩
  intro t ht x y
  have hn (n : ℕ) : ‖weight N t x y • K n t x y‖ ≤ a n/t^2 := by
    simpa only [norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le] using
      (hK n).sup t ht x y
  have hh := tsum_of_norm_bounded (ha.div_const (t^2)).hasSum hn
  rw [(hKs t x y).of_norm.tsum_const_smul, norm_smul,
    Real.norm_of_nonneg (weight_pos N ht.1 x y).le, tsum_div_const] at hh
  exact hh

def correction (T : ℝ) (R : Kernel (X := X) (B := B)) : Kernel (X := X) (B := B) :=
  fun t x y => ∑' n, term μ T R n t x y

lemma correction_heatBound (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R) (hq : 4*T*A < 1) :
    HeatBound μ N T (A/(1-4*T*A)) (correction μ T R) := by
  have hq0 : 0 ≤ 4*T*A := by have hA := hR.nonneg; positivity
  have hqabs : ‖(4*T*A : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg hq0]
  have ha : Summable (fun n : ℕ => A*(4*T*A)^n) :=
    (summable_geometric_of_norm_lt_one hqabs).mul_left A
  have h := heatBound_tsum μ N (term μ T R) _ ha
    (term_heatBound μ N hT R hR) (term_norm_summable μ N hT R hR hq)
  have he : (∑' n : ℕ, A*(4*T*A)^n) = A/(1-4*T*A) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqabs, div_eq_mul_inv]
  change HeatBound μ N T (A/(1-4*T*A)) (fun t x y => ∑' n, term μ T R n t x y)
  rw [he] at h
  exact h

omit [NormedAlgebra ℝ B] [CompleteSpace B] [SFinite μ]
  [BorelSpace X] [SecondCountableTopology X] in
lemma heatBound_norm (N : ℕ) {T A : ℝ} (K : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) : HeatBound μ N T A (fun t x y => ‖K t x y‖) := by
  exact ⟨hK.measurable.norm, hK.nonneg, by simpa only [norm_norm] using hK.sup,
    by simpa only [norm_norm] using hK.row_int, by simpa only [norm_norm] using hK.row,
    by simpa only [norm_norm] using hK.col_int, by simpa only [norm_norm] using hK.col⟩

omit [CompleteSpace B] [SFinite μ] [BorelSpace X] [SecondCountableTopology X] in
lemma spatial_product_norm_bound (N : ℕ) {T A C : ℝ}
    (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (x y : X) :
    Integrable (fun z => K (t-s) x z * L s z y) μ ∧
    (∫ z, ‖K (t-s) x z * L s z y‖ ∂μ) ≤ 4*A*C/t^2 := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  have hi := time_integrand_bound μ N ht.1 hs.1 hs.2 hK.nonneg hL.nonneg K L x y
    (hK.sup _ ha x) (fun z => hL.sup _ hb z y) (hK.row_int _ ha x)
    (hL.col_int _ hb y) (hK.row _ ha x) (hL.col _ hb y)
    (product_section K L hK.measurable hL.measurable t s x y).aestronglyMeasurable
  have hKn := heatBound_norm μ N K hK
  have hLn := heatBound_norm μ N L hL
  have hn := time_integrand_bound μ N ht.1 hs.1 hs.2 hK.nonneg hL.nonneg
    (fun t x y => ‖K t x y‖) (fun t x y => ‖L t x y‖) x y
    (hKn.sup _ ha x) (fun z => hLn.sup _ hb z y) (hKn.row_int _ ha x)
    (hLn.col_int _ hb y) (hKn.row _ ha x) (hLn.col _ hb y)
    (product_section _ _ hKn.measurable hLn.measurable t s x y).aestronglyMeasurable
  refine ⟨hi.1, ?_⟩
  calc
    _ ≤ ∫ z, ‖K (t-s) x z‖ * ‖L s z y‖ ∂μ := integral_mono hi.1.norm hn.1
      (fun z => norm_mul_le _ _)
    _ ≤ weight N t x y * (∫ z, ‖K (t-s) x z‖ * ‖L s z y‖ ∂μ) :=
      le_mul_of_one_le_left (integral_nonneg (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (weight_one_le N ht.1 x y)
    _ ≤ 4*A*C/t^2 := by
      simpa only [Real.norm_of_nonneg (integral_nonneg
        (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)))] using hn.2

omit [SFinite μ] [BorelSpace X] [SecondCountableTopology X] in
lemma spatial_tsum_right (N : ℕ) {T A : ℝ}
    (K : Kernel (X := X) (B := B)) (L : ℕ → Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (a : ℕ → ℝ) (ha : Summable a)
    (hL : ∀ n, HeatBound μ N T (a n) (L n))
    (hLs : ∀ t x y, Summable (fun n => ‖L n t x y‖))
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (x y : X) :
    spatial μ K (fun t x y => ∑' n, L n t x y) t s x y =
      ∑' n, spatial μ K (L n) t s x y := by
  have hi (n : ℕ) := spatial_product_norm_bound μ N K (L n) hK (hL n) ht hs x y
  have ha' : Summable (fun n => 4*A*a n/t^2) := by
    convert ha.mul_left (4*A/t^2) using 1
    ext n
    ring
  have hsum : Summable (fun n => ∫ z, ‖K (t-s) x z * L n s z y‖ ∂μ) :=
    ha'.of_nonneg_of_le (fun n => integral_nonneg (fun z => norm_nonneg _)) (fun n => (hi n).2)
  unfold spatial
  rw [integral_tsum_of_summable_integral_norm (fun n => (hi n).1) hsum]
  apply integral_congr_ae
  filter_upwards [] with z
  exact ((hLs s z y).of_norm.tsum_mul_left (K (t-s) x z)).symm

omit [BorelSpace X] [SecondCountableTopology X] in
lemma convolution_tsum_right (N : ℕ) {T A : ℝ}
    (K : Kernel (X := X) (B := B)) (L : ℕ → Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (a : ℕ → ℝ) (ha : Summable a)
    (hL : ∀ n, HeatBound μ N T (a n) (L n))
    (hLs : ∀ t x y, Summable (fun n => ‖L n t x y‖))
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    convolution μ K (fun t x y => ∑' n, L n t x y) t x y =
      ∑' n, convolution μ K (L n) t x y := by
  have hi (n : ℕ) := (convolution_sup μ N K (L n) hK (hL n) ht x y).1
  have hb (n : ℕ) : (∫ s in Ioo 0 t, ‖spatial μ K (L n) t s x y‖) ≤ 4*A*a n/t := by
    have hc : IntegrableOn (fun _ : ℝ => 4*A*a n/t^2) (Ioo 0 t) :=
      integrableOn_const (hs := measure_Ioo_lt_top.ne)
    have hp : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ‖spatial μ K (L n) t s x y‖ ≤ 4*A*a n/t^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (norm_integral_le_integral_norm _).trans
        (spatial_product_norm_bound μ N K (L n) hK (hL n) ht hs x y).2
    apply (integral_mono_ae (hi n).norm hc hp).trans_eq
    simp only [integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul]
    field_simp
  have ha' : Summable (fun n => 4*A*a n/t) := by
    convert ha.mul_left (4*A/t) using 1
    ext n
    ring
  have hsum : Summable (fun n => ∫ s in Ioo 0 t, ‖spatial μ K (L n) t s x y‖) :=
    ha'.of_nonneg_of_le (fun n => integral_nonneg (fun s => norm_nonneg _)) hb
  unfold VolterraKernel.convolution
  rw [integral_tsum_of_summable_integral_norm hi hsum]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact spatial_tsum_right μ N K L hK a ha hL hLs ht hs x y

lemma correction_equation (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R) (hq : 4*T*A < 1)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    R t x y + correction μ T R t x y + convolution μ R (correction μ T R) t x y = 0 := by
  have hq0 : 0 ≤ 4*T*A := by have hA := hR.nonneg; positivity
  have ha : Summable (fun n : ℕ => A*(4*T*A)^n) :=
    (summable_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hq0] : ‖(4*T*A:ℝ)‖ < 1)).mul_left A
  have hs := term_norm_summable μ N hT R hR hq t x y
  have he := convolution_tsum_right μ N R (term μ T R) hR _ ha
    (term_heatBound μ N hT R hR) (term_norm_summable μ N hT R hR hq) ht x y
  have h0 : term μ T R 0 t x y = -R t x y := by simp only [term, clip_of_mem T _ ht]
  have hsucc (n : ℕ) : term μ T R (n+1) t x y = - convolution μ R (term μ T R n) t x y := by
    simp only [term, clip_of_mem T _ ht]
  have hh := hs.of_norm.tsum_eq_zero_add
  simp only [h0, hsucc, tsum_neg] at hh
  change (∑' n, term μ T R n t x y) = _ at hh
  change R t x y + (∑' n, term μ T R n t x y) +
    convolution μ R (fun t x y => ∑' n, term μ T R n t x y) t x y = 0
  change convolution μ R (fun t x y => ∑' n, term μ T R n t x y) t x y = _ at he
  rw [he, hh]
  abel

end TamingCompatibility.GeometricHilbert.KernelSeries

end
end

end

end OAI
