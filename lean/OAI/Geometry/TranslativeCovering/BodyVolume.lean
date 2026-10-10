import OAI.Geometry.TranslativeCovering.BinSelection

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BodyVolume
open Set MeasureTheory Metric SphericalLaw RandomBody CapCost
open scoped ENNReal NNReal

noncomputable def law {n : ℕ} (e : Sphere n) (a : ℝ) :
    Measure (PoissonConfig.Config (Sphere n)) :=
  PoissonSample.simpleSample (rate e (1/a)) (σ n)
instance law_probability {n : ℕ} [NeZero n] (e : Sphere n) (a : ℝ) :
    IsProbabilityMeasure (law e a) := inferInstanceAs (IsProbabilityMeasure (PoissonSample.simpleSample _ _))

lemma law_void {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n) (a : ℝ) :
    PoissonConfig.HasVoidLaw (intensity e (1/a)) (law e a) :=
  PoissonSample.simpleSample_void (rate e (1/a)) (σ n)

lemma membership_eq {n : ℕ} {b t : ℝ} (x : Space n) (hx : ‖x‖ ≤ b) :
    {U : PoissonConfig.Config (Sphere n) | x ∈ body b t U} =
      {U | PoissonConfig.count (cap x t) U = 0} := by
  ext U
  simp only [mem_ofPred_eq,PoissonConfig.count_zero_iff,body,mem_inter_iff,
    mem_closedBall_zero_iff, hx,true_and,mem_iInter,cap,not_lt]

lemma point_survival {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (x : Space n) (hx : ‖x‖ ≤ a) :
    ENNReal.ofReal (Real.exp (-1)) ≤ (law e a) {U | x ∈ body b 1 U} := by
  rw [membership_eq x (hx.trans hab),(law_void e a).void _ (cap_measurable x 1)]
  have hmass := cutting_mass_le e ha x hx
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmass
  have ht1 : 1/a < 1 := (div_lt_one (by linarith)).mpr ha
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [intensity_real]
  have hh := (div_le_one (cap_real_pos e ht1)).mpr hreal
  change (σ n).real (cap x 1)/(σ n).real (cap e.val (1/a)) ≤ 1 at hh
  linarith

lemma volume_tonelli {n : ℕ} (P : Measure (PoissonConfig.Config (Sphere n))) [SFinite P]
    (b t : ℝ) :
    ∫⁻ U,volume (body b t U) ∂P = ∫⁻ x,(P {U | x ∈ body b t U}) := by
  have hS := measurable_bodyRelation (n := n) b t
  exact (Measure.prod_apply hS).symm.trans (Measure.prod_apply_symm hS)

lemma expected_volume {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ENNReal.ofReal (Real.exp (-1))*volume (closedBall (0 : Space n) a) ≤
      ∫⁻ U,volume (body b 1 U) ∂law e a := by
  rw [volume_tonelli]
  calc
    _ = ∫⁻ x,(closedBall (0 : Space n) a).indicator (fun _ => ENNReal.ofReal (Real.exp (-1))) x := by
      rw [lintegral_indicator isClosed_closedBall.measurableSet,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := lintegral_mono fun x => by
      by_cases hx : x ∈ closedBall (0 : Space n) a
      · rw [indicator_of_mem hx]
        exact point_survival e ha hab x (mem_closedBall_zero_iff.mp hx)
      · rw [indicator_of_notMem hx]; exact bot_le

lemma volume_finite {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    volume (body b t U) ≠ ∞ :=
  ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) b).measure_ne_top
    (measure_mono inter_subset_left)

lemma integrable_volume {n : ℕ} (P : Measure (PoissonConfig.Config (Sphere n))) [IsFiniteMeasure P]
    (b t : ℝ) : Integrable (fun U => volume.real (body b t U)) P := by
  apply (integrable_const (volume.real (closedBall (0 : Space n) b))).mono'
    (measurable_bodyVolume b t).ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun U => by
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_mono (μ := volume) inter_subset_left (isCompact_closedBall (0 : Space n) b).measure_ne_top

lemma expected_volume_real {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Real.exp (-1)*volume.real (closedBall (0 : Space n) a) ≤
      ∫ U,volume.real (body b 1 U) ∂law e a := by
  have h := expected_volume e ha hab
  have hi := ofReal_integral_eq_lintegral_ofReal (integrable_volume (law e a) b 1)
    (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
  have he : (∫⁻ U,volume (body b 1 U) ∂law e a) =
      ENNReal.ofReal (∫ U,volume.real (body b 1 U) ∂law e a) := by
    rw [hi]
    apply lintegral_congr
    intro U
    exact (ENNReal.ofReal_toReal (volume_finite b 1 U)).symm
  rw [he] at h
  have he' : ENNReal.ofReal (Real.exp (-1)*volume.real (closedBall (0 : Space n) a)) =
      ENNReal.ofReal (Real.exp (-1))*volume (closedBall (0 : Space n) a) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,Measure.real,
      ENNReal.ofReal_toReal (isCompact_closedBall (0 : Space n) a).measure_ne_top]
  rw [← he'] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => measureReal_nonneg)).mp h

lemma bounded_tail {Ω : Type u_1} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hXi : Integrable X P) {a b c : ℝ}
    (hab : a < b) (hupper : ∀ x, X x ≤ b) (hmean : c ≤ ∫ x,X x ∂P) :
    (c-a)/(b-a) ≤ P.real {x | a < X x} := by
  let S := {x | a < X x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hX
  have hI : (∫ x,X x ∂P) ≤ b*P.real S+a*(1-P.real S) := by
    rw [← integral_add_compl hS hXi]
    have h1 : (∫ x in S,X x ∂P) ≤ ∫ _x in S,b ∂P :=
      integral_mono hXi.integrableOn (integrable_const _) hupper
    have h2 : (∫ x in Sᶜ,X x ∂P) ≤ ∫ _x in Sᶜ,a ∂P := by
      apply integral_mono_ae hXi.integrableOn (integrable_const _)
      filter_upwards [ae_restrict_mem hS.compl] with x hx
      exact le_of_not_gt hx
    have h := add_le_add h1 h2
    simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,
      probReal_compl_eq_one_sub hS,mul_comm] using h
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  linarith

lemma volume_probability {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b v : ℝ} (ha : 1 < a) (hab : a ≤ b) (hv : 2*v < 3)
    (hball : volume.real (closedBall (0 : Space n) b) ≤
      3*volume.real (closedBall (0 : Space n) a)) :
    (Real.exp (-1)-2*v)/(3-2*v) ≤
      (law e a).real {U | 2*v*volume.real (closedBall (0 : Space n) a) < volume.real (body b 1 U)} := by
  let V := volume.real (closedBall (0 : Space n) a)
  have hV : 0 < V := by
    apply ENNReal.toReal_pos _ (isCompact_closedBall (0 : Space n) a).measure_ne_top
    exact ne_of_gt (measure_closedBall_pos volume (0 : Space n) (by linarith : 0 < a))
  have h := bounded_tail (law e a) (fun U => volume.real (body b 1 U))
    (measurable_bodyVolume b 1).ennreal_toReal (integrable_volume (law e a) b 1)
    (show 2*v*V < 3*V by nlinarith)
    (fun U => (measureReal_mono inter_subset_left (isCompact_closedBall (0 : Space n) b).measure_ne_top).trans hball) (expected_volume_real e ha hab)
  convert h using 1
  dsimp [V] at hV ⊢
  field_simp [ne_of_gt hV]

end BodyVolume

end OAI
