import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.HeavyCells

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
noncomputable def scorePosterior {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (p x/scoreMass μ p))

lemma scorePosterior_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) (hP : 0 < scoreMass μ p) :
    IsProbabilityMeasure (scorePosterior μ p) := by
  have hi := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa [abs_of_nonneg (hp0 x)] using hp1 x)
  refine ⟨?_⟩
  rw [scorePosterior,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (ae_of_all _ (fun x => div_nonneg (hp0 x) hP.le)),
    integral_div]
  change ENNReal.ofReal (scoreMass μ p/scoreMass μ p) = 1
  simp [hP.ne']

lemma integral_scorePosterior {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x)
    (hP : 0 < scoreMass μ p) (f : α → ℝ) :
    (∫ x,f x ∂scorePosterior μ p) = (∫ x,p x*f x ∂μ)/scoreMass μ p := by
  rw [scorePosterior,integral_withDensity_eq_integral_toReal_smul (hp.div_const _).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hp0 _) hP.le),smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact integral_div _ _

lemma scorePosterior_apply_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp1 : ∀ x,p x ≤ 1)
    (hP : 0 < scoreMass μ p) (s : Set α) (hs : MeasurableSet s) :
    scorePosterior μ p s ≤ ENNReal.ofReal (1/scoreMass μ p)*μ s := by
  rw [scorePosterior,withDensity_apply _ hs]
  calc
    _ ≤ ∫⁻ _ in s,ENNReal.ofReal (1/scoreMass μ p) ∂μ := lintegral_mono (fun x =>
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hp1 x) hP.le))
    _ = _ := by simp

lemma scorePosterior_null_of_score_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (s : Set α) (hs : MeasurableSet s)
    (hz : ∀ x ∈ s,p x = 0) : scorePosterior μ p s = 0 := by
  rw [scorePosterior,withDensity_apply _ hs]
  calc
    _ = ∫⁻ _ in s,(0:ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simp [hz x hx]
    _ = 0 := by simp

lemma scorePosterior_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) : scorePosterior μ p ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma scoreMass_posterior_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x)
    (hP : 0 < scoreMass μ p) (q : α → ℝ) :
    scoreMass μ (fun x => p x*q x) = scoreMass μ p*scoreMass (scorePosterior μ p) q := by
  change (∫ x,p x*q x ∂μ) = scoreMass μ p*(∫ x,q x ∂scorePosterior μ p)
  rw [integral_scorePosterior μ p hp hp0 hP]
  field_simp

lemma infoContribution_split {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1)
    (q : ι → α → ℝ) (hq : ∀ i,Measurable (q i)) (hq0 : ∀ i x,0 ≤ q i x)
    (hq1 : ∀ i x,q i x ≤ 1) (hqs : ∀ x,∑ i,q i x = 1) (hP : 0 < scoreMass μ p) :
    (∑ i,infoContribution μ (fun x => p x*q i x)) =
      infoContribution μ p+scoreMass μ p*finiteInformation (scorePosterior μ p) q := by
  have := scorePosterior_probability μ p hp hp0 hp1 hP
  let ν := scorePosterior μ p
  have hip := integrable_xlog_probability μ p hp hp0 hp1
  have hipq (i : ι) : Integrable (fun x => q i x*xlog (p x)) μ :=
    hip.bdd_mul (hq i).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hq0 i x)] using hq1 i x))
  have hiqp (i : ι) : Integrable (fun x => p x*xlog (q i x)) μ :=
    (integrable_xlog_probability μ (q i) (hq i) (hq0 i) (hq1 i)).bdd_mul
      hp.aestronglyMeasurable (ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hp0 x)] using hp1 x))
  have hm (i : ι) := scoreMass_posterior_mul μ p hp hp0 hP (q i)
  have hx (i : ι) : (∫ x,p x*xlog (q i x) ∂μ) =
      scoreMass μ p*(∫ x,xlog (q i x) ∂ν) := by
    rw [integral_scorePosterior μ p hp hp0 hP]
    field_simp
  have hsum : ∑ i,scoreMass ν (q i) = 1 := by
    unfold scoreMass
    rw [← integral_finsetSum]
    · simp [hqs]
    · intro i hi
      exact integrable_bounded_measurable ν (q i) (hq i) (C := 1)
        (fun x => by simpa only [abs_of_nonneg (hq0 i x)] using hq1 i x)
  have hfirst : (∑ i,∫ x,q i x*xlog (p x) ∂μ) = ∫ x,xlog (p x) ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hipq i)]
    simp_rw [← Finset.sum_mul,hqs,one_mul]
  unfold finiteInformation
  simp only [infoContribution]
  dsimp only [ν] at hx hsum
  simp_rw [xlog_mul,integral_add (hipq _) (hiqp _),hx,hm,xlog_mul]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    ← Finset.sum_mul,hsum,one_mul,hfirst]
  ring

lemma infoContribution_split_zero {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1)
    (q : ι → α → ℝ) (hq : ∀ i,Measurable (q i)) (hq0 : ∀ i x,0 ≤ q i x)
    (hq1 : ∀ i x,q i x ≤ 1) (hP : scoreMass μ p = 0) :
    (∑ i,infoContribution μ (fun x => p x*q i x)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hpi : ∀ x,p x*q i x ≤ 1 := fun x => (mul_le_mul (hp1 x) (hq1 i x) (hq0 i x) (by norm_num)).trans_eq (one_mul 1)
  apply infoContribution_zero_mass μ _ (hp.mul (hq i)) (fun x => mul_nonneg (hp0 x) (hq0 i x)) hpi
  have hn : 0 ≤ scoreMass μ (fun x => p x*q i x) := scoreMass_nonneg _ _ (fun x => mul_nonneg (hp0 x) (hq0 i x))
  have hi1 := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hi2 := integrable_bounded_measurable μ (fun x => p x*q i x) (hp.mul (hq i)) (C := 1)
    (fun x => by rw [abs_of_nonneg (mul_nonneg (hp0 x) (hq0 i x))]; exact hpi x)
  have hh : scoreMass μ (fun x => p x*q i x) ≤ scoreMass μ p :=
    integral_mono hi2 hi1 (fun x => by simpa using mul_le_mul_of_nonneg_left (hq1 i x) (hp0 x))
  change scoreMass μ (fun x => p x*q i x) = 0
  linarith

structure FiniteChannel (α ι : Type*) [MeasurableSpace α] [Fintype ι] where
  prob : ι → α → ℝ
  measurable : ∀ i,Measurable (prob i)
  nonneg : ∀ i x,0 ≤ prob i x
  total : ∀ x,∑ i,prob i x = 1

namespace FiniteChannel
variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]

lemma le_one (p : FiniteChannel α ι) (i : ι) (x : α) : p.prob i x ≤ 1 := by
  rw [← p.total x]
  exact Finset.single_le_sum (fun j _ => p.nonneg j x) (Finset.mem_univ _)

lemma integrable (p : FiniteChannel α ι) (μ : Measure α) [IsFiniteMeasure μ] (i : ι) :
    Integrable (p.prob i) μ := integrable_bounded_measurable μ _ (p.measurable i) (C := 1)
      (fun x => by rw [abs_of_nonneg (p.nonneg i x)]; exact p.le_one i x)

lemma mass_total (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ i,scoreMass μ (p.prob i) = 1 := by
  unfold scoreMass
  rw [← integral_finsetSum _ (fun i _ => p.integrable μ i)]
  simp [p.total]

lemma information_nonneg (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    0 ≤ finiteInformation μ p.prob := Finset.sum_nonneg (fun i _ =>
      infoContribution_nonneg μ _ (p.measurable i) (p.nonneg i) (p.le_one i))

def bind (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ) : FiniteChannel α (ι × κ) where
  prob i x := p.prob i.1 x*(q i.1).prob i.2 x
  measurable i := (p.measurable i.1).mul ((q i.1).measurable i.2)
  nonneg i x := mul_nonneg (p.nonneg i.1 x) ((q i.1).nonneg i.2 x)
  total x := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,FiniteChannel.total,mul_one]
    exact p.total x

lemma information_bind (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ)
    (μ : Measure α) [IsProbabilityMeasure μ] :
    finiteInformation μ (p.bind q).prob = finiteInformation μ p.prob+
      ∑ i,scoreMass μ (p.prob i)*finiteInformation (scorePosterior μ (p.prob i)) (q i).prob := by
  unfold finiteInformation
  rw [Fintype.sum_prod_type]
  have he (i : ι) :
      (∑ j,infoContribution μ (fun x => p.prob i x*(q i).prob j x)) =
        infoContribution μ (p.prob i)+scoreMass μ (p.prob i)*finiteInformation (scorePosterior μ (p.prob i)) (q i).prob := by
    by_cases h : scoreMass μ (p.prob i) = 0
    · rw [infoContribution_split_zero μ _ (p.measurable i) (p.nonneg i) (p.le_one i)
        _ (q i).measurable (q i).nonneg (q i).le_one h,
        infoContribution_zero_mass μ _ (p.measurable i) (p.nonneg i) (p.le_one i) h,h]
      simp
    · exact infoContribution_split μ _ (p.measurable i) (p.nonneg i) (p.le_one i)
        _ (q i).measurable (q i).nonneg (q i).le_one (q i).total
          (lt_of_le_of_ne (scoreMass_nonneg μ _ (p.nonneg i)) (Ne.symm h))
  change (∑ i,∑ j,infoContribution μ (fun x => p.prob i x*(q i).prob j x)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  rfl

open scoped Classical in
noncomputable def deterministic [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (f : α → κ) (hf : Measurable f) : FiniteChannel α κ where
  prob i x := if f x = i then 1 else 0
  measurable i := measurable_const.piecewise (hf (measurableSet_singleton i)) measurable_const
  nonneg i x := by split_ifs <;> norm_num
  total x := by
    classical
    simp

lemma deterministic_information [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (f : α → κ) (hf : Measurable f) (μ : Measure α) :
    finiteInformation μ (deterministic f hf).prob =
      -∑ i,xlog (scoreMass μ ((deterministic f hf).prob i)) := by
  unfold finiteInformation infoContribution
  have he (i : κ) : (fun x => xlog ((deterministic f hf).prob i x)) = 0 := by
    funext x
    dsimp [deterministic]
    split_ifs <;> simp [xlog]
  simp only [he]
  simp

end FiniteChannel

lemma infoContribution_sum_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ι) (p : ι → α → ℝ)
    (hp : ∀ i,Measurable (p i)) (hp0 : ∀ i x,0 ≤ p i x)
    (hp1 : ∀ x,∑ i ∈ s,p i x ≤ 1) :
    infoContribution μ (fun x => ∑ i ∈ s,p i x) ≤ ∑ i ∈ s,infoContribution μ (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [infoContribution,scoreMass,xlog]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi] at hp1 ⊢
    have hs1 : ∀ x,∑ j ∈ s,p j x ≤ 1 := by intro x; have := hp1 x; linarith [hp0 i x]
    have h := infoContribution_add_le μ (p i) (fun x => ∑ j ∈ s,p j x) (hp i)
      (Finset.measurable_sum _ (fun j _ => hp j)) (hp0 i) (fun x => Finset.sum_nonneg (fun j _ => hp0 j x)) hp1
    exact h.trans (add_le_add le_rfl (ih hs1))

namespace FiniteChannel
variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]

open scoped Classical in
noncomputable def coarsen (p : FiniteChannel α ι) (f : ι → κ) : FiniteChannel α κ where
  prob j x := ∑ i,if f i = j then p.prob i x else 0
  measurable j := Finset.measurable_sum _ (fun i _ => by by_cases h : f i = j <;> simp [h,p.measurable])
  nonneg j x := Finset.sum_nonneg (fun i _ => by split_ifs; exact p.nonneg _ _; exact le_refl _)
  total x := by
    classical
    rw [Finset.sum_comm]
    simp [p.total]

lemma information_coarsen_le (p : FiniteChannel α ι) (f : ι → κ)
    (μ : Measure α) [IsProbabilityMeasure μ] :
    finiteInformation μ (p.coarsen f).prob ≤ finiteInformation μ p.prob := by
  classical
  have h (j : κ) := infoContribution_sum_le μ Finset.univ
    (fun i x => if f i = j then p.prob i x else 0)
    (fun i => by by_cases h : f i = j <;> simp [h,p.measurable])
    (fun i x => by split_ifs; exact p.nonneg _ _; exact le_refl _)
    ((p.coarsen f).le_one j)
  have H := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  change finiteInformation μ (p.coarsen f).prob ≤ _ at H
  apply H.trans_eq
  rw [Finset.sum_comm]
  unfold finiteInformation
  apply Finset.sum_congr rfl
  intro i hi
  have he (j : κ) : infoContribution μ (fun x => if f i = j then p.prob i x else 0) =
      if f i = j then infoContribution μ (p.prob i) else 0 := by
    by_cases h : f i = j <;> simp [h,infoContribution,scoreMass,xlog]
  simp_rw [he]
  simp

end FiniteChannel

end RepeatedLocalization

end OAI
