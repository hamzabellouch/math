import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.PosteriorChannels

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
lemma scorePosterior_assoc {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p q : α → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (_hq0 : ∀ x,0 ≤ q x)
    (hP : 0 < scoreMass μ p) (_hQ : 0 < scoreMass (scorePosterior μ p) q) :
    scorePosterior (scorePosterior μ p) q = scorePosterior μ (fun x => p x*q x) := by
  have hm := scoreMass_posterior_mul μ p hp hp0 hP q
  unfold scorePosterior
  rw [← withDensity_mul _ (hp.div_const _).ennreal_ofReal (hq.div_const _).ennreal_ofReal]
  apply congrArg (Measure.withDensity μ)
  funext x
  change ENNReal.ofReal (p x/scoreMass μ p)*ENNReal.ofReal (q x/scoreMass (scorePosterior μ p) q) = _
  rw [← ENNReal.ofReal_mul (div_nonneg (hp0 x) hP.le),hm]
  congr 1
  ring

lemma scoreMass_indicator_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) :
    scoreMass μ (S.indicator (fun _ => (1:ℝ))) = μ.real S := by
  rw [scoreMass,integral_indicator hS]
  simp

lemma scorePosterior_indicator_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (S : Set α) (hS : MeasurableSet S) (hP : 0 < μ.real S) :
    scorePosterior μ (S.indicator (fun _ => (1:ℝ))) = cond μ S := by
  rw [scorePosterior,scoreMass_indicator_one μ S hS]
  have he : (fun x => ENNReal.ofReal (S.indicator (fun _ => (1:ℝ)) x/μ.real S)) =
      S.indicator (fun _ => ENNReal.ofReal (1/μ.real S)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he,withDensity_indicator hS,MeasureTheory.withDensity_const,ProbabilityTheory.cond]
  congr 1
  rw [one_div,ENNReal.ofReal_inv_of_pos hP,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma scorePosterior_congr_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p q : α → ℝ} (h : p =ᵐ[μ] q) : scorePosterior μ p = scorePosterior μ q := by
  have hm : scoreMass μ p = scoreMass μ q := integral_congr_ae h
  unfold scorePosterior
  rw [hm]
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

lemma scorePosterior_null_iff {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hP : 0 < scoreMass μ p)
    (S : Set α) (hS : MeasurableSet S) :
    scorePosterior μ p S = 0 ↔ ∀ᵐ x ∂μ,x ∈ S → p x = 0 := by
  rw [scorePosterior,withDensity_apply _ hS,lintegral_eq_zero_iff' (hp.div_const _).ennreal_ofReal.aemeasurable]
  change (∀ᵐ x ∂μ.restrict S, ENNReal.ofReal (p x / scoreMass μ p) = 0) ↔ _
  rw [ae_restrict_iff' hS]
  apply Filter.eventually_congr
  filter_upwards [] with x
  constructor
  · intro hx hxs
    have h : p x/scoreMass μ p ≤ 0 := ENNReal.ofReal_eq_zero.mp (hx hxs)
    exact le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ hP).mp h) (hp0 x)
  · intro hx hxs
    simp [hx hxs]

lemma infoContribution_support_lower {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ)
    (hp : Measurable p) (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1)
    (S : Set α) (hS : MeasurableSet S) (hSpos : 0 < μ.real S)
    (hz : ∀ᵐ x ∂μ,x ∉ S → p x = 0) :
    -scoreMass μ p*Real.log (μ.real S) ≤ infoContribution μ p := by
  have hip := integrable_bounded_measurable μ p hp (C := 1)
    (fun x => by rw [abs_of_nonneg (hp0 x)]; exact hp1 x)
  have hix := integrable_xlog_probability μ p hp hp0 hp1
  have hpint : ∫ x in S,p x ∂μ = scoreMass μ p := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    by_cases h : x ∈ S <;> simp [h,hx]
  have hxint : ∫ x in S,xlog (p x) ∂μ = ∫ x,xlog (p x) ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    by_cases h : x ∈ S <;> simp [h,hx,xlog_zero]
  by_cases hP : scoreMass μ p = 0
  · rw [hP,neg_zero,zero_mul]
    exact infoContribution_nonneg μ p hp hp0 hp1
  have hPp : 0 < scoreMass μ p := lt_of_le_of_ne (scoreMass_nonneg μ p hp0) (Ne.symm hP)
  let y := scoreMass μ p/μ.real S
  have hy : 0 < y := div_pos hPp hSpos
  have h := integral_mono (μ := μ.restrict S) ((integrable_const (xlog y)).add (((hip.restrict.sub (integrable_const y))).const_mul (Real.log y+1)))
    hix.restrict (fun x => xlog_lower_tangent (hp0 x) hy)
  change (∫ x in S, xlog y+(Real.log y+1)*(p x-y) ∂μ) ≤ ∫ x in S,xlog (p x) ∂μ at h
  rw [integral_add (f := fun _ => xlog y) (g := fun x => (Real.log y+1)*(p x-y)) (integrable_const _) ((hip.restrict.sub (integrable_const y)).const_mul _),
    integral_const_mul,integral_sub hip.restrict (integrable_const y),hpint,hxint] at h
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter] at h
  have hey : μ.real S*y = scoreMass μ p := by dsimp [y]; field_simp
  rw [hey,sub_self,mul_zero,add_zero] at h
  have he : μ.real S*xlog y = xlog (scoreMass μ p)-scoreMass μ p*Real.log (μ.real S) := by
    unfold xlog
    dsimp [y]
    rw [Real.log_div hPp.ne' hSpos.ne']
    field_simp
  rw [he] at h
  unfold infoContribution
  linarith

lemma scorePosterior_of_mass_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (h : scoreMass μ p = 0) : scorePosterior μ p = 0 := by
  simp [scorePosterior,h]

lemma scoreMass_mul_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (hq0 : ∀ x,0 ≤ q x) (hp1 : ∀ x,p x ≤ 1) (hq1 : ∀ x,q x ≤ 1) :
    scoreMass μ (fun x => p x*q x) ≤ scoreMass μ p := by
  have hpq1 : ∀ x,p x*q x ≤ 1 := fun x =>
    (mul_le_mul (hp1 x) (hq1 x) (hq0 x) (by norm_num)).trans_eq (one_mul 1)
  apply integral_mono
    (integrable_bounded_measurable μ _ (hp.mul hq) (C := 1) (fun x => by
      change |p x*q x| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (hp0 x) (hq0 x))]; exact hpq1 x))
    (integrable_bounded_measurable μ _ hp (C := 1) (fun x => by rw [abs_of_nonneg (hp0 x)]; exact hp1 x))
  intro x
  simpa using mul_le_mul_of_nonneg_left (hq1 x) (hp0 x)

lemma scoreMass_mul_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (hq0 : ∀ x,0 ≤ q x) (hp1 : ∀ x,p x ≤ 1) (hq1 : ∀ x,q x ≤ 1) :
    scoreMass μ (fun x => p x*q x) = scoreMass μ p*scoreMass (scorePosterior μ p) q := by
  by_cases h : scoreMass μ p = 0
  · rw [h,zero_mul]
    exact le_antisymm (by simpa only [h] using scoreMass_mul_le μ p q hp hq hp0 hq0 hp1 hq1)
      (scoreMass_nonneg μ _ (fun x => mul_nonneg (hp0 x) (hq0 x)))
  · exact (scoreMass_posterior_mul μ p hp hp0
      (lt_of_le_of_ne (scoreMass_nonneg μ p hp0) (Ne.symm h)) q)

namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {κ : ι → Type*} [∀ i,Fintype (κ i)]

def dbind (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i)) : FiniteChannel α (Sigma κ) where
  prob i x := p.prob i.1 x*(q i.1).prob i.2 x
  measurable i := (p.measurable i.1).mul ((q i.1).measurable i.2)
  nonneg i x := mul_nonneg (p.nonneg i.1 x) ((q i.1).nonneg i.2 x)
  total x := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum,FiniteChannel.total,mul_one]
    exact p.total x

lemma information_dbind (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsProbabilityMeasure μ] :
    finiteInformation μ (p.dbind q).prob = finiteInformation μ p.prob+
      ∑ i,scoreMass μ (p.prob i)*finiteInformation (scorePosterior μ (p.prob i)) (q i).prob := by
  unfold finiteInformation
  rw [Fintype.sum_sigma]
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

lemma mass_dbind (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : Sigma κ) :
    scoreMass μ ((p.dbind q).prob i) = scoreMass μ (p.prob i.1)*
      scoreMass (scorePosterior μ (p.prob i.1)) ((q i.1).prob i.2) :=
  scoreMass_mul_eq μ _ _ (p.measurable i.1) ((q i.1).measurable i.2)
    (p.nonneg i.1) ((q i.1).nonneg i.2) (p.le_one i.1) ((q i.1).le_one i.2)

lemma mass_bind {κ : Type*} [Fintype κ] (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ)
    (μ : Measure α) [IsFiniteMeasure μ] (i : ι × κ) :
    scoreMass μ ((p.bind q).prob i) = scoreMass μ (p.prob i.1)*
      scoreMass (scorePosterior μ (p.prob i.1)) ((q i.1).prob i.2) :=
  scoreMass_mul_eq μ _ _ (p.measurable i.1) ((q i.1).measurable i.2)
    (p.nonneg i.1) ((q i.1).nonneg i.2) (p.le_one i.1) ((q i.1).le_one i.2)

lemma coarsen_dbind_fst (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i)) :
    ((p.dbind q).coarsen Sigma.fst).prob = p.prob := by
  classical
  funext i x
  simp only [coarsen,dbind,Fintype.sum_sigma]
  change (∑ a, ∑ b, if a = i then p.prob a x*(q a).prob b x else 0) = _
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp [← Finset.mul_sum,FiniteChannel.total]

lemma coarsen_comp {κ η : Type*} [Fintype κ] [Fintype η]
    (p : FiniteChannel α ι) (f : ι → κ) (g : κ → η) :
    ((p.coarsen f).coarsen g).prob = (p.coarsen (g ∘ f)).prob := by
  classical
  funext k x
  simp only [coarsen,Function.comp_apply]
  have hex (j : κ) : (if g j = k then ∑ i,if f i = j then p.prob i x else 0 else 0) =
      ∑ i,if g j = k then if f i = j then p.prob i x else 0 else 0 := by
    by_cases h : g j = k <;> simp [h]
  simp_rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun j => if g j = k then if f i = j then p.prob i x else 0 else 0) =
      (fun j => if f i = j then if g (f i) = k then p.prob i x else 0 else 0) := by
    funext j
    by_cases h : f i = j
    · subst j; simp
    · simp [h]
  rw [he]
  simp

end FiniteChannel

end RepeatedLocalization

end OAI
