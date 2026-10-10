import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestActualMoment

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpLogRamsey.PoissonGrouping
open Classical
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def law (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi fun i => poissonMeasure (rate i)

instance probability (rate : ι → ℝ≥0) : IsProbabilityMeasure (law rate) := by
  unfold law
  infer_instance

lemma sum_hasLaw (rate : ι → ℝ≥0) (S : Finset ι) :
    HasLaw (fun ω : ι → ℕ => ∑ i ∈ S, ω i) (poissonMeasure (∑ i ∈ S, rate i)) (law rate) := by
  have hi : iIndepFun (fun i (ω : ι → ℕ) => ω i) (law rate) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have he (i : ι) : HasLaw (fun ω : ι → ℕ => ω i) (poissonMeasure (rate i)) (law rate) :=
    (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_const, measure_univ, one_smul]
    symm
    apply Measure.ext_of_singleton
    intro n
    rw [poissonMeasure_singleton]
    cases n <;> simp
  | @insert i S hiS ih =>
    have ih' : HasLaw (∑ j ∈ S, fun ω : ι → ℕ => ω j)
        (poissonMeasure (∑ j ∈ S, rate j)) (law rate) := by
      convert ih using 1
      ext ω
      simp
    simp only [Finset.sum_insert hiS]
    convert (hi.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) hiS).symm.hasLaw_add_poissonMeasure
        (he i) ih' using 1
    ext ω
    simp

def regroup (g : ι → κ) (ω : ι → ℕ) : (k : κ) → {i // g i = k} → ℕ :=
  fun _ i => ω i

lemma regroup_hasLaw (rate : ι → ℝ≥0) (g : ι → κ) :
    HasLaw (regroup g) (Measure.pi fun k => law (fun i : {i // g i = k} => rate i)) (law rate) := by
  refine ⟨by exact (measurable_of_countable _).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z)]
  have hpre : regroup g ⁻¹' {z} = {fun i => z (g i) ⟨i, rfl⟩} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      exact congrFun (congrFun h (g i)) ⟨i, rfl⟩
    · rintro rfl
      funext k i
      obtain ⟨i, rfl⟩ := i
      rfl
  rw [hpre]
  simp only [law, Measure.pi_singleton]
  have hf := Fintype.prod_fiberwise g (fun i => (poissonMeasure (rate i)) {z (g i) ⟨i, rfl⟩})
  convert hf.symm using 1
  apply Finset.prod_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨i, rfl⟩ := i
  rfl

def groupedCount (g : ι → κ) (ω : ι → ℕ) (k : κ) : ℕ :=
  ∑ i : {i // g i = k}, ω i

theorem groupedCount_hasLaw (rate : ι → ℝ≥0) (g : ι → κ) :
    HasLaw (groupedCount g)
      (law (fun k => ∑ i : {i // g i = k}, rate i)) (law rate) := by
  have hs (k : κ) : HasLaw (fun ω : {i // g i = k} → ℕ => ∑ i, ω i)
      (poissonMeasure (∑ i : {i // g i = k}, rate i))
      (law (fun i : {i // g i = k} => rate i)) := sum_hasLaw _ Finset.univ
  have hp := measurePreserving_pi _ _ (fun k => (hs k).measurePreserving (by fun_prop))
  exact hp.hasLaw.comp (regroup_hasLaw rate g)

end
end SharpLogRamsey.PoissonGrouping

namespace SharpLogRamsey.PoissonGrouping
open Finset MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
lemma groupedCount_eq_zero (g : ι → κ) (ω : ι → ℕ) (k : κ) :
    groupedCount g ω k=0 ↔ ∀ i,g i=k → ω i=0 := by
  simp only [groupedCount,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies]
  exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.2⟩

omit [Fintype κ] in
lemma grouped_empty_iff (g : ι → κ) (ω : ι → ℕ) (S : Finset κ) :
    (∀ k∈S,groupedCount g ω k=0) ↔ ∀ i,g i∈S → ω i=0 := by
  simp only [groupedCount_eq_zero]
  constructor
  · intro h i hi
    exact h (g i) hi i rfl
  · intro h k hk i he
    exact h i (he ▸ hk)

theorem grouped_moment (rate : ι → ℝ≥0) (g : ι → κ) (f : (κ → ℕ) → ℝ) (p : ℕ) :
    (∫ ω,f (groupedCount g ω)^p ∂law rate) =
      ∫ ω,f ω^p ∂law (fun k => ∑ i : {i // g i=k},rate i) := by
  exact (groupedCount_hasLaw rate g).integral_comp
    (measurable_of_countable (fun ω => f ω^p)).aestronglyMeasurable

end
end SharpLogRamsey.PoissonGrouping

namespace SharpLogRamsey.PointScore
open Finset MeasureTheory ProbabilityTheory
open SharpRamseyFive.PoissonScore SharpLogRamsey.PoissonGrouping
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D H : Type*} [Fintype A] [Fintype D] [Fintype H]

def pointEmpty {R : ℕ} (P : A → Prop) (ω : Fin R × A → ℕ) (r : Fin R) : ℝ :=
  if ∀ y,P y → ω (r,y)=0 then 1 else 0

def pointScore {R : ℕ} (own : A → Prop) (inc : H → A → Prop) (b : ℝ)
    (ω : Fin R × A → ℕ) : ℝ :=
  ∑ h,∏ r,pointEmpty (fun y => own y ∧ inc h y) ω r *
    (pointEmpty (fun y => ¬own y ∧ inc h y) ω r-b)

def held {R : ℕ} (own center : A → Prop) (i : Fin R × A) : Prop := own i.2 ∨ center i.2

def outsideGroup {R : ℕ} (own center : A → Prop) (g : {y // ¬(own y ∨ center y)} → D)
    (i : {i : Fin R × A // ¬held own center i}) : Fin R × D :=
  (i.1.1,g ⟨i.1.2,i.2⟩)

def ownBit {R : ℕ} (own center : A → Prop) (inc : H → A → Prop)
    (a : {i : Fin R × A // held own center i} → ℕ) (h : H) (r : Fin R) : Bool :=
  decide (∀ y,∀ ho : own y,inc h y → a ⟨(r,y),Or.inl ho⟩=0)

omit [Fintype D] [Fintype H] in
lemma grouped_empty {R : ℕ} (own center : A → Prop) (g : {y // ¬(own y ∨ center y)} → D)
    (T : Finset D) (a : {i : Fin R × A // ¬held own center i} → ℕ) (r : Fin R) :
    (∀ d∈T,groupedCount (outsideGroup own center g) a (r,d)=0) ↔
      ∀ y : {y // ¬(own y ∨ center y)},g y∈T → a ⟨(r,y),y.2⟩=0 := by
  classical
  simp only [PoissonGrouping.groupedCount_eq_zero]
  constructor
  · intro hh y hy
    exact hh (g y) hy ⟨(r,y),y.2⟩ rfl
  · intro hh d hd i hi
    have hr : i.1.1=r := congrArg Prod.fst hi
    have hg : g ⟨i.1.2,i.2⟩=d := congrArg Prod.snd hi
    have hh' := hh ⟨i.1.2,i.2⟩ (hg ▸ hd)
    convert hh' using 1
    apply congrArg a
    apply Subtype.ext
    exact Prod.ext hr rfl

omit [Fintype D] in
lemma source_score_eq_grouped {R : ℕ} (own center : A → Prop) (inc : H → A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (lines : H → Finset D)
    (hinc : ∀ h y,inc h y.1 ↔ g y∈lines h) (b : ℝ) (ω : Fin R × A → ℕ)
    (hcenter : ∀ r y,center y → ω (r,y)=0) :
    pointScore own inc b ω =
      ∑ h,scoreTerm (lines h) b (ownBit own center inc (fun i => ω i.1) h)
        (fun r d => groupedCount (outsideGroup own center g) (fun i => ω i.1) (r,d)) := by
  classical
  apply sum_congr rfl
  intro h _
  apply prod_congr rfl
  intro r _
  have ho : pointEmpty (fun y => own y ∧ inc h y) ω r =
      if ownBit own center inc (fun i => ω i.1) h r then (1:ℝ) else 0 := by
    simp only [pointEmpty,ownBit]
    congr 1
    exact propext (by aesop)
  have he : (∀ y,¬own y ∧ inc h y → ω (r,y)=0) ↔
      ∀ d∈lines h,groupedCount (outsideGroup own center g) (fun i => ω i.1) (r,d)=0 := by
    rw [grouped_empty]
    constructor
    · intro hh y hy
      exact hh y ⟨fun ho => y.2 (Or.inl ho),(hinc h y).mpr hy⟩
    · intro hh y hy
      by_cases hc : center y
      · exact hcenter r y hc
      · have hn : ¬(own y ∨ center y) := by tauto
        exact hh ⟨y,hn⟩ ((hinc h ⟨y,hn⟩).mp hy.2)
  have hx : pointEmpty (fun y => ¬own y ∧ inc h y) ω r =
      emptyIndicator (lines h) (fun d => groupedCount (outsideGroup own center g) (fun i => ω i.1) (r,d)) := by
    simp only [pointEmpty,emptyIndicator,emptyEvent,Set.indicator_apply,Set.mem_pi,
      Finset.mem_coe,Set.mem_singleton_iff,he]
  change _ = if ownBit own center inc (fun i => ω i.1) h r then _ else 0
  rw [ho,hx]
  unfold centeredFactor
  split_ifs <;> simp

end
end SharpLogRamsey.PointScore

open MeasureTheory
open scoped BigOperators Classical
namespace SharpLogRamsey.BoundedProbability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem mass_above_half (Y : Ω → ℝ) (hY : Integrable Y μ)
    (m a : ℝ) (hm : 0  <  m) (ha : 0  ≤  a)
    (hupper : ∀ ω,Y ω ≤ m) (hlower : m*a ≤ ∫ ω,Y ω ∂μ)
    (hE : MeasurableSet {ω | m*a/2 ≤ Y ω}) :
    a/2  ≤  μ.real {ω | m*a/2 ≤ Y ω} := by
  let E := {ω | m*a/2 ≤ Y ω}
  have hi : Integrable (E.indicator (fun _ : Ω =>  m)) μ := (integrable_const _).indicator hE
  have hp : ∀ ω,Y ω  ≤  m*a/2+E.indicator (fun _ : Ω =>  m) ω := by
    intro ω
    by_cases he : ω∈E
    · rw [Set.indicator_of_mem he]
      nlinarith [hupper ω]
    · rw [Set.indicator_of_notMem he]
      exact le_trans (le_of_lt (not_le.mp he)) (by simp)
  have hh := integral_mono hY ((integrable_const _).add hi) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hi,integral_const,
    integral_indicator_const _ hE] at hh
  simp only [probReal_univ,smul_eq_mul] at hh
  apply (le_of_mul_le_mul_left ?_ hm)
  nlinarith

theorem real_markov (Y : Ω → ℝ) (hY : Integrable Y μ) (hy : ∀ ω,0 ≤ Y ω)
    (t : ℝ) (_ht : 0  ≤  t) (hE : MeasurableSet {ω | t ≤ Y ω}) :
    t*μ.real {ω | t ≤ Y ω}  ≤  ∫ ω,Y ω ∂μ := by
  have hi := (integrable_const t).indicator hE (μ:=μ)
  have hp : ∀ ω,({ω | t ≤ Y ω}.indicator (fun _ : Ω =>  t)) ω  ≤  Y ω := by
    intro ω
    by_cases he : t ≤ Y ω
    · simp [he]
    · simpa [he] using hy ω
  have hh := integral_mono hi hY hp
  rw [integral_indicator_const _ hE] at hh
  simpa only [smul_eq_mul,mul_comm] using hh

lemma good_minus_bad (E B : Set Ω) : μ.real E-μ.real B  ≤  μ.real (E\B) := by
  have hh : μ.real E  ≤  μ.real (E\B)+μ.real B := by
    apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) (measureReal_union_le _ _)
    intro ω hω
    by_cases hB : ω∈B
    · exact Or.inr hB
    · exact Or.inl ⟨hω,hB⟩
  linarith

end
end SharpLogRamsey.BoundedProbability

namespace SharpLogRamsey.BoundedProbability
open MeasureTheory Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω A B I : Type*} [MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B]

theorem product_event_le (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (A×B)) (hE : MeasurableSet E) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ a,ν.real (Prod.mk a ⁻¹' E) ≤ ε) : (μ.prod ν).real E ≤ ε := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mp
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ _a,ENNReal.ofReal ε ∂μ := lintegral_mono (fun a =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mpr (h a))
    _ = _ := by simp

theorem even_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0 < t)
    (hi : Integrable (fun ω => f ω^p) μ)
    (hE : MeasurableSet {ω | t ≤ |f ω|})
    (hm : (∫ ω,f ω^p ∂μ) ≤ M) :
    μ.real {ω | t ≤ |f ω|} ≤ M/t^p := by
  have hh : t^p*μ.real {ω | t ≤ |f ω|} ≤ ∫ ω,f ω^p ∂μ := by
    have hi' := (integrable_const (t^p)).indicator hE (μ:=μ)
    have hpt : ∀ ω,({ω | t ≤ |f ω|}.indicator (fun _ => t^p)) ω ≤ f ω^p := by
      intro ω
      by_cases he : t ≤ |f ω|
      · rw [Set.indicator_of_mem (show ω∈{ω | t ≤ |f ω|} from he),←hp.pow_abs (f ω)]
        exact pow_le_pow_left₀ ht.le he p
      · rw [Set.indicator_of_notMem (show ω∉{ω | t ≤ |f ω|} from he)]
        exact hp.pow_nonneg (f ω)
    have hle := integral_mono hi' hi hpt
    rw [integral_indicator_const _ hE,smul_eq_mul] at hle
    simpa only [mul_comm] using hle
  exact (le_div_iff₀ (pow_pos ht p)).mpr (by simpa only [mul_comm] using hh.trans hm)

def eventCount (S : Finset I) (E : I → Set Ω) (ω : Ω) : ℝ :=
  ∑ i∈S,if ω∈E i then 1 else 0

omit [MeasurableSpace Ω] in
lemma eventCount_nonneg (S : Finset I) (E : I → Set Ω) (ω : Ω) :
    0 ≤ eventCount S E ω := sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma integrable_eventCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset I) (E : I → Set Ω) (hE : ∀ i∈S,MeasurableSet (E i)) :
    Integrable (eventCount S E) μ := by
  apply integrable_finsetSum
  intro i hi
  exact (integrable_const 1).indicator (hE i hi)

lemma integral_eventCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset I) (E : I → Set Ω) (hE : ∀ i∈S,MeasurableSet (E i)) :
    (∫ ω,eventCount S E ω ∂μ) = ∑ i∈S,μ.real (E i) := by
  unfold eventCount
  rw [integral_finsetSum _ (fun i hi => (integrable_const 1).indicator (hE i hi))]
  apply sum_congr rfl
  intro i hi
  have he : (fun ω : Ω => if ω∈E i then (1:ℝ) else 0) = (E i).indicator (fun _ => 1) := rfl
  rw [he,integral_indicator_const _ (hE i hi)]
  simp

theorem eventCount_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset I) (E : I → Set Ω) (hE : ∀ i∈S,MeasurableSet (E i))
    (ε t : ℝ) (ht : 0 < t) (he : ∀ i∈S,μ.real (E i) ≤ ε) :
    μ.real {ω | t ≤ eventCount S E ω} ≤ (S.card:ℝ)*ε/t := by
  have hi := integrable_eventCount μ S E hE
  have hme : Measurable (eventCount S E) := by
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.indicator (hE i hi)
  have hm := real_markov μ (eventCount S E) hi (eventCount_nonneg S E) t ht.le
    (measurableSet_le measurable_const hme)
  rw [integral_eventCount μ S E hE] at hm
  have hs : (∑ i∈S,μ.real (E i)) ≤ (S.card:ℝ)*ε := by
    calc
      _ ≤ ∑ _i∈S,ε := sum_le_sum he
      _ = _ := by simp
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hm.trans hs)

end
end SharpLogRamsey.BoundedProbability

namespace SharpLogRamsey.PoissonConditioning
open MeasureTheory ProbabilityTheory
open SharpLogRamsey.BoundedProbability
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem own_outside_tail (rate : ι → ℝ≥0) (own : ι → Prop)
    (f : ({i // own i} → ℕ) → ({i // ¬own i} → ℕ) → ℝ)
    (score : (ι → ℕ) → ℝ) (unsampled : (ι → ℕ) → Prop)
    (heq : ∀ ω,unsampled ω → score ω=f (fun i => ω i) (fun i => ω i))
    (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0 < t) (hM : 0 ≤ M)
    (hi : ∀ a,Integrable (fun b => f a b^p)
      (Measure.pi (fun i : {i // ¬own i} => poissonMeasure (rate i))))
    (hm : ∀ a,(∫ b,f a b^p ∂Measure.pi (fun i : {i // ¬own i} => poissonMeasure (rate i))) ≤ M) :
    (Measure.pi (fun i => poissonMeasure (rate i))).real
      {ω | unsampled ω ∧ t ≤ |score ω|} ≤ M/t^p := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℕ) own
  let ν₁ := Measure.pi (fun i : {i // own i} => poissonMeasure (rate i))
  let ν₂ := Measure.pi (fun i : {i // ¬own i} => poissonMeasure (rate i))
  let E : Set (({i // own i} → ℕ) × ({i // ¬own i} → ℕ)) := {ab | t ≤ |f ab.1 ab.2|}
  have hE : MeasurableSet E := Set.to_countable _ |>.measurableSet
  have hp' := measurePreserving_piEquivPiSubtypeProd (fun i => poissonMeasure (rate i)) own
  have hh : (ν₁.prod ν₂).real E ≤ M/t^p := by
    apply product_event_le ν₁ ν₂ E hE (M/t^p) (by positivity)
    intro a
    exact even_moment_tail ν₂ (f a) p hp t M ht (hi a)
      (Set.to_countable _ |>.measurableSet) (hm a)
  have hsub : {ω | unsampled ω ∧ t ≤ |score ω|} ⊆ e ⁻¹' E := by
    intro ω hω
    change t ≤ |f (fun i => ω i) (fun i => ω i)|
    rw [←heq ω hω.1]
    exact hω.2
  apply (measureReal_mono (h₂:=measure_ne_top _ _) hsub).trans
  have he : (Measure.pi (fun i => poissonMeasure (rate i))).real (e ⁻¹' E) =
      (ν₁.prod ν₂).real E := by
    unfold Measure.real
    rw [hp'.measure_preimage hE.nullMeasurableSet]
  rw [he]
  exact hh

end
end SharpLogRamsey.PoissonConditioning

namespace SharpLogRamsey.PointScore
open Finset MeasureTheory ProbabilityTheory
open SharpRamseyFive.PoissonScore SharpLogRamsey.PoissonGrouping
open SharpLogRamsey.PoissonConditioning
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D H : Type*} [Fintype A] [Fintype D] [Fintype H]

omit [Fintype A] [Fintype D] [Fintype H] in
lemma centeredFactor_abs (T : Finset D) (b : ℝ) (ω : D → ℕ) :
    |centeredFactor T b ω|≤1+|b| := by
  unfold centeredFactor emptyIndicator
  rw [Set.indicator_apply]
  split_ifs
  · exact (abs_sub _ _).trans (by simp)
  · simp only [zero_sub,abs_neg]
    linarith [abs_nonneg b]

omit [Fintype A] [Fintype D] in
lemma radial_score_abs {R : ℕ} (lines : H → Finset D) (b : ℝ)
    (own : H → Fin R → Bool) (ω : Fin R × D → ℕ) :
    |∑ h,scoreTerm (lines h) b (own h) (fun r d => ω (r,d))| ≤
      (Fintype.card H:ℝ)*(1+|b|)^R := by
  calc
    _ ≤ ∑ h,|scoreTerm (lines h) b (own h) (fun r d => ω (r,d))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _h : H,(1+|b|)^R := by
      apply sum_le_sum
      intro h _
      unfold scoreTerm
      rw [abs_prod]
      calc
        _ ≤ ∏ _r : Fin R,(1+|b|) := by
          apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
          intro r _
          split_ifs
          · exact centeredFactor_abs _ _ _
          · simp only [abs_zero]; positivity
        _ = _ := by simp
    _ = _ := by simp

omit [Fintype A] [Fintype D] in
lemma integrable_radial_power {R : ℕ} (lines : H → Finset D) (b : ℝ)
    (own : H → Fin R → Bool) (p : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    [Countable Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → Fin R × D → ℕ) :
    Integrable (fun ω => (∑ h,scoreTerm (lines h) b (own h) (fun r d => g ω (r,d)))^p) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (((Fintype.card H:ℝ)*(1+|b|)^R)^p)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (radial_score_abs lines b own (g ω)) p

theorem point_score_tail {R : ℕ} (rate : Fin R × A → ℝ≥0)
    (own center : A → Prop) (inc : H → A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (lines : H → Finset D)
    (hinc : ∀ h y,inc h y.1 ↔ g y∈lines h) (b : ℝ)
    (radialRate : Fin R × D → ℝ≥0)
    (hrate : ∀ k,(∑ i : {i : {i : Fin R × A // ¬held own center i} //
      outsideGroup own center g i=k},rate i.1.1)=radialRate k)
    (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0<t) (hM : 0≤M)
    (hm : ∀ bits : H → Fin R → Bool,
      (∫ ω,(∑ h,scoreTerm (lines h) b (bits h) (fun r d => ω (r,d)))^p
        ∂batchMeasure radialRate)≤M) :
    (batchMeasure rate).real {ω | (∀ r y,center y → ω (r,y)=0) ∧
      t≤|pointScore own inc b ω|} ≤ M/t^p := by
  let f := fun (a : {i : Fin R × A // held own center i} → ℕ)
      (c : {i : Fin R × A // ¬held own center i} → ℕ) =>
    ∑ h,scoreTerm (lines h) b (ownBit own center inc a h)
      (fun r d => groupedCount (outsideGroup own center g) c (r,d))
  apply own_outside_tail rate (held own center) f (pointScore own inc b)
    (fun ω => ∀ r y,center y → ω (r,y)=0)
    (fun ω hc => source_score_eq_grouped own center inc g lines hinc b ω hc)
    p hp t M ht hM
  · intro a
    exact integrable_radial_power lines b (ownBit own center inc a) p _
      (groupedCount (outsideGroup own center g))
  · intro a
    have hh := grouped_moment (fun i : {i : Fin R × A // ¬held own center i} => rate i.1)
      (outsideGroup own center g)
      (fun ω => ∑ h,scoreTerm (lines h) b (ownBit own center inc a h) (fun r d => ω (r,d))) p
    change (∫ c,(f a c)^p ∂law (fun i : {i : Fin R × A // ¬held own center i} => rate i.1))≤M
    apply hh.le.trans
    convert! hm (ownBit own center inc a) using 1
    congr 2
    funext k
    convert! hrate k using 1
    congr 1
    ext i
    simp only [mem_univ]

end
end SharpLogRamsey.PointScore

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def direction (x : Projectivization K V) (y : {y : Projectivization K V // y≠x}) :
    RadialLine x := ⟨x.submodule ⊔ y.1.submodule,finrank_join x y.1 y.2.symm,le_sup_left⟩

omit [Finite K] in
lemma direction_eq_iff (x : Projectivization K V)
    (y : {y : Projectivization K V // y≠x}) (W : RadialLine x) :
    direction x y=W ↔ y.1.submodule ≤ W.1 := by
  constructor
  · intro h
    rw [←h]
    exact le_sup_right
  · intro h
    exact Subtype.ext (radial_unique x y y.2.symm W h)

lemma direction_mem_lines (x : Projectivization K V)
    (y : {y : Projectivization K V // y≠x}) (H : Projectivization K (Module.Dual K V))
    (hx : x.submodule ≤ LinearMap.ker H.rep) :
    direction x y∈lines x H ↔ y.1.submodule ≤ LinearMap.ker H.rep := by
  rw [mem_lines]
  change x.submodule ⊔ y.1.submodule ≤ LinearMap.ker H.rep ↔ _
  simp only [sup_le_iff,hx,true_and]

omit [Finite K] in
theorem direction_fiber_card (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (hx : x∉S) (W : RadialLine x) :
    Fintype.card {y : S // direction x ⟨y.1,fun h => hx (h ▸ y.2)⟩=W}=
      (radialFiber S x W).card := by
  let e : {y : S // direction x ⟨y.1,fun h => hx (h ▸ y.2)⟩=W} ≃ radialFiber S x W :=
    { toFun := fun y => ⟨y.1.1,by
        rw [mem_radialFiber]
        exact ⟨y.1.2,fun h => hx (h ▸ y.1.2),
          (direction_eq_iff x _ W).mp y.2⟩⟩
      invFun := fun y => ⟨⟨y.1,(mem_radialFiber S x y W).mp y.2 |>.1⟩,by
        apply (direction_eq_iff x _ W).mpr
        exact (mem_radialFiber S x y W).mp y.2 |>.2.2⟩
      left_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun y => by apply Subtype.ext; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PointScore
open Finset
open SharpLogRamsey.PoissonGrouping
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D : Type*} [Fintype A] [Fintype D]

def outsideBatchFiber {R : ℕ} (own center : A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (r : Fin R) (d : D) :
    {i : {i : Fin R × A // ¬held own center i} // outsideGroup own center g i=(r,d)} ≃
      {y : {y // ¬(own y ∨ center y)} // g y=d} where
  toFun i := ⟨⟨i.1.1.2,i.1.2⟩,congrArg Prod.snd i.2⟩
  invFun y := ⟨⟨(r,y.1.1),y.1.2⟩,Prod.ext rfl y.2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.fst i.2).symm rfl
  right_inv y := by rfl

omit [Fintype D] in
lemma outside_uniform_rate {R : ℕ} (own center : A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (u : ℝ≥0) (k : Fin R × D) :
    (∑ _i : {i : {i : Fin R × A // ¬held own center i} // outsideGroup own center g i=k},u)=
      u*Fintype.card {y : {y // ¬(own y ∨ center y)} // g y=k.2} := by
  simp only [sum_const,card_univ,nsmul_eq_mul]
  rw [Fintype.card_congr (outsideBatchFiber own center g k.1 k.2)]
  exact mul_comm _ _

end
end SharpLogRamsey.PointScore

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open SharpLogRamsey.PointScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def outsideDirection (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (y : {y : S // ¬(y.1∈O ∨ y.1=x)}) : RadialLine x :=
  direction x ⟨y.1.1,fun h => y.2 (Or.inr h)⟩

def outsideDirectionFiber (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) :
    {y : {y : S // ¬(y.1∈O ∨ y.1=x)} // outsideDirection S O x y=W} ≃
      radialFiber (S\(O∪{x})) x W where
  toFun y := ⟨y.1.1.1,by
    apply (mem_radialFiber _ _ _ _).mpr
    refine ⟨mem_sdiff.mpr ⟨y.1.1.2,?_⟩,fun h => y.1.2 (Or.inr h),?_⟩
    · simpa only [mem_union,mem_singleton] using y.1.2
    · exact (direction_eq_iff x _ W).mp y.2⟩
  invFun y := ⟨⟨⟨y.1,(mem_sdiff.mp ((mem_radialFiber _ _ _ _).mp y.2).1).1⟩,by
      simpa only [mem_union,mem_singleton] using
        (mem_sdiff.mp ((mem_radialFiber _ _ _ _).mp y.2).1).2⟩,by
    apply (direction_eq_iff x _ W).mpr
    exact ((mem_radialFiber _ _ _ _).mp y.2).2.2⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

omit [Finite K] in
lemma outsideDirection_card (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) :
    Fintype.card {y : {y : S // ¬(y.1∈O ∨ y.1=x)} // outsideDirection S O x y=W}=
      (radialFiber (S\(O∪{x})) x W).card :=
  (Fintype.card_congr (outsideDirectionFiber S O x W)).trans (Fintype.card_coe _)

lemma outsideDirection_incidence (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (H : Projectivization K (Module.Dual K V)) (hxH : x.submodule≤LinearMap.ker H.rep)
    (y : {y : S // ¬(y.1∈O ∨ y.1=x)}) :
    y.1.1.submodule≤LinearMap.ker H.rep ↔ outsideDirection S O x y∈lines x H :=
  by
    exact (direction_mem_lines x ⟨y.1.1,fun h => y.2 (Or.inr h)⟩ H hxH).symm

omit [Finite K] in
theorem actual_radial_rate (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    {R : ℕ} (L c : ℝ≥0) (k : Fin R × RadialLine x) :
    (∑ _i : {i : {i : Fin R × S // ¬held (fun y : S => y.1∈O) (fun y : S => y.1=x) i} //
      outsideGroup (fun y : S => y.1∈O) (fun y : S => y.1=x) (outsideDirection S O x) i=k},L*c)=
      L*(c*(radialFiber (S\(O∪{x})) x k.2).card) := by
  rw [outside_uniform_rate,mul_assoc]
  congr 2
  have hc := outsideDirection_card S O x k.2
  simp only [←Nat.card_eq_fintype_card] at hc ⊢
  exact_mod_cast hc

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
