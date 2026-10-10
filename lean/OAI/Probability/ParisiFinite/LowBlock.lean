import Mathlib
import OAI.Probability.ParisiFinite.GenericDegrees

namespace OAI

/-! Low Block. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def lowBlock (r : ℕ) (a : ℝ) : Set (OverlapBlock r) :=
  {T | ∀ i j, i≠j → (T i j:ℝ)≤a}

def lowEvent (r : ℕ) (a : ℝ) : Set OverlapArray := (blockOfArray r) ⁻¹' lowBlock r a

def lowBad (r : ℕ) (i : Fin r) (a : ℝ) : Set OverlapArray :=
  {R | R∈lowEvent r a ∧ a<(R i r:ℝ)}

lemma measurableSet_lowBlock (r : ℕ) (a : ℝ) : MeasurableSet (lowBlock r a) := by
  unfold lowBlock
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => measurableSet_le (by fun_prop) measurable_const

lemma lowEvent_one (a : ℝ) : lowEvent 1 a=Set.univ := by
  ext R
  simp [lowEvent, lowBlock]

lemma lowBad_GG {μ : ProbabilityMeasure OverlapArray} (h : GGIdentities μ)
    (r : ℕ) (i : Fin r) (a : ℝ) :
    (r:ℝ)*(μ : Measure OverlapArray).real (lowBad r i a)=
      (μ : Measure OverlapArray).real (lowEvent r a)*(entryLaw μ 0 1).real {x | a<(x:ℝ)} := by
  have he := GG_event_identity h r i (lowBlock r a) {x | a<(x:ℝ)}
    (measurableSet_lowBlock r a) (measurableSet_lt measurable_const (by fun_prop))
  have hz (l : Fin r) (hl : l∈Finset.univ.erase i) :
      {R | blockOfArray r R∈lowBlock r a ∧ a<(R i l:ℝ)}=(∅ : Set OverlapArray) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro R hR
    exact (not_lt_of_ge (hR.1 i l (Finset.ne_of_mem_erase hl).symm)) hR.2
  have hs : (∑ l∈Finset.univ.erase i, (μ : Measure OverlapArray).real
      {R | blockOfArray r R∈lowBlock r a ∧ a<(R i l:ℝ)})=0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [hz l hl,measureReal_empty]
  simp only [Set.mem_ofPred_eq] at he
  rw [hs,add_zero] at he
  exact he

lemma lowEvent_step_cover (r : ℕ) (a : ℝ) :
    lowEvent r a ⊆ (lowEvent (r+1) a ∪ ⋃ i, lowBad r i a) ∪ GramArraysᶜ := by
  classical
  intro R hR
  by_cases hG : R∈GramArrays
  · by_cases hb : ∃ i, R∈lowBad r i a
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr hb))
    · have hn (i : Fin r) : (R i r:ℝ)≤a := by
        by_contra hh
        exact hb ⟨i,hR,lt_of_not_ge hh⟩
      apply Or.inl ∘ Or.inl
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact False.elim (hij rfl)
        | cast j =>
          change (R r j:ℝ)≤a
          rw [hG.1 r j]
          exact hn j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact hn i
        | cast j => exact hR i j (fun h => hij (congrArg Fin.castSucc h))
  · exact Or.inr hG

lemma lowEvent_step_bound {μ : ProbabilityMeasure OverlapArray} (hG : (μ : Measure OverlapArray) GramArrays=1)
    (h : GGIdentities μ) {r : ℕ} (hr : 0<r) (a : ℝ) :
    (μ : Measure OverlapArray).real (lowEvent r a)*(entryLaw μ 0 1).real {x | (x:ℝ)≤a} ≤
      (μ : Measure OverlapArray).real (lowEvent (r+1) a) := by
  let ν : Measure OverlapArray := μ
  have hc : ν.real GramArraysᶜ=0 := by
    rw [measureReal_compl isClosed_GramArrays.measurableSet]
    simp [ν, measureReal_def, hG]
  have hh := measureReal_mono (μ:=ν) (lowEvent_step_cover r a)
  have hu := measureReal_union_le (μ:=ν) (lowEvent (r+1) a ∪ ⋃ i,lowBad r i a) GramArraysᶜ
  have hu' := measureReal_union_le (μ:=ν) (lowEvent (r+1) a) (⋃ i,lowBad r i a)
  have hs := measureReal_iUnion_fintype_le (μ:=ν) (fun i => lowBad r i a)
  have he : (∑ i : Fin r,ν.real (lowBad r i a))=
      ν.real (lowEvent r a)*(entryLaw μ 0 1).real {x | a<(x:ℝ)} := by
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hr.ne' : (r:ℝ)≠0)
    rw [Finset.mul_sum]
    simp_rw [show ∀ i : Fin r, (r:ℝ)*ν.real (lowBad r i a)=
        ν.real (lowEvent r a)*(entryLaw μ 0 1).real {x | a<(x:ℝ)} from fun i => lowBad_GG h r i a]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp : (entryLaw μ 0 1).real {x : OverlapEntry | (x:ℝ)≤a}+
      (entryLaw μ 0 1).real {x : OverlapEntry | a<(x:ℝ)}=1 := by
    let := entryLaw_probability μ 0 1
    have ht := measureReal_add_measureReal_compl (μ:=entryLaw μ 0 1) (s:={x : OverlapEntry | (x:ℝ)≤a})
      (measurableSet_le (by fun_prop : Measurable (fun x : OverlapEntry => (x:ℝ))) measurable_const)
    simpa only [Set.compl_ofPred, not_le, measureReal_def, measure_univ, ENNReal.toReal_one] using ht
  rw [he] at hs
  change ν.real (lowEvent r a)*(entryLaw μ 0 1).real {x | (x:ℝ)≤a} ≤ν.real (lowEvent (r+1) a)
  have hm := congrArg (fun x : ℝ => ν.real (lowEvent r a)*x) hp
  simp only [mul_add,mul_one] at hm
  linarith

lemma lowEvent_positive {μ : ProbabilityMeasure OverlapArray} (hG : (μ : Measure OverlapArray) GramArrays=1)
    (h : GGIdentities μ) (a : ℝ) (ha : 0<(entryLaw μ 0 1).real {x | (x:ℝ)≤a}) :
    ∀ r : ℕ, 0<(μ : Measure OverlapArray).real (lowEvent (r+1) a) := by
  intro r
  induction r with
  | zero => rw [Nat.zero_add,lowEvent_one]; simp
  | succ r ih => exact lt_of_lt_of_le (mul_pos ih ha) (lowEvent_step_bound hG h (Nat.succ_pos r) a)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma gram_clique_bound {R : OverlapArray} (hG : R∈GramArrays) {r : ℕ} {a : ℝ}
    (hl : R∈lowEvent (r+1) a) : 0≤1+(r:ℝ)*a := by
  have hr (i : Fin (r+1)) : (∑ j : Fin (r+1), (R i j:ℝ)) ≤ 1+(r:ℝ)*a := by
    calc
      _ = (∑ j∈Finset.univ.erase i, (R i j:ℝ))+(R i i:ℝ) :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
      _ ≤ (∑ j∈Finset.univ.erase i,a)+1 := by
        apply add_le_add
        · exact Finset.sum_le_sum (fun j hj => hl i j (Finset.ne_of_mem_erase hj).symm)
        · exact le_of_eq (hG.2.1 i)
      _ = _ := by simp; ring
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (r+1)))) => hr i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hp := hG.2.2 (r+1) (fun _ => 1)
  simp only [one_mul] at hp
  have hh' : 0≤((r+1:ℕ):ℝ)*(1+(r:ℝ)*a) := hp.trans hh
  have hp' : (0:ℝ)<(r+1:ℕ) := by positivity
  nlinarith

 
lemma exists_negative_clique_impossible {a : ℝ} (ha : a<0) :
    ∃ r : ℕ, lowEvent (r+1) a ⊆ GramArraysᶜ := by
  obtain ⟨r,hr⟩ := exists_nat_gt ((-1:ℝ)/a)
  refine ⟨r,fun R hl hG => ?_⟩
  have hg := gram_clique_bound hG hl
  have hh := (div_lt_iff_of_neg ha).mp hr
  linarith

 

theorem GG_negative_threshold_zero {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (h : GGIdentities μ) {a : ℝ} (ha : a<0) :
    (entryLaw μ 0 1).real {x | (x:ℝ)≤a}=0 := by
  by_contra hh
  have hp : 0<(entryLaw μ 0 1).real {x | (x:ℝ)≤a} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hh)
  obtain ⟨r,hr⟩ := exists_negative_clique_impossible ha
  have hc : (μ : Measure OverlapArray).real GramArraysᶜ=0 := by
    rw [measureReal_compl isClosed_GramArrays.measurableSet]
    simp [measureReal_def,hG]
  have he := measureReal_mono (μ:=(μ:Measure OverlapArray)) hr
  rw [hc] at he
  exact (not_lt_of_ge he) (lowEvent_positive hG h a hp r)

lemma GG_negative_overlap_zero {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (h : GGIdentities μ) :
    (entryLaw μ 0 1) {x | (x:ℝ)<0}=0 := by
  let Q := {q : ℚ // (q:ℝ)<0}
  have hz (q : Q) : (entryLaw μ 0 1) {x | (x:ℝ)≤(q.1:ℝ)}=0 :=
    (measureReal_eq_zero_iff).mp (GG_negative_threshold_zero hG h q.2)
  have hc : {x : OverlapEntry | (x:ℝ)<0} ⊆ ⋃ q : Q, {x | (x:ℝ)≤(q.1:ℝ)} := by
    intro x hx
    obtain ⟨q,hxq,hq⟩ := exists_rat_btwn (show (x:ℝ)<0 from hx)
    exact Set.mem_iUnion.mpr ⟨⟨q,hq⟩,le_of_lt hxq⟩
  exact measure_mono_null hc (measure_iUnion_null hz)

lemma GG_nonnegative_overlap {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (h : GGIdentities μ) :
    ∀ᵐ R ∂(μ : Measure OverlapArray), 0≤(R 0 1:ℝ) := by
  have he := GG_negative_overlap_zero hG h
  rw [entryLaw, Measure.map_apply (by fun_prop) (measurableSet_lt (by fun_prop) measurable_const)] at he
  apply ae_iff.mpr
  simpa only [Set.preimage_ofPred_eq, not_le] using he

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity

 

theorem urn_growth_contradiction {r : ℕ} (hr : 0<r) {z : ℝ} (hz : 0<z)
    (f : ℕ → ℝ) (hf : ∀ m, 0≤f m) (h₀ : 0<f 0)
    (hrec : ∀ m, ((r+m+1:ℕ):ℝ)*f (m+1)=(((r+m:ℕ):ℝ)+z)*f m)
    (hub : ∀ m, ((m+1:ℕ):ℝ)*f m≤1) : False := by
  let u : ℕ → ℝ := fun m => ((r+m:ℕ):ℝ)*f m
  have hu0 : 0<u 0 := by dsimp [u]; positivity
  have hus (m : ℕ) : u (m+1)=u m+z*f m := by
    dsimp [u]
    have he := hrec m
    push_cast at he ⊢
    nlinarith only [he]
  have hum : Monotone u := monotone_nat_of_le_succ fun m => by rw [hus]; nlinarith [hf m]
  have hub' (m : ℕ) : u m≤r := by
    have hh := hub m
    have hr' : (1:ℝ)≤r := by exact_mod_cast hr
    dsimp [u]
    push_cast at hh ⊢
    have hm : (r:ℝ)*m*f m≥(m:ℝ)*f m := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr' (Nat.cast_nonneg m)) (hf m)
    have hb := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg r)
    nlinarith only [hm,hb]
  have hs (k : ℕ) : u k=u 0+z*∑ m∈Finset.range k,f m := by
    induction k with
    | zero => simp
    | succ k ih => rw [hus,ih,Finset.sum_range_succ]; ring
  have hsum : Summable f := summable_of_sum_range_le hf (c:=(r:ℝ)/z) fun k => by
    apply (le_div_iff₀ hz).mpr
    have hh := hub' k
    rw [hs] at hh
    nlinarith
  have hl (m : ℕ) : (1:ℝ)/((m+r:ℕ):ℝ)≤f m/u 0 := by
    have hu := hum (Nat.zero_le m)
    have hp : (0:ℝ)<((m+r:ℕ):ℝ) := by positivity
    apply (div_le_div_iff₀ hp hu0).mpr
    change u 0≤((r+m:ℕ):ℝ)*f m at hu
    simpa only [one_mul,mul_one,Nat.add_comm,mul_comm] using hu
  have htail : Summable (fun m : ℕ => (1:ℝ)/((m+r:ℕ):ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hl (hsum.div_const (u 0))
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff r).mp htail)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def initialBlock {s t : ℕ} (h : s≤t) (T : OverlapBlock t) : OverlapBlock s :=
  fun i j => T (Fin.castLE h i) (Fin.castLE h j)

lemma continuous_initialBlock {s t : ℕ} (h : s≤t) : Continuous (initialBlock h) := by
  unfold initialBlock
  fun_prop

 
def rowSurvival (r m : ℕ) (D : Set (OverlapBlock (r+1))) (q : ℝ) : Set OverlapArray :=
  {R | blockOfArray (r+1) R∈D ∧ ∀ j : ℕ, j<r+m+1 → j≠r → (R r j:ℝ)≤q}

def survivalBlock (r m : ℕ) (D : Set (OverlapBlock (r+1))) (q : ℝ) : Set (OverlapBlock (r+m+1)) :=
  {T | initialBlock (show r+1≤r+m+1 by omega) T∈D ∧
    ∀ j : Fin (r+m+1), (j:ℕ)≠r → (T ⟨r,by omega⟩ j:ℝ)≤q}

lemma rowSurvival_eq_preimage (r m : ℕ) (D : Set (OverlapBlock (r+1))) (q : ℝ) :
    rowSurvival r m D q=(blockOfArray (r+m+1)) ⁻¹' survivalBlock r m D q := by
  ext R
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨h₁,h₂⟩
  · exact ⟨h₁,fun j hj => h₂ j j.isLt hj⟩
  · exact ⟨h₁,fun j hj hne => h₂ ⟨j,hj⟩ hne⟩

lemma measurableSet_survivalBlock (r m : ℕ) {D : Set (OverlapBlock (r+1))}
    (hD : MeasurableSet D) (q : ℝ) : MeasurableSet (survivalBlock r m D q) := by
  change MeasurableSet ((initialBlock (show r+1≤r+m+1 by omega)) ⁻¹' D ∩
    {T | ∀ j : Fin (r+m+1), (j:ℕ)≠r → (T ⟨r,by omega⟩ j:ℝ)≤q})
  apply MeasurableSet.inter (hD.preimage (continuous_initialBlock _).measurable)
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => measurableSet_le (by fun_prop) measurable_const

lemma measurableSet_rowSurvival (r m : ℕ) {D : Set (OverlapBlock (r+1))}
    (hD : MeasurableSet D) (q : ℝ) : MeasurableSet (rowSurvival r m D q) := by
  rw [rowSurvival_eq_preimage]
  exact (measurableSet_survivalBlock r m hD q).preimage (continuous_blockOfArray _).measurable

lemma rowSurvival_succ (r m : ℕ) (D : Set (OverlapBlock (r+1))) (q : ℝ) :
    rowSurvival r (m+1) D q={R | R∈rowSurvival r m D q ∧ (R r (r+m+1):ℝ)≤q} := by
  ext R
  constructor
  · rintro ⟨hD,h⟩
    exact ⟨⟨hD,fun j hj hne => h j (by omega) hne⟩,h (r+m+1) (by omega) (by omega)⟩
  · rintro ⟨⟨hD,h⟩,hn⟩
    refine ⟨hD,fun j hj hne => ?_⟩
    by_cases hh : j<r+m+1
    · exact h j hh hne
    · have he : j=r+m+1 := by omega
      simpa only [he] using hn

lemma rowSurvival_GG {μ : ProbabilityMeasure OverlapArray} (h : GGIdentities μ)
    (r m : ℕ) {D : Set (OverlapBlock (r+1))} (hD : MeasurableSet D) (q : ℝ) :
    ((r+m+1:ℕ):ℝ)*(μ : Measure OverlapArray).real (rowSurvival r (m+1) D q)=
      (((r+m:ℕ):ℝ)+(entryLaw μ 0 1).real {x | (x:ℝ)≤q})*
        (μ : Measure OverlapArray).real (rowSurvival r m D q) := by
  let i : Fin (r+m+1) := ⟨r,by omega⟩
  have he := GG_event_identity h (r+m+1) i (survivalBlock r m D q) {x | (x:ℝ)≤q}
    (measurableSet_survivalBlock r m hD q) (measurableSet_le (by fun_prop) measurable_const)
  have hz (l : Fin (r+m+1)) (hl : l∈Finset.univ.erase i) :
      {R | blockOfArray (r+m+1) R∈survivalBlock r m D q ∧ R i l∈{x : OverlapEntry | (x:ℝ)≤q}}=
        rowSurvival r m D q := by
    ext R
    have hh : blockOfArray (r+m+1) R∈survivalBlock r m D q ↔ R∈rowSurvival r m D q := by
      rw [rowSurvival_eq_preimage]; rfl
    constructor
    · exact fun hR => hh.mp hR.1
    · intro hR
      refine ⟨hh.mpr hR, hR.2 l l.isLt ?_⟩
      intro hc
      exact Finset.ne_of_mem_erase hl (Fin.ext hc)
  have hs : (∑ l∈Finset.univ.erase i,(μ : Measure OverlapArray).real
      {R | blockOfArray (r+m+1) R∈survivalBlock r m D q ∧ R i l∈{x : OverlapEntry | (x:ℝ)≤q}})=
        ((r+m:ℕ):ℝ)*(μ : Measure OverlapArray).real (rowSurvival r m D q) := by
    simp_rw [Finset.sum_congr rfl (fun l hl => congrArg (μ : Measure OverlapArray).real (hz l hl))]
    simp
  rw [hs,← rowSurvival_eq_preimage] at he
  have heSet : {R | blockOfArray (r+m+1) R∈survivalBlock r m D q ∧ R i (r+m+1)∈{x : OverlapEntry | (x:ℝ)≤q}}=
      rowSurvival r (m+1) D q := by
    rw [rowSurvival_succ, rowSurvival_eq_preimage r m]
    rfl
  rw [heSet] at he
  linarith

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def FiniteExchangeable (μ : ProbabilityMeasure OverlapArray) : Prop :=
  ∀ (r : ℕ) (e : Fin r → ℕ), Function.Injective e →
    (μ : Measure OverlapArray).map (selectedBlock e)=blockLaw μ r

lemma genericOverlap_limit_FiniteExchangeable (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ)) :
    FiniteExchangeable μ := genericOverlap_limit_exchangeable β hφ hμ

lemma exchangeable_event {μ : ProbabilityMeasure OverlapArray} (h : FiniteExchangeable μ)
    {r : ℕ} (e : Fin r → ℕ) (he : Function.Injective e) {B : Set (OverlapBlock r)} (hB : MeasurableSet B) :
    (μ : Measure OverlapArray) ((selectedBlock e) ⁻¹' B)=(μ : Measure OverlapArray) ((blockOfArray r) ⁻¹' B) := by
  have hh := congrArg (fun ν : Measure (OverlapBlock r) => ν B) (h r e he)
  rw [Measure.map_apply (continuous_selectedBlock e).measurable hB,
    blockLaw, Measure.map_apply (continuous_blockOfArray r).measurable hB] at hh
  exact hh

lemma exchangeable_event_real {μ : ProbabilityMeasure OverlapArray} (h : FiniteExchangeable μ)
    {r : ℕ} (e : Fin r → ℕ) (he : Function.Injective e) {B : Set (OverlapBlock r)} (hB : MeasurableSet B) :
    (μ : Measure OverlapArray).real ((selectedBlock e) ⁻¹' B)=
      (μ : Measure OverlapArray).real ((blockOfArray r) ⁻¹' B) :=
  congrArg ENNReal.toReal (exchangeable_event h e he hB)

def tailPerm (r : ℕ) {k : ℕ} (q : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (r+k)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin r)) q).trans finSumFinEquiv)

@[simp] lemma tailPerm_old (r : ℕ) {k : ℕ} (q : Equiv.Perm (Fin k)) (i : Fin r) :
    tailPerm r q (Fin.castAdd k i)=Fin.castAdd k i := by simp [tailPerm]

@[simp] lemma tailPerm_new (r : ℕ) {k : ℕ} (q : Equiv.Perm (Fin k)) (i : Fin k) :
    tailPerm r q (Fin.natAdd r i)=Fin.natAdd r (q i) := by simp [tailPerm]

def newRow {r k : ℕ} (T : OverlapBlock (r+k)) (j : Fin k) : Fin r → OverlapEntry :=
  fun i => T (Fin.natAdd r j) (Fin.castAdd k i)

lemma continuous_newRow {r k : ℕ} (j : Fin k) : Continuous (fun T : OverlapBlock (r+k) => newRow T j) := by
  unfold newRow
  fun_prop

 
def uniqueMark (r k : ℕ) (B : Set (Fin r → OverlapEntry)) (j : Fin k) : Set (OverlapBlock (r+k)) :=
  {T | newRow T j∈B ∧ ∀ l : Fin k, l≠j → newRow T l∉B}

lemma measurableSet_uniqueMark (r k : ℕ) {B : Set (Fin r → OverlapEntry)} (hB : MeasurableSet B) (j : Fin k) :
    MeasurableSet (uniqueMark r k B j) := by
  change MeasurableSet ((fun T : OverlapBlock (r+k) => newRow T j) ⁻¹' B ∩
    {T | ∀ l : Fin k, l≠j → newRow T l∉B})
  apply MeasurableSet.inter (hB.preimage (continuous_newRow j).measurable)
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    (hB.preimage (continuous_newRow l).measurable).compl

lemma uniqueMark_disjoint (r k : ℕ) (B : Set (Fin r → OverlapEntry)) :
    Pairwise (fun i j => Disjoint ((blockOfArray (r+k)) ⁻¹' uniqueMark r k B i) ((blockOfArray (r+k)) ⁻¹' uniqueMark r k B j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro R hi hj
  exact hi.2 j hij.symm hj.1

lemma uniqueMark_relabel {r k : ℕ} (B : Set (Fin r → OverlapEntry)) (q : Equiv.Perm (Fin k)) (j : Fin k) :
    (selectedBlock (fun i : Fin (r+k) => (tailPerm r q i:ℕ))) ⁻¹' uniqueMark r k B j=
      (blockOfArray (r+k)) ⁻¹' uniqueMark r k B (q j) := by
  ext R
  have he (l : Fin k) : newRow (selectedBlock (fun i : Fin (r+k) => (tailPerm r q i:ℕ)) R) l=
      newRow (blockOfArray (r+k) R) (q l) := by
    funext i
    simp only [newRow,selectedBlock,tailPerm_old,tailPerm_new,blockOfArray]
  change (_ ∧ _) ↔ (_ ∧ _)
  simp_rw [he]
  constructor
  · rintro ⟨hj,hh⟩
    refine ⟨hj,fun l hl => ?_⟩
    have hl' : q.symm l≠j := fun h => hl (by simpa using congrArg q h)
    simpa only [q.apply_symm_apply] using hh (q.symm l) hl'
  · rintro ⟨hj,hh⟩
    exact ⟨hj,fun l hl => hh (q l) (fun he => hl (q.injective he))⟩

lemma uniqueMark_equal {μ : ProbabilityMeasure OverlapArray} (h : FiniteExchangeable μ)
    (r k : ℕ) {B : Set (Fin r → OverlapEntry)} (hB : MeasurableSet B) (i j : Fin k) :
    (μ : Measure OverlapArray).real ((blockOfArray (r+k)) ⁻¹' uniqueMark r k B i)=
      (μ : Measure OverlapArray).real ((blockOfArray (r+k)) ⁻¹' uniqueMark r k B j) := by
  let q : Equiv.Perm (Fin k) := Equiv.swap j i
  have hh := exchangeable_event_real h (fun l : Fin (r+k) => (tailPerm r q l:ℕ))
    (Fin.val_injective.comp (tailPerm r q).injective) (measurableSet_uniqueMark r k hB j)
  rw [uniqueMark_relabel] at hh
  simpa [q] using hh

lemma uniqueMark_bound {μ : ProbabilityMeasure OverlapArray} (h : FiniteExchangeable μ)
    (r k : ℕ) {B : Set (Fin r → OverlapEntry)} (hB : MeasurableSet B) (i : Fin k) :
    (k:ℝ)*(μ : Measure OverlapArray).real ((blockOfArray (r+k)) ⁻¹' uniqueMark r k B i)≤1 := by
  have hh := measureReal_iUnion_fintype (μ:=(μ:Measure OverlapArray))
    (uniqueMark_disjoint r k B) (fun j => (measurableSet_uniqueMark r k hB j).preimage (continuous_blockOfArray _).measurable)
  have he : (∑ j : Fin k, (μ : Measure OverlapArray).real ((blockOfArray (r+k)) ⁻¹' uniqueMark r k B j))=
      (k:ℝ)*(μ : Measure OverlapArray).real ((blockOfArray (r+k)) ⁻¹' uniqueMark r k B i) := by
    simp_rw [uniqueMark_equal h r k hB _ i]
    simp
  rw [he] at hh
  rw [← hh]
  exact measureReal_le_one

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def arrayRow (r j : ℕ) (R : OverlapArray) : Fin r → OverlapEntry := fun i => R j i

lemma continuous_arrayRow (r j : ℕ) : Continuous (arrayRow r j) := by
  unfold arrayRow
  fun_prop

def patternBlock (r : ℕ) (C : Set (OverlapBlock r)) (B : Set (Fin r → OverlapEntry)) :
    Set (OverlapBlock (r+1)) :=
  {T | initialBlock (Nat.le_succ r) T∈C ∧ newRow T (0 : Fin 1)∈B}

lemma measurableSet_patternBlock {r : ℕ} {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (hC : MeasurableSet C) (hB : MeasurableSet B) : MeasurableSet (patternBlock r C B) :=
  (hC.preimage (continuous_initialBlock _).measurable).inter
    (hB.preimage (continuous_newRow _).measurable)

@[simp] lemma patternBlock_preimage (r : ℕ) (C : Set (OverlapBlock r)) (B : Set (Fin r → OverlapEntry)) :
    (blockOfArray (r+1)) ⁻¹' patternBlock r C B=
      {R | blockOfArray r R∈C ∧ arrayRow r r R∈B} := by
  rfl

def doubleMarkBlock (r : ℕ) (C : Set (OverlapBlock r)) (B : Set (Fin r → OverlapEntry)) (q : ℝ) :
    Set (OverlapBlock (r+2)) :=
  {T | initialBlock (by omega : r≤r+2) T∈C ∧ newRow T (0 : Fin 2)∈B ∧
    newRow T (1 : Fin 2)∈B ∧ (T ⟨r,by omega⟩ ⟨r+1,by omega⟩:ℝ)≤q}

lemma measurableSet_doubleMarkBlock {r : ℕ} {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (hC : MeasurableSet C) (hB : MeasurableSet B) (q : ℝ) : MeasurableSet (doubleMarkBlock r C B q) := by
  exact (hC.preimage (continuous_initialBlock _).measurable).inter
    ((hB.preimage (continuous_newRow _).measurable).inter
      ((hB.preimage (continuous_newRow _).measurable).inter (measurableSet_le (f := fun T : OverlapBlock (r+2) => (T ⟨r,by omega⟩ ⟨r+1,by omega⟩:ℝ)) (by fun_prop) measurable_const)))

def doubleMarkAt (r j : ℕ) (C : Set (OverlapBlock r)) (B : Set (Fin r → OverlapEntry)) (q : ℝ) :
    Set OverlapArray :=
  {R | blockOfArray r R∈C ∧ arrayRow r r R∈B ∧ arrayRow r j R∈B ∧ (R r j:ℝ)≤q}

lemma measurableSet_doubleMarkAt {r j : ℕ} {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (hC : MeasurableSet C) (hB : MeasurableSet B) (q : ℝ) : MeasurableSet (doubleMarkAt r j C B q) := by
  exact (hC.preimage (continuous_blockOfArray _).measurable).inter
    ((hB.preimage (continuous_arrayRow _ _).measurable).inter
      ((hB.preimage (continuous_arrayRow _ _).measurable).inter (measurableSet_le (f := fun R : OverlapArray => (R r j:ℝ)) (by fun_prop) measurable_const)))

def prefixFresh (s j : ℕ) : Fin (s+1) → ℕ := fun i => if (i:ℕ)<s then i else j

lemma prefixFresh_injective {s j : ℕ} (hj : s≤j) : Function.Injective (prefixFresh s j) := by
  intro a b h
  unfold prefixFresh at h
  split_ifs at h with ha hb hb
  · exact Fin.ext h
  · omega
  · omega
  · apply Fin.ext; omega

@[simp] lemma prefixFresh_old {s j : ℕ} (i : Fin s) : prefixFresh s j i.castSucc=i := by
  simp [prefixFresh,i.isLt]

@[simp] lemma prefixFresh_last (s j : ℕ) : prefixFresh s j (Fin.last s)=j := by simp [prefixFresh]

lemma doubleMarkAt_preimage (r j : ℕ) (C : Set (OverlapBlock r)) (B : Set (Fin r → OverlapEntry)) (q : ℝ) :
    (selectedBlock (prefixFresh (r+1) j)) ⁻¹' doubleMarkBlock r C B q=doubleMarkAt r j C B q := by
  have he (i : ℕ) (hi : i<r+1) : prefixFresh (r+1) j ⟨i,by omega⟩=i := by simp [prefixFresh,hi]
  ext R
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  have h₁ : initialBlock (show r≤r+2 by omega) (selectedBlock (prefixFresh (r+1) j) R)=blockOfArray r R := by
    funext a b
    simp [initialBlock,selectedBlock,blockOfArray, prefixFresh,show (a:ℕ)<r+1 by omega,show (b:ℕ)<r+1 by omega]
  have h₂ : newRow (r:=r) (k:=2) (selectedBlock (prefixFresh (r+1) j) R) (0:Fin 2)=arrayRow r r R := by
    funext i
    simp [newRow,selectedBlock,arrayRow,prefixFresh,show (i:ℕ)<r+1 by omega]
  have h₃ : newRow (r:=r) (k:=2) (selectedBlock (prefixFresh (r+1) j) R) (1:Fin 2)=arrayRow r j R := by
    funext i
    simp [newRow,selectedBlock,arrayRow,prefixFresh,show (i:ℕ)<r+1 by omega]
  simp only [h₁,h₂,h₃,selectedBlock,he r (by omega)]
  simp [prefixFresh]

lemma doubleMarkAt_equal {μ : ProbabilityMeasure OverlapArray} (hex : FiniteExchangeable μ)
    {r j : ℕ} (hj : r+1≤j) {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (hC : MeasurableSet C) (hB : MeasurableSet B) (q : ℝ) :
    (μ : Measure OverlapArray) (doubleMarkAt r j C B q)=
      (μ : Measure OverlapArray) (doubleMarkAt r (r+1) C B q) := by
  have hh := exchangeable_event hex (prefixFresh (r+1) j) (prefixFresh_injective hj)
    (measurableSet_doubleMarkBlock hC hB q)
  rw [doubleMarkAt_preimage] at hh
  exact hh

lemma rowSurvival_zero (r : ℕ) {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (q : ℝ) (hB : ∀ x∈B, ∀ i, (x i:ℝ)≤q) :
    rowSurvival r 0 (patternBlock r C B) q=(blockOfArray (r+1)) ⁻¹' patternBlock r C B := by
  ext R
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h,fun j hj hne => ?_⟩
    have hb : arrayRow r r R∈B := h.2
    exact hB _ hb ⟨j,by omega⟩

 

theorem GG_duplication {μ : ProbabilityMeasure OverlapArray} (hgg : GGIdentities μ)
    (hex : FiniteExchangeable μ) {r : ℕ} (hr : 0<r)
    {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (hC : MeasurableSet C) (hB : MeasurableSet B) (q : ℝ)
    (hrow : ∀ x∈B, ∀ i, (x i:ℝ)≤q)
    (hz : 0<(entryLaw μ 0 1).real {x | (x:ℝ)≤q})
    (hpos : 0<(μ : Measure OverlapArray).real ((blockOfArray (r+1)) ⁻¹' patternBlock r C B)) :
    0<(μ : Measure OverlapArray).real (doubleMarkAt r (r+1) C B q) := by
  by_contra hn
  have hzero : (μ : Measure OverlapArray) (doubleMarkAt r (r+1) C B q)=0 := by
    apply (measureReal_eq_zero_iff).mp
    exact le_antisymm (le_of_not_gt hn) measureReal_nonneg
  have hall : ∀ᵐ R ∂(μ : Measure OverlapArray), ∀ j : ℕ, r+1≤j → R∉doubleMarkAt r j C B q := by
    apply eventually_countable_forall.mpr
    intro j
    by_cases hj : r+1≤j
    · have hzj : (μ : Measure OverlapArray) (doubleMarkAt r j C B q)=0 := by
        rw [doubleMarkAt_equal hex hj hC hB q,hzero]
      have ha : ∀ᵐ R ∂(μ : Measure OverlapArray), R∉doubleMarkAt r j C B q := by
        apply ae_iff.mpr
        simpa only [not_not,Set.ofPred_mem_eq] using hzj
      exact ha.mono fun R hR _ => hR
    · exact Filter.Eventually.of_forall fun _ h => (hj h).elim
  let f : ℕ → ℝ := fun m => (μ : Measure OverlapArray).real (rowSurvival r m (patternBlock r C B) q)
  have h₀ : 0<f 0 := by
    dsimp [f]
    rw [rowSurvival_zero r q hrow]
    exact hpos
  have hrec : ∀ m, ((r+m+1:ℕ):ℝ)*f (m+1)=
      (((r+m:ℕ):ℝ)+(entryLaw μ 0 1).real {x | (x:ℝ)≤q})*f m :=
    fun m => rowSurvival_GG hgg r m (measurableSet_patternBlock hC hB) q
  have hub (m : ℕ) : ((m+1:ℕ):ℝ)*f m≤1 := by
    have hs : ∀ᵐ R ∂(μ : Measure OverlapArray), R∈rowSurvival r m (patternBlock r C B) q →
        R∈(blockOfArray (r+(m+1))) ⁻¹' uniqueMark r (m+1) B 0 := by
      filter_upwards [hall] with R hR hsur
      refine ⟨hsur.1.2,fun j hj hBj => ?_⟩
      have hj' : r+1≤r+(j:ℕ) := by
        have : (j:ℕ)≠0 := fun he => hj (Fin.ext he)
        omega
      apply hR (r+j) hj'
      exact ⟨hsur.1.1,hsur.1.2,hBj,hsur.2 (r+j) (by omega) (by omega)⟩
    have hm : f m≤(μ : Measure OverlapArray).real
        ((blockOfArray (r+(m+1))) ⁻¹' uniqueMark r (m+1) B 0) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    exact (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans (uniqueMark_bound hex r (m+1) hB 0)
  exact urn_growth_contradiction hr hz f (fun _ => measureReal_nonneg) h₀ hrec hub

lemma exchangeable_pair_event {μ : ProbabilityMeasure OverlapArray} (hex : FiniteExchangeable μ)
    {i j : ℕ} (hij : i≠j) {A : Set OverlapEntry} (hA : MeasurableSet A) :
    (μ : Measure OverlapArray).real {R | R i j∈A}=(entryLaw μ 0 1).real A := by
  let e : Fin 2 → ℕ := ![i,j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hij hab).elim
    · exact (hij hab.symm).elim
    · rfl
  have hh := exchangeable_event_real hex e he (hA.preimage (show Measurable (fun T : OverlapBlock 2 => T 0 1) by fun_prop))
  change (μ : Measure OverlapArray).real {R | R i j∈A}=(μ : Measure OverlapArray).real {R | R 0 1∈A} at hh
  rw [hh,measureReal_def,measureReal_def,entryLaw,Measure.map_apply (by fun_prop) hA]
  rfl

 
theorem GG_duplication_of_positive {μ : ProbabilityMeasure OverlapArray} (hgg : GGIdentities μ)
    (hex : FiniteExchangeable μ) {r : ℕ} (hr : 0<r)
    {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (hC : MeasurableSet C) (hB : MeasurableSet B) (q : ℝ)
    (hrow : ∀ x∈B, ∀ i, (x i:ℝ)≤q)
    (hpos : 0<(μ : Measure OverlapArray).real ((blockOfArray (r+1)) ⁻¹' patternBlock r C B)) :
    0<(μ : Measure OverlapArray).real (doubleMarkAt r (r+1) C B q) := by
  have hs : (blockOfArray (r+1)) ⁻¹' patternBlock r C B ⊆ {R : OverlapArray | (R r 0:ℝ)≤q} := by
    intro R hR
    exact hrow _ hR.2 ⟨0,hr⟩
  have hh := hpos.trans_le (measureReal_mono hs)
  have he := exchangeable_pair_event hex (by omega : r≠0)
    (A:={x : OverlapEntry | (x:ℝ)≤q}) (measurableSet_le (by fun_prop) measurable_const)
  change (μ : Measure OverlapArray).real {R | (R r 0:ℝ)≤q}=_ at he
  rw [he] at hh
  exact GG_duplication hgg hex hr hC hB q hrow hh hpos

end SKCavity

end

end OAI
