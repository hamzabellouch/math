import Mathlib
import OAI.Probability.ParisiFinite.OrderedCode

namespace OAI

/-! Branch Numerator. -/

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
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def branchNumerator {r : ℕ} (a b : ℝ) (c : Fin r → ℕ) : ℝ :=
  branchFactor a b (codeLabels c).card * ∏ x∈codeLabels c,blockFactor a (labelCount c x)

lemma branchNumerator_existing {r : ℕ} (a b : ℝ) (c : Fin (r+1) → ℕ) (i : Fin r)
    (hi : restrictCode c i=c (Fin.last r)) :
    branchNumerator a b c=
      ((clusterCount (restrictCode c) i:ℝ)-a)*branchNumerator a b (restrictCode c) := by
  let x := c (Fin.last r)
  have hx : x∈codeLabels (restrictCode c) := (codeLabels_mem _ _).mpr ⟨i,hi⟩
  have hlabels : codeLabels c=codeLabels (restrictCode c) := by
    rw [codeLabels_succ,Finset.insert_eq_of_mem hx]
  have hcount : labelCount (restrictCode c) x=clusterCount (restrictCode c) i := by
    change labelCount (restrictCode c) (c (Fin.last r))=_
    rw [← hi]
    rfl
  have hprod : (∏ y∈codeLabels c,blockFactor a (labelCount c y))=
      (((clusterCount (restrictCode c) i:ℝ)-a))*
        ∏ y∈codeLabels (restrictCode c),blockFactor a (labelCount (restrictCode c) y) := by
    rw [hlabels,← Finset.mul_prod_erase _ _ hx,← Finset.mul_prod_erase _ _ hx]
    have he : (∏ y∈(codeLabels (restrictCode c)).erase x,blockFactor a (labelCount c y))=
        ∏ y∈(codeLabels (restrictCode c)).erase x,blockFactor a (labelCount (restrictCode c) y) := by
      apply Finset.prod_congr rfl
      intro y hy
      rw [labelCount_succ,ite_eq_right (Ne.symm (Finset.mem_erase.mp hy).1),add_zero]
    rw [he,labelCount_succ,ite_eq_left rfl,hcount,blockFactor_succ a (clusterCount_pos _ i)]
    ring
  unfold branchNumerator
  rw [hprod,hlabels]
  ring

lemma branchNumerator_fresh {r : ℕ} (hr : 0<r) (a b : ℝ) (c : Fin (r+1) → ℕ)
    (hi : ∀ i, restrictCode c i≠c (Fin.last r)) :
    branchNumerator a b c= (a*((codeLabels (restrictCode c)).card:ℝ)-b)*
      branchNumerator a b (restrictCode c) := by
  let x := c (Fin.last r)
  have hx : x∉codeLabels (restrictCode c) := by
    simpa only [codeLabels_mem,not_exists] using hi
  have hz : labelCount (restrictCode c) x=0 := by
    simpa only [← labelCount_pos_iff,not_lt,Nat.le_zero] using hx
  have hold : ∀ y∈codeLabels (restrictCode c),labelCount c y=labelCount (restrictCode c) y := by
    intro y hy
    have hyx : x≠y := fun h => hx (h ▸ hy)
    rw [labelCount_succ,ite_eq_right hyx,add_zero]
  unfold branchNumerator
  rw [codeLabels_succ,Finset.card_insert_of_notMem hx,
    branchFactor_succ a b (Finset.card_pos.mpr (codeLabels_nonempty hr _)),Finset.prod_insert hx]
  have hn : labelCount c x=1 := by rw [labelCount_succ,hz,ite_eq_left rfl,zero_add]
  rw [hn,blockFactor_one,one_mul]
  have he := Finset.prod_congr (s₁:=codeLabels (restrictCode c)) (s₂:=codeLabels (restrictCode c))
    rfl (fun y hy => congrArg (blockFactor a) (hold y hy))
  rw [he]
  ring

lemma branchNumerator_one (a b : ℝ) (c : Fin 1 → ℕ) : branchNumerator a b c=1 := by
  have hc : codeLabels c={c 0} := by
    ext x
    simp only [codeLabels_mem,Finset.mem_singleton]
    exact ⟨fun ⟨i,hi⟩ => by fin_cases i; exact hi.symm,fun h => ⟨0,h.symm⟩⟩
  have hn : labelCount c (c 0)=1 := by simp [labelCount,Finset.filter_singleton]
  simp [branchNumerator,hc,hn]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def branchEvent {r : ℕ} (c : Fin r → ℕ) (q t : ℝ) : Set OverlapArray :=
  partitionEvent (fun _ : Fin r => 0) q∩partitionEvent c t

def branchBlock {r : ℕ} (c : Fin r → ℕ) (q t : ℝ) : Set (OverlapBlock r) :=
  partitionBlock (fun _ => 0) q∩partitionBlock c t

lemma branchBlock_measurable {r : ℕ} (c : Fin r → ℕ) (q t : ℝ) :
    MeasurableSet (branchBlock c q t) :=
  (measurableSet_partitionBlock _ _).inter (measurableSet_partitionBlock _ _)

lemma branch_existing_iff {r : ℕ} (c : Fin (r+1) → ℕ) {q t : ℝ}
    (hqt : q≤t) (ht : t<1) (i : Fin r) (hi : restrictCode c i=c (Fin.last r))
    {R : OverlapArray} (hG : R∈GramArrays) (hu : R∈UltrametricArrays) :
    R∈branchEvent c q t ↔ R∈branchEvent (restrictCode c) q t ∧ t<(R i r:ℝ) := by
  unfold branchEvent
  rw [Set.mem_inter_iff,partition_existing_iff c ht i hi hG hu,
    partition_existing_iff (fun _ => 0) (hqt.trans_lt ht) i rfl hG hu]
  change (_ ∧ q<(R i r:ℝ)) ∧ _ ∧ t<(R i r:ℝ) ↔ (_ ∧ _) ∧ t<(R i r:ℝ)
  constructor
  · exact fun h => ⟨⟨h.1.1,h.2.1⟩,h.2.2⟩
  · exact fun h => ⟨⟨h.1.1,hqt.trans_lt h.2⟩,h.1.2,h.2⟩

lemma reps_row_le {r : ℕ} {c : Fin r → ℕ} {T : Finset (Fin r)} (hT : ClusterReps c T)
    {t : ℝ} {R : OverlapArray} (hG : R∈GramArrays) (hu : R∈UltrametricArrays)
    (hc : R∈partitionEvent c t) : (∀ i : Fin r,(R i r:ℝ)≤t) ↔ ∀ k∈T,(R k r:ℝ)≤t := by
  refine ⟨fun h k _ => h k,fun h i => ?_⟩
  by_contra hn
  have hi : t<(R i r:ℝ) := lt_of_not_ge hn
  obtain ⟨k,hk,hki⟩ := hT.2 i
  have hki' : t<(R k i:ℝ) := (hc k i).mpr hki
  have hh := hu k r i
  rw [hG.1 r i] at hh
  exact (not_lt_of_ge (h k hk)) ((lt_min hki' hi).trans_le hh)

lemma branch_fresh_iff {r : ℕ} (c : Fin (r+1) → ℕ) {q t : ℝ}
    (hqt : q≤t) (ht : t<1) (i : Fin r) (hi : ∀ j,restrictCode c j≠c (Fin.last r))
    {T : Finset (Fin r)} (hT : ClusterReps (restrictCode c) T)
    {R : OverlapArray} (hG : R∈GramArrays) (hu : R∈UltrametricArrays) :
    R∈branchEvent c q t ↔ R∈branchEvent (restrictCode c) q t ∧ q<(R i r:ℝ) ∧
      ∀ k∈T,(R k r:ℝ)≤t := by
  unfold branchEvent
  rw [Set.mem_inter_iff,partition_fresh_iff c ht hi hG,
    partition_existing_iff (fun _ => 0) (hqt.trans_lt ht) i rfl hG hu]
  constructor
  · rintro ⟨⟨hP,hq⟩,hC,hrow⟩
    exact ⟨⟨hP,hC⟩,hq,(reps_row_le hT hG hu hC).mp hrow⟩
  · rintro ⟨⟨hP,hC⟩,hq,hrow⟩
    exact ⟨⟨hP,hq⟩,hC,(reps_row_le hT hG hu hC).mpr hrow⟩

lemma GG_branch_existing {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {r : ℕ} (c : Fin (r+1) → ℕ) {q t : ℝ} (hqt : q≤t) (ht : t<1) (i : Fin r)
    (hi : restrictCode c i=c (Fin.last r)) :
    (r:ℝ)*(μ:Measure OverlapArray).real (branchEvent c q t)=
      ((clusterCount (restrictCode c) i:ℝ)-overlapDiscount μ t)*
        (μ:Measure OverlapArray).real (branchEvent (restrictCode c) q t) := by
  have he : branchEvent c q t =ᵐ[(μ:Measure OverlapArray)]
      {R | R∈branchEvent (restrictCode c) q t ∧ t<(R i r:ℝ)} := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG,
      ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu] with R hg hu
    exact propext (branch_existing_iff c hqt ht i hi hg hu)
  rw [measureReal_congr he]
  exact GG_join_on_block hgg (branchBlock_measurable _ q t) (restrictCode c) t (fun _ h => h.2) i

lemma GG_branch_fresh {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {r : ℕ} (c : Fin (r+1) → ℕ) {q t : ℝ} (hqt : q≤t) (ht : t<1) (i : Fin r)
    (hi : ∀ j,restrictCode c j≠c (Fin.last r))
    {T : Finset (Fin r)} (hT : ClusterReps (restrictCode c) T) :
    (r:ℝ)*(μ:Measure OverlapArray).real (branchEvent c q t)=
      ((T.card:ℝ)*overlapDiscount μ t-overlapDiscount μ q)*
        (μ:Measure OverlapArray).real (branchEvent (restrictCode c) q t) := by
  have he : branchEvent c q t =ᵐ[(μ:Measure OverlapArray)]
      {R | R∈branchEvent (restrictCode c) q t ∧ q<(R i r:ℝ) ∧ ∀ k∈T,(R k r:ℝ)≤t} := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG,
      ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu] with R hg hu
    exact propext (branch_fresh_iff c hqt ht i hi hT hg hu)
  rw [measureReal_congr he]
  have hp : ParentReps (fun _ : Fin r => 0) (restrictCode c) i T := by
    refine ⟨hT.1,fun _ _ => rfl,fun j => ?_⟩
    simp only [iff_true_left]
    exact hT.2 j
  exact GG_nested_innovation hG hgg hu (branchBlock_measurable _ q t) hqt
    (fun _ h => h.1) (fun _ h => h.2) i hp

lemma branch_one_real {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1)
    (c : Fin 1 → ℕ) {q t : ℝ} (hqt : q≤t) (ht : t<1) :
    (μ:Measure OverlapArray).real (branchEvent c q t)=1 := by
  have he : branchEvent c q t =ᵐ[(μ:Measure OverlapArray)] partitionEvent c t := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG] with R hg
    apply propext
    refine ⟨fun h => h.2,fun h => ⟨?_,h⟩⟩
    intro i j
    fin_cases i; fin_cases j
    change q<(R 0 0:ℝ) ↔ _
    rw [hg.2.1]
    simp [hqt.trans_lt ht]
  rw [measureReal_congr he,partition_one_real hG c ht]

 

theorem GG_branch_EPPF {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q t : ℝ} (hqt : q≤t) (ht : t<1) {r : ℕ} (hr : 0<r) (c : Fin r → ℕ) :
    ((r-1).factorial:ℝ)*(μ:Measure OverlapArray).real (branchEvent c q t)=
      branchNumerator (overlapDiscount μ t) (overlapDiscount μ q) c := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=0
    · subst r
      rw [branch_one_real hG c hqt ht,branchNumerator_one]
      norm_num
    have hr' : 0<r := Nat.pos_of_ne_zero hr0
    have hold := ih hr' (restrictCode c)
    have hf : (r.factorial:ℝ)=(r:ℝ)*((r-1).factorial:ℝ) := by
      exact_mod_cast (Nat.mul_factorial_pred hr0).symm
    simp only [Nat.add_sub_cancel] at *
    by_cases hc : ∃ i,restrictCode c i=c (Fin.last r)
    · obtain ⟨i,hi⟩ := hc
      rw [branchNumerator_existing _ _ c i hi,hf]
      have he := GG_branch_existing hG hgg hu c hqt ht i hi
      linear_combination ((r-1).factorial:ℝ)*he+
        ((clusterCount (restrictCode c) i:ℝ)-overlapDiscount μ t)*hold
    · have hc' : ∀ i,restrictCode c i≠c (Fin.last r) := not_exists.mp hc
      obtain ⟨T,hT⟩ := exists_clusterReps (restrictCode c)
      rw [branchNumerator_fresh hr' _ _ c hc',hf]
      have he := GG_branch_fresh hG hgg hu c hqt ht ⟨0,hr'⟩ hc' hT
      rw [hT.card_codeLabels] at he
      linear_combination ((r-1).factorial:ℝ)*he+
        (overlapDiscount μ t*((codeLabels (restrictCode c)).card:ℝ)-overlapDiscount μ q)*hold

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma branchNumerator_ordered {r : ℕ} (a b : ℝ) (c : OrderedFinpartition r) :
    branchNumerator a b (orderedCode c)=
      branchFactor a b c.length*∏ i,blockFactor a (c.partSize i) := by
  unfold branchNumerator
  rw [codeLabels_orderedCode,Finset.card_range,← Fin.prod_univ_eq_prod_range]
  simp_rw [labelCount_orderedCode]

def branchMarkedMoment (μ : ProbabilityMeasure OverlapArray) (q t : ℝ)
    (moments : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition r,(μ:Measure OverlapArray).real (branchEvent (orderedCode c) q t)*
    ∏ j,moments (c.partSize j)

variable {ι : Type*} [Fintype ι]

 

theorem GG_marked_power_derivative {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q t : ℝ} (hqt : q≤t) (ht : t<1) (ha : overlapDiscount μ t≠0)
    (w x : ι → ℝ) (hw : ∑ i,w i=1) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun z => (finiteMarkTransform (overlapDiscount μ t) w x z)^
      (overlapDiscount μ q/overlapDiscount μ t)) 0=
      -overlapDiscount μ q*((n-1).factorial:ℝ)*branchMarkedMoment μ q t (finiteMarkMoment w x) n := by
  rw [power_mark_derivative ha _ w x hw hn]
  unfold branchMarkedMoment
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have he := GG_branch_EPPF hG hgg hu hqt ht hn (orderedCode c)
  rw [branchNumerator_ordered] at he
  rw [Finset.prod_mul_distrib]
  linear_combination (overlapDiscount μ q)*(∏ j,finiteMarkMoment w x (c.partSize j))*he

lemma branchMarkedMoment_nonneg (μ : ProbabilityMeasure OverlapArray) (q t : ℝ)
    {moments : ℕ → ℝ} (hm : ∀ n,0 ≤ moments n) (n : ℕ) :
    0≤branchMarkedMoment μ q t moments n := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg measureReal_nonneg (Finset.prod_nonneg fun _ _ => hm _)

lemma branchMarkedMoment_le_ordered (μ : ProbabilityMeasure OverlapArray) (q t : ℝ)
    {moments : ℕ → ℝ} (hm : ∀ n,0 ≤ moments n) (n : ℕ) :
    branchMarkedMoment μ q t moments n≤orderedMarkedMoment μ t moments n := by
  apply Finset.sum_le_sum
  intro c _
  exact mul_le_mul_of_nonneg_right (measureReal_mono Set.inter_subset_right)
    (Finset.prod_nonneg fun _ _ => hm _)

lemma overlapDiscount_mem_unit (μ : ProbabilityMeasure OverlapArray) (q : ℝ) :
    0≤overlapDiscount μ q ∧ overlapDiscount μ q≤1 := by
  let := entryLaw_probability μ 0 1
  exact ⟨measureReal_nonneg,measureReal_le_one⟩

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma ordered_range_iff_index {r : ℕ} (c : OrderedFinpartition r) (i : Fin c.length) (j : Fin r) :
    j∈Set.range (c.emb i) ↔ c.index j=i := by
  constructor
  · rintro ⟨k,rfl⟩
    exact orderedIndex_emb c i k
  · intro h
    refine ⟨?_,?_⟩
    · exact h ▸ c.invEmbedding j
    · subst i
      exact c.emb_invEmbedding j

def blockMax {r : ℕ} (c : OrderedFinpartition r) (i : Fin c.length) : Fin r :=
  c.emb i ⟨c.partSize i-1,Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩

lemma blockMax_index {r : ℕ} (c : OrderedFinpartition r) (i : Fin c.length) :
    c.index (blockMax c i)=i := orderedIndex_emb _ _ _

lemma le_blockMax {r : ℕ} (c : OrderedFinpartition r) {i : Fin c.length} {j : Fin r}
    (h : c.index j=i) : j≤blockMax c i := by
  obtain ⟨k,rfl⟩ := (ordered_range_iff_index c i j).mpr h
  apply (c.emb_strictMono i).monotone
  change (k:ℕ)≤c.partSize i-1
  omega

lemma ordered_rel_range {r : ℕ} (c d : OrderedFinpartition r)
    (h : ∀ i j,c.index i=c.index j ↔ d.index i=d.index j) (i : Fin c.length) :
    Set.range (c.emb i)=Set.range (d.emb (d.index (blockMax c i))) := by
  ext j
  rw [ordered_range_iff_index,ordered_range_iff_index,← h j (blockMax c i),blockMax_index]

lemma ordered_rel_max {r : ℕ} (c d : OrderedFinpartition r)
    (h : ∀ i j,c.index i=c.index j ↔ d.index i=d.index j) (i : Fin c.length) :
    blockMax c i=blockMax d (d.index (blockMax c i)) := by
  apply le_antisymm
  · exact le_blockMax d rfl
  · apply le_blockMax c
    have hd := blockMax_index d (d.index (blockMax c i))
    have hc := (h (blockMax d (d.index (blockMax c i))) (blockMax c i)).mpr hd
    rwa [blockMax_index] at hc

lemma ordered_rel_map_mono {r : ℕ} (c d : OrderedFinpartition r)
    (h : ∀ i j,c.index i=c.index j ↔ d.index i=d.index j) :
    StrictMono (fun i => d.index (blockMax c i)) := by
  intro i j hij
  have hh : blockMax c i<blockMax c j := c.parts_strictMono hij
  rw [ordered_rel_max c d h i,ordered_rel_max c d h j] at hh
  exact d.parts_strictMono.lt_iff_lt.mp hh

 

theorem ordered_eq_of_same_relation {r : ℕ} (c d : OrderedFinpartition r)
    (h : ∀ i j,c.index i=c.index j ↔ d.index i=d.index j) : c=d := by
  have hm := ordered_rel_map_mono c d h
  have hm' := ordered_rel_map_mono d c (fun i j => (h i j).symm)
  have hlen : c.length=d.length := by
    apply le_antisymm
    · simpa using Fintype.card_le_of_injective _ hm.injective
    · simpa using Fintype.card_le_of_injective _ hm'.injective
  have hf : ∀ i, d.index (blockMax c i)=Fin.cast hlen i := by
    have hg : StrictMono (fun i => Fin.cast hlen.symm (d.index (blockMax c i))) :=
      (Fin.castOrderIso hlen.symm).strictMono.comp hm
    intro i
    have hh := congrFun hg.eq_id i
    apply Fin.ext
    have hv := congrArg (fun j : Fin c.length => (j:ℕ)) hh
    exact hv
  have hcode : ∀ j,(c.index j:ℕ)=(d.index j:ℕ) := by
    intro j
    have hj : d.index j=d.index (blockMax c (c.index j)) :=
      (h j (blockMax c (c.index j))).mp (by rw [blockMax_index])
    rw [hj,hf]
    rfl
  rcases c with ⟨cl,cs,cp,ce,cm,ct,cd,cc⟩
  rcases d with ⟨dl,ds,dp,de,dm,dt,dd,dc⟩
  dsimp only at hlen
  subst dl
  have hs : cs=ds := by
    funext i
    have hc := labelCount_orderedCode (OrderedFinpartition.mk cl cs cp ce cm ct cd cc) i
    have hd := labelCount_orderedCode (OrderedFinpartition.mk cl ds dp de dm dt dd dc) i
    have hh : orderedCode (OrderedFinpartition.mk cl cs cp ce cm ct cd cc)=
        orderedCode (OrderedFinpartition.mk cl ds dp de dm dt dd dc) := funext hcode
    rw [hh] at hc
    exact hc.symm.trans hd
  subst ds
  have he : ce=de := by
    funext i
    apply (cm i).range_inj_of_wellFoundedLT (dm i) |>.mp
    have hr := ordered_rel_range (OrderedFinpartition.mk cl cs cp ce cm ct cd cc)
      (OrderedFinpartition.mk cl cs dp de dm dt dd dc) h i
    rw [hf] at hr
    exact hr
  subst de
  rfl

lemma ordered_partition_disjoint {r : ℕ} {c d : OrderedFinpartition r} (hcd : c≠d) (q : ℝ) :
    Disjoint (partitionEvent (orderedCode c) q) (partitionEvent (orderedCode d) q) := by
  apply Set.disjoint_left.mpr
  intro R hc hd
  apply hcd
  apply ordered_eq_of_same_relation
  intro i j
  have hh := (hc i j).symm.trans (hd i j)
  simpa only [orderedCode,Fin.val_inj] using hh

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def Refines {r : ℕ} (p c : Fin r → ℕ) : Prop := ∀ i j,c i=c j → p i=p j

def NestedCodes {d r : ℕ} (c : Fin (d+1) → Fin r → ℕ) : Prop :=
  ∀ k l,k≤l → Refines (c k) (c l)

def hierarchyEvent {d r : ℕ} (c : Fin (d+1) → Fin r → ℕ) (q : Fin (d+1) → ℝ) : Set OverlapArray :=
  {R | ∀ k,R∈partitionEvent (c k) (q k)}

def hierarchyBlock {d r : ℕ} (c : Fin (d+1) → Fin r → ℕ) (q : Fin (d+1) → ℝ) : Set (OverlapBlock r) :=
  {R | ∀ k,R∈partitionBlock (c k) (q k)}

lemma hierarchyBlock_measurable {d r : ℕ} (c : Fin (d+1) → Fin r → ℕ) (q : Fin (d+1) → ℝ) :
    MeasurableSet (hierarchyBlock c q) := by
  unfold hierarchyBlock
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => measurableSet_partitionBlock _ _

lemma nestedCodes_restrict {d r : ℕ} {c : Fin (d+1) → Fin (r+1) → ℕ} (hc : NestedCodes c) :
    NestedCodes (fun k => restrictCode (c k)) :=
  fun k l hkl i j hij => hc k l hkl i.castSucc j.castSucc hij

lemma hierarchy_restrict {d r : ℕ} {c : Fin (d+1) → Fin (r+1) → ℕ} {q : Fin (d+1) → ℝ}
    {R : OverlapArray} (h : R∈hierarchyEvent c q) :
    R∈hierarchyEvent (fun k => restrictCode (c k)) q := fun k => partition_restrict (h k)

lemma hierarchy_existing_iff {d r : ℕ} (c : Fin (d+1) → Fin (r+1) → ℕ)
    (hc : NestedCodes c) (q : Fin (d+1) → ℝ) (hq : Monotone q) (h1 : q (Fin.last d)<1)
    (i : Fin r) (hi : restrictCode (c (Fin.last d)) i=c (Fin.last d) (Fin.last r))
    {R : OverlapArray} (hG : R∈GramArrays) (hu : R∈UltrametricArrays) :
    R∈hierarchyEvent c q ↔ R∈hierarchyEvent (fun k => restrictCode (c k)) q ∧
      q (Fin.last d)<(R i r:ℝ) := by
  constructor
  · exact fun h => ⟨hierarchy_restrict h,((h (Fin.last d)) i.castSucc (Fin.last r)).mpr hi⟩
  · rintro ⟨h,hrow⟩ k
    have hki : restrictCode (c k) i=c k (Fin.last r) :=
      hc k (Fin.last d) (Fin.le_last k) _ _ hi
    exact (partition_existing_iff (c k) ((hq (Fin.le_last k)).trans_lt h1) i hki hG hu).mpr
      ⟨h k,(hq (Fin.le_last k)).trans_lt hrow⟩

lemma parentRep_no_join {r : ℕ} {p c : Fin r → ℕ} {q t : ℝ} (hqt : q≤t)
    {i : Fin r} {T : Finset (Fin r)} (hT : ParentReps p c i T)
    {R : OverlapArray} (hG : R∈GramArrays) (hu : R∈UltrametricArrays)
    (hp : R∈partitionEvent p q) (hc : R∈partitionEvent c t)
    (hi : q<(R i r:ℝ)) (hrow : ∀ k∈T,(R k r:ℝ)≤t) :
    ∀ j : Fin r,(R j r:ℝ)≤t := by
  intro j
  by_contra hn
  have hj : t<(R j r:ℝ) := lt_of_not_ge hn
  have hji : p j=p i := (hp j i).mp
    ((lt_min (hqt.trans_lt hj) hi).trans_le (hu j i r))
  obtain ⟨k,hk,hkj⟩ := (hT.2.2 j).mp hji
  have hkj' : t<(R k j:ℝ) := (hc k j).mpr hkj
  have hh := hu k r j
  rw [hG.1 r j] at hh
  exact (not_lt_of_ge (hrow k hk)) ((lt_min hkj' hj).trans_le hh)

 

lemma hierarchy_fresh_iff {d r : ℕ} (c : Fin (d+1) → Fin (r+1) → ℕ)
    (hc : NestedCodes c) (q : Fin (d+1) → ℝ) (hq : Monotone q) (h1 : q (Fin.last d)<1)
    (k : Fin d) (i : Fin r) (hi : restrictCode (c k.castSucc) i=c k.castSucc (Fin.last r))
    (hn : ∀ j,restrictCode (c k.succ) j≠c k.succ (Fin.last r))
    {T : Finset (Fin r)} (hT : ParentReps (restrictCode (c k.castSucc)) (restrictCode (c k.succ)) i T)
    {R : OverlapArray} (hG : R∈GramArrays) (hu : R∈UltrametricArrays) :
    R∈hierarchyEvent c q ↔ R∈hierarchyEvent (fun l => restrictCode (c l)) q ∧
      q k.castSucc<(R i r:ℝ) ∧ ∀ j∈T,(R j r:ℝ)≤q k.succ := by
  constructor
  · intro h
    refine ⟨hierarchy_restrict h,((h k.castSucc) i.castSucc (Fin.last r)).mpr hi,fun j _ => ?_⟩
    exact le_of_not_gt fun hj => hn j (((h k.succ) j.castSucc (Fin.last r)).mp hj)
  · rintro ⟨h,hrow,hnew⟩ l
    have hll : q l<1 := (hq (Fin.le_last l)).trans_lt h1
    by_cases hl : l≤k.castSucc
    · have hli : restrictCode (c l) i=c l (Fin.last r) := hc l k.castSucc hl _ _ hi
      exact (partition_existing_iff (c l) hll i hli hG hu).mpr ⟨h l,(hq hl).trans_lt hrow⟩
    · have hkl : k.succ≤l := by change (k:ℕ)+1≤(l:ℕ); have := not_le.mp hl; change (k:ℕ)<(l:ℕ) at this; omega
      have hnf : ∀ j,restrictCode (c l) j≠c l (Fin.last r) := fun j hj =>
        hn j (hc k.succ l hkl _ _ hj)
      apply (partition_fresh_iff (c l) hll hnf hG).mpr
      refine ⟨h l,fun j => ?_⟩
      have hqs : q k.castSucc≤q k.succ := hq (by change (k:ℕ)≤(k:ℕ)+1; omega)
      exact (parentRep_no_join hqs hT hG hu (h k.castSucc) (h k.succ) hrow hnew j).trans (hq hkl)

lemma GG_hierarchy_existing {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d r : ℕ} (c : Fin (d+1) → Fin (r+1) → ℕ) (hc : NestedCodes c)
    (q : Fin (d+1) → ℝ) (hq : Monotone q) (h1 : q (Fin.last d)<1) (i : Fin r)
    (hi : restrictCode (c (Fin.last d)) i=c (Fin.last d) (Fin.last r)) :
    (r:ℝ)*(μ:Measure OverlapArray).real (hierarchyEvent c q)=
      ((clusterCount (restrictCode (c (Fin.last d))) i:ℝ)-overlapDiscount μ (q (Fin.last d)))*
        (μ:Measure OverlapArray).real (hierarchyEvent (fun k => restrictCode (c k)) q) := by
  have he : hierarchyEvent c q =ᵐ[(μ:Measure OverlapArray)]
      {R | R∈hierarchyEvent (fun k => restrictCode (c k)) q ∧ q (Fin.last d)<(R i r:ℝ)} := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG,
      ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu] with R hg hu
    exact propext (hierarchy_existing_iff c hc q hq h1 i hi hg hu)
  rw [measureReal_congr he]
  exact GG_join_on_block hgg (hierarchyBlock_measurable _ q) _ _ (fun _ h => h (Fin.last d)) i

lemma GG_hierarchy_fresh {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d r : ℕ} (c : Fin (d+1) → Fin (r+1) → ℕ) (hc : NestedCodes c)
    (q : Fin (d+1) → ℝ) (hq : Monotone q) (h1 : q (Fin.last d)<1)
    (k : Fin d) (i : Fin r) (hi : restrictCode (c k.castSucc) i=c k.castSucc (Fin.last r))
    (hn : ∀ j,restrictCode (c k.succ) j≠c k.succ (Fin.last r))
    {T : Finset (Fin r)} (hT : ParentReps (restrictCode (c k.castSucc)) (restrictCode (c k.succ)) i T) :
    (r:ℝ)*(μ:Measure OverlapArray).real (hierarchyEvent c q)=
      ((T.card:ℝ)*overlapDiscount μ (q k.succ)-overlapDiscount μ (q k.castSucc))*
        (μ:Measure OverlapArray).real (hierarchyEvent (fun l => restrictCode (c l)) q) := by
  have he : hierarchyEvent c q =ᵐ[(μ:Measure OverlapArray)]
      {R | R∈hierarchyEvent (fun l => restrictCode (c l)) q ∧ q k.castSucc<(R i r:ℝ) ∧
        ∀ j∈T,(R j r:ℝ)≤q k.succ} := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG,
      ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu] with R hg hu
    exact propext (hierarchy_fresh_iff c hc q hq h1 k i hi hn hT hg hu)
  rw [measureReal_congr he]
  exact GG_nested_innovation hG hgg hu (hierarchyBlock_measurable _ q)
    (hq (by change (k:ℕ)≤(k:ℕ)+1; omega))
    (fun _ h => h k.castSucc) (fun _ h => h k.succ) i hT

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def childLabels {r : ℕ} (p c : Fin r → ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i => p i=x)).image c

lemma mem_childLabels {r : ℕ} (p c : Fin r → ℕ) (x y : ℕ) :
    y∈childLabels p c x ↔ ∃ i,p i=x ∧ c i=y := by
  simp only [childLabels,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

lemma childLabels_nonempty {r : ℕ} (p c : Fin r → ℕ) {x : ℕ} (hx : x∈codeLabels p) :
    (childLabels p c x).Nonempty := by
  obtain ⟨i,hi⟩ := (codeLabels_mem _ _).mp hx
  exact ⟨c i,(mem_childLabels _ _ _ _).mpr ⟨i,hi,rfl⟩⟩

lemma childLabels_empty {r : ℕ} (p c : Fin r → ℕ) {x : ℕ} (hx : x∉codeLabels p) :
    childLabels p c x=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨i,hi,_⟩ := (mem_childLabels _ _ _ _).mp hy
  exact hx ((codeLabels_mem _ _).mpr ⟨i,hi⟩)

lemma childLabels_succ {r : ℕ} (p c : Fin (r+1) → ℕ) (x : ℕ) :
    childLabels p c x=if p (Fin.last r)=x then
      insert (c (Fin.last r)) (childLabels (restrictCode p) (restrictCode c) x)
      else childLabels (restrictCode p) (restrictCode c) x := by
  ext y
  simp only [mem_childLabels]
  split_ifs with hp
  · simp only [Finset.mem_insert,mem_childLabels]
    constructor
    · rintro ⟨i,hi,hc⟩
      exact Fin.lastCases (fun _ hc => Or.inl hc.symm)
        (fun j hj hc => Or.inr ⟨j,hj,hc⟩) i hi hc
    · rintro (hy | ⟨i,hi,hc⟩)
      · exact ⟨Fin.last r,hp,hy.symm⟩
      · exact ⟨i.castSucc,hi,hc⟩
  · rw [mem_childLabels]
    constructor
    · rintro ⟨i,hi,hc⟩
      exact Fin.lastCases (fun hi _ => (hp hi).elim) (fun j hj hc => ⟨j,hj,hc⟩) i hi hc
    · rintro ⟨i,hi,hc⟩
      exact ⟨i.castSucc,hi,hc⟩

lemma exists_parentReps {r : ℕ} {p c : Fin r → ℕ} (hpc : Refines p c) (i : Fin r) :
    ∃ T, ParentReps p c i T := by
  obtain ⟨S,hS⟩ := exists_clusterReps c
  let T := S.filter (fun j => p j=p i)
  refine ⟨T,hS.1.mono (by intro j hj; exact (Finset.mem_filter.mp hj).1),?_,?_⟩
  · exact fun j hj => (Finset.mem_filter.mp hj).2
  · intro j
    constructor
    · intro hj
      obtain ⟨k,hk,hkj⟩ := hS.2 j
      exact ⟨k,Finset.mem_filter.mpr ⟨hk,(hpc k j hkj).trans hj⟩,hkj⟩
    · rintro ⟨k,hk,hkj⟩
      exact (hpc k j hkj).symm.trans (Finset.mem_filter.mp hk).2

lemma ParentReps.card_childLabels {r : ℕ} {p c : Fin r → ℕ} {i : Fin r} {T : Finset (Fin r)}
    (hT : ParentReps p c i T) : T.card=(childLabels p c (p i)).card := by
  have he : T.image c=childLabels p c (p i) := by
    ext y
    simp only [Finset.mem_image,mem_childLabels]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨j,hT.2.1 j hj,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact (hT.2.2 j).mp hj
  rw [← he,Finset.card_image_of_injOn hT.1]

def edgeFactor {r : ℕ} (a b : ℝ) (p c : Fin r → ℕ) : ℝ :=
  ∏ x∈codeLabels p,branchFactor a b (childLabels p c x).card

def leafFactor {r : ℕ} (a : ℝ) (c : Fin r → ℕ) : ℝ :=
  ∏ x∈codeLabels c,blockFactor a (labelCount c x)

lemma edgeFactor_existing {r : ℕ} (a b : ℝ) (p c : Fin (r+1) → ℕ)
    (hpc : Refines p c) (i : Fin r) (hi : restrictCode c i=c (Fin.last r)) :
    edgeFactor a b p c=edgeFactor a b (restrictCode p) (restrictCode c) := by
  have hp : restrictCode p i=p (Fin.last r) := hpc _ _ hi
  have hlabels : codeLabels p=codeLabels (restrictCode p) := by
    rw [codeLabels_succ,Finset.insert_eq_of_mem ((codeLabels_mem _ _).mpr ⟨i,hp⟩)]
  unfold edgeFactor
  apply Finset.prod_congr hlabels
  intro x _
  congr 2
  rw [childLabels_succ]
  split_ifs with hx
  · exact Finset.insert_eq_of_mem ((mem_childLabels _ _ _ _).mpr ⟨i,hp.trans hx,hi⟩)
  · rfl

lemma edgeFactor_fresh_parent {r : ℕ} (a b : ℝ) (p c : Fin (r+1) → ℕ)
    (hp : ∀ i,restrictCode p i≠p (Fin.last r)) :
    edgeFactor a b p c=edgeFactor a b (restrictCode p) (restrictCode c) := by
  have hx : p (Fin.last r)∉codeLabels (restrictCode p) := by
    simpa only [codeLabels_mem,not_exists] using hp
  have hn : childLabels p c (p (Fin.last r))={c (Fin.last r)} := by
    rw [childLabels_succ,ite_eq_left rfl,childLabels_empty _ _ hx,Finset.insert_empty]
  unfold edgeFactor
  rw [codeLabels_succ,Finset.prod_insert hx,hn,Finset.card_singleton,branchFactor_one,one_mul]
  apply Finset.prod_congr rfl
  intro x hxx
  have hne : p (Fin.last r)≠x := fun hh => hx (hh ▸ hxx)
  rw [childLabels_succ,ite_eq_right hne]

lemma edgeFactor_fresh_child {r : ℕ} (a b : ℝ) (p c : Fin (r+1) → ℕ)
    (i : Fin r) (hp : restrictCode p i=p (Fin.last r))
    (hc : ∀ j,restrictCode c j≠c (Fin.last r)) :
    edgeFactor a b p c=
      (a*((childLabels (restrictCode p) (restrictCode c) (restrictCode p i)).card:ℝ)-b)*
        edgeFactor a b (restrictCode p) (restrictCode c) := by
  let x := p (Fin.last r)
  have hx : x∈codeLabels (restrictCode p) := (codeLabels_mem _ _).mpr ⟨i,hp⟩
  have hn : c (Fin.last r)∉childLabels (restrictCode p) (restrictCode c) x := by
    rintro hy
    obtain ⟨j,_,hj⟩ := (mem_childLabels _ _ _ _).mp hy
    exact hc j hj
  have hlabels : codeLabels p=codeLabels (restrictCode p) := by
    rw [codeLabels_succ,Finset.insert_eq_of_mem hx]
  unfold edgeFactor
  rw [hlabels,← Finset.mul_prod_erase _ _ hx,← Finset.mul_prod_erase _ _ hx]
  have he : (∏ y∈(codeLabels (restrictCode p)).erase x,branchFactor a b (childLabels p c y).card)=
      ∏ y∈(codeLabels (restrictCode p)).erase x,branchFactor a b
        (childLabels (restrictCode p) (restrictCode c) y).card := by
    apply Finset.prod_congr rfl
    intro y hy
    rw [childLabels_succ,ite_eq_right (Ne.symm (Finset.mem_erase.mp hy).1)]
  rw [he,childLabels_succ,ite_eq_left rfl,Finset.card_insert_of_notMem hn,
    branchFactor_succ a b (Finset.card_pos.mpr (childLabels_nonempty _ _ hx)),hp]
  ring

lemma leafFactor_existing {r : ℕ} (a : ℝ) (c : Fin (r+1) → ℕ) (i : Fin r)
    (hi : restrictCode c i=c (Fin.last r)) :
    leafFactor a c=((clusterCount (restrictCode c) i:ℝ)-a)*leafFactor a (restrictCode c) := by
  let x := c (Fin.last r)
  have hx : x∈codeLabels (restrictCode c) := (codeLabels_mem _ _).mpr ⟨i,hi⟩
  have hlabels : codeLabels c=codeLabels (restrictCode c) := by
    rw [codeLabels_succ,Finset.insert_eq_of_mem hx]
  have hcount : labelCount (restrictCode c) x=clusterCount (restrictCode c) i := by
    change labelCount (restrictCode c) (c (Fin.last r))=_
    rw [← hi]
    rfl
  unfold leafFactor
  rw [hlabels,← Finset.mul_prod_erase _ _ hx,← Finset.mul_prod_erase _ _ hx]
  have he : (∏ y∈(codeLabels (restrictCode c)).erase x,blockFactor a (labelCount c y))=
      ∏ y∈(codeLabels (restrictCode c)).erase x,blockFactor a (labelCount (restrictCode c) y) := by
    apply Finset.prod_congr rfl
    intro y hy
    rw [labelCount_succ,ite_eq_right (Ne.symm (Finset.mem_erase.mp hy).1),add_zero]
  rw [he,labelCount_succ,ite_eq_left rfl,hcount,blockFactor_succ a (clusterCount_pos _ i)]
  ring

lemma leafFactor_fresh {r : ℕ} (a : ℝ) (c : Fin (r+1) → ℕ)
    (hc : ∀ i,restrictCode c i≠c (Fin.last r)) : leafFactor a c=leafFactor a (restrictCode c) := by
  have hx : c (Fin.last r)∉codeLabels (restrictCode c) := by simpa only [codeLabels_mem,not_exists] using hc
  have hz : labelCount (restrictCode c) (c (Fin.last r))=0 := by
    simpa only [← labelCount_pos_iff,not_lt,Nat.le_zero] using hx
  have hn : labelCount c (c (Fin.last r))=1 := by rw [labelCount_succ,hz,ite_eq_left rfl,zero_add]
  unfold leafFactor
  rw [codeLabels_succ,Finset.prod_insert hx,hn,blockFactor_one,one_mul]
  apply Finset.prod_congr rfl
  intro y hy
  have hne : c (Fin.last r)≠y := fun hh => hx (hh ▸ hy)
  rw [labelCount_succ,ite_eq_right hne,add_zero]

end SKCavity

end

end OAI
