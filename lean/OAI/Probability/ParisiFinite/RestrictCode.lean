import Mathlib
import OAI.Probability.ParisiFinite.CoreScaleSqLeOne

namespace OAI

/-! Restrict Code. -/

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

def restrictCode {r : ℕ} (c : Fin (r+1) → ℕ) : Fin r → ℕ := fun i => c i.castSucc

lemma partition_restrict {r : ℕ} {c : Fin (r+1) → ℕ} {q : ℝ} {R : OverlapArray}
    (h : R∈partitionEvent c q) : R∈partitionEvent (restrictCode c) q :=
  fun i j => h i.castSucc j.castSucc

lemma partition_extend_iff {r : ℕ} (c : Fin (r+1) → ℕ) {q : ℝ} (hq : q<1)
    {R : OverlapArray} (hG : R∈GramArrays) : R∈partitionEvent c q ↔
      R∈partitionEvent (restrictCode c) q ∧
      ∀ i : Fin r, q<(R i r:ℝ) ↔ restrictCode c i=c (Fin.last r) := by
  constructor
  · intro h
    exact ⟨partition_restrict h,fun i => h i.castSucc (Fin.last r)⟩
  · rintro ⟨h,hrow⟩
    intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · change (q<(R r r:ℝ)) ↔ _
        rw [hG.2.1]
        simp [hq]
      · change (q<(R r b:ℝ)) ↔ c (Fin.last r)=restrictCode c b
        rw [hG.1 r b]
        exact (hrow b).trans eq_comm
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · exact hrow a
      · exact h a b

lemma partition_existing_iff {r : ℕ} (c : Fin (r+1) → ℕ) {q : ℝ} (hq : q<1)
    (i : Fin r) (hi : restrictCode c i=c (Fin.last r)) {R : OverlapArray}
    (hG : R∈GramArrays) (hu : R∈UltrametricArrays) :
    R∈partitionEvent c q ↔ R∈partitionEvent (restrictCode c) q ∧ q<(R i r:ℝ) := by
  rw [partition_extend_iff c hq hG]
  constructor
  · exact fun h => ⟨h.1,(h.2 i).mpr hi⟩
  · rintro ⟨h,hir⟩
    refine ⟨h,fun j => ?_⟩
    constructor
    · intro hjr
      have hji : q<(R j i:ℝ) := (lt_min hjr hir).trans_le (hu j i r)
      exact ((h j i).mp hji).trans hi
    · intro hj
      have hji : q<(R j i:ℝ) := (h j i).mpr (hj.trans hi.symm)
      have hh := hu j r i
      rw [hG.1 r i] at hh
      exact (lt_min hji hir).trans_le hh

lemma partition_fresh_iff {r : ℕ} (c : Fin (r+1) → ℕ) {q : ℝ} (hq : q<1)
    (hi : ∀ i, restrictCode c i≠c (Fin.last r)) {R : OverlapArray}
    (hG : R∈GramArrays) :
    R∈partitionEvent c q ↔ R∈partitionEvent (restrictCode c) q ∧ ∀ i : Fin r, (R i r:ℝ) ≤ q := by
  rw [partition_extend_iff c hq hG]
  simp only [hi,iff_false,not_lt]

lemma partition_zero (c : Fin 0 → ℕ) (q : ℝ) : partitionEvent c q=Set.univ := by
  ext R
  simp only [Set.mem_univ,iff_true]
  exact fun i => Fin.elim0 i

lemma partition_one_real {μ : ProbabilityMeasure OverlapArray} (hG : (μ:Measure OverlapArray) GramArrays=1)
    (c : Fin 1 → ℕ) {q : ℝ} (hq : q<1) : (μ:Measure OverlapArray).real (partitionEvent c q)=1 := by
  have he : partitionEvent c q =ᵐ[(μ:Measure OverlapArray)] Set.univ := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG] with R hR
    apply propext
    change (∀ i j : Fin 1, q<(R i j:ℝ) ↔ c i=c j) ↔ True
    rw [iff_true]
    intro i j
    fin_cases i; fin_cases j
    change q<(R 0 0:ℝ) ↔ _
    rw [hR.2.1]
    simp [hq]
  rw [measureReal_congr he,probReal_univ]

lemma GG_partition_existing {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {r : ℕ} (c : Fin (r+1) → ℕ) {q : ℝ} (hq : q<1) (i : Fin r)
    (hi : restrictCode c i=c (Fin.last r)) :
    (r:ℝ)*(μ:Measure OverlapArray).real (partitionEvent c q)=
      ((clusterCount (restrictCode c) i:ℝ)-overlapDiscount μ q)*
        (μ:Measure OverlapArray).real (partitionEvent (restrictCode c) q) := by
  have he : partitionEvent c q =ᵐ[(μ:Measure OverlapArray)]
      {R | R∈partitionEvent (restrictCode c) q ∧ q<(R i r:ℝ)} := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG,
      ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu] with R hg hu
    exact propext (partition_existing_iff c hq i hi hg hu)
  rw [measureReal_congr he]
  exact GG_cluster_join hgg _ q i

lemma GG_partition_fresh {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {r : ℕ} (c : Fin (r+1) → ℕ) {q : ℝ} (hq : q<1)
    {S : Finset (Fin r)} (hS : ClusterReps (restrictCode c) S)
    (hi : ∀ i, restrictCode c i≠c (Fin.last r)) :
    (r:ℝ)*(μ:Measure OverlapArray).real (partitionEvent c q)=
      (S.card:ℝ)*overlapDiscount μ q*(μ:Measure OverlapArray).real (partitionEvent (restrictCode c) q) := by
  have he : partitionEvent c q =ᵐ[(μ:Measure OverlapArray)]
      {R | R∈partitionEvent (restrictCode c) q ∧ ∀ i : Fin r,(R i r:ℝ) ≤ q} := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG] with R hg
    exact propext (partition_fresh_iff c hq hi hg)
  rw [measureReal_congr he]
  exact GG_cluster_innovation hG hgg hu hS q

 

theorem threshold_partition_unique {μ ν : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    (hG' : (ν:Measure OverlapArray) GramArrays=1) (hgg' : GGIdentities ν)
    (hu' : (ν:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) (hz : overlapDiscount μ q=overlapDiscount ν q)
    (r : ℕ) (c : Fin r → ℕ) :
    (μ:Measure OverlapArray).real (partitionEvent c q)=(ν:Measure OverlapArray).real (partitionEvent c q) := by
  induction r with
  | zero => rw [partition_zero]; simp
  | succ r ih =>
    by_cases hr : r=0
    · subst r
      rw [partition_one_real hG c hq,partition_one_real hG' c hq]
    have hr' : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr hr
    have hold := ih (restrictCode c)
    by_cases hc : ∃ i, restrictCode c i=c (Fin.last r)
    · obtain ⟨i,hi⟩ := hc
      have h1 := GG_partition_existing hG hgg hu c hq i hi
      have h2 := GG_partition_existing hG' hgg' hu' c hq i hi
      rw [hz,hold] at h1
      exact mul_left_cancel₀ hr' (h1.trans h2.symm)
    · have hc' : ∀ i, restrictCode c i≠c (Fin.last r) := not_exists.mp hc
      obtain ⟨S,hS⟩ := exists_clusterReps (restrictCode c)
      have h1 := GG_partition_fresh hG hgg hu c hq hS hc'
      have h2 := GG_partition_fresh hG' hgg' hu' c hq hS hc'
      rw [hz,hold] at h1
      exact mul_left_cancel₀ hr' (h1.trans h2.symm)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 
def oldRowCondition {r : ℕ} (S : Set (OverlapBlock r)) (t : Fin r → ℝ) (j : Fin r) : Set (OverlapBlock r) :=
  {T | T∈S ∧ ∀ i, t i<(T i j:ℝ)}

lemma measurableSet_oldRowCondition {r : ℕ} {S : Set (OverlapBlock r)}
    (hS : MeasurableSet S) (t : Fin r → ℝ) (j : Fin r) : MeasurableSet (oldRowCondition S t j) := by
  simp only [oldRowCondition,Set.ofPred_and,Set.ofPred_forall]
  exact hS.inter (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (by fun_prop))

lemma ultra_row_event {r : ℕ} (S : Set (OverlapBlock r)) (t : Fin r → ℝ) (j : Fin r)
    (hj : ∀ i, t i ≤ t j) {R : OverlapArray} (hG : R∈GramArrays) (hu : R∈UltrametricArrays) :
    (blockOfArray r R∈S ∧ ∀ i : Fin r, t i<(R i r:ℝ)) ↔
      blockOfArray r R∈oldRowCondition S t j ∧ t j<(R j r:ℝ) := by
  constructor
  · rintro ⟨hS,hrow⟩
    exact ⟨⟨hS,fun i => (lt_min (hrow i) ((hj i).trans_lt (hrow j))).trans_le (hu i j r)⟩,hrow j⟩
  · rintro ⟨⟨hS,hrow⟩,hjr⟩
    refine ⟨hS,fun i => ?_⟩
    have hh := hu i r j
    rw [hG.1 r j] at hh
    exact (lt_min (hrow i) ((hj i).trans_lt hjr)).trans_le hh

lemma blockLaw_real (μ : ProbabilityMeasure OverlapArray) (r : ℕ) {S : Set (OverlapBlock r)}
    (hS : MeasurableSet S) : (blockLaw μ r).real S=(μ:Measure OverlapArray).real ((blockOfArray r) ⁻¹' S) := by
  unfold Measure.real blockLaw
  rw [Measure.map_apply (continuous_blockOfArray r).measurable hS]

 

theorem GG_row_tail_identity {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {r : ℕ} {S : Set (OverlapBlock r)} (hS : MeasurableSet S)
    (t : Fin r → ℝ) (j : Fin r) (hj : ∀ i, t i ≤ t j) :
    (r:ℝ)*(μ:Measure OverlapArray).real {R | blockOfArray r R∈S ∧ ∀ i : Fin r, t i<(R i r:ℝ)}=
      (blockLaw μ r).real (oldRowCondition S t j)*(entryLaw μ 0 1).real {x | t j<(x:ℝ)}+
      ∑ l∈Finset.univ.erase j,(blockLaw μ r).real {T | T∈oldRowCondition S t j ∧ t j<(T j l:ℝ)} := by
  have he : {R | blockOfArray r R∈S ∧ ∀ i : Fin r, t i<(R i r:ℝ)} =ᵐ[(μ:Measure OverlapArray)]
      {R | blockOfArray r R∈oldRowCondition S t j ∧ t j<(R j r:ℝ)} := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG,
      ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu] with R hR hU
    exact propext (ultra_row_event S t j hj hR hU)
  rw [measureReal_congr he]
  have hB := measurableSet_oldRowCondition hS t j
  have hg := GG_event_identity hgg r j (oldRowCondition S t j) {x : OverlapEntry | t j<(x:ℝ)} hB (measurableSet_lt measurable_const (by fun_prop))
  simp only [Set.mem_ofPred_eq] at hg
  rw [hg]
  rw [blockLaw_real μ r hB]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact (blockLaw_real μ r (S:={T | T∈oldRowCondition S t j ∧ t j<(T j l:ℝ)})
    (hB.inter (measurableSet_lt measurable_const
      (by fun_prop : Measurable (fun T : OverlapBlock r => (T j l:ℝ)))))).symm

lemma row_tail_unique {μ ν : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    (hG' : (ν:Measure OverlapArray) GramArrays=1) (hgg' : GGIdentities ν)
    (hu' : (ν:Measure OverlapArray) UltrametricArrays=1)
    (hz : entryLaw μ 0 1=entryLaw ν 0 1) (r : ℕ) (hblock : blockLaw μ r=blockLaw ν r)
    {S : Set (OverlapBlock r)} (hS : MeasurableSet S) (t : Fin r → ℝ) :
    (μ:Measure OverlapArray).real {R | blockOfArray r R∈S ∧ ∀ i : Fin r, t i<(R i r:ℝ)}=
      (ν:Measure OverlapArray).real {R | blockOfArray r R∈S ∧ ∀ i : Fin r, t i<(R i r:ℝ)} := by
  by_cases hr : r=0
  · subst r
    simp only [Fin.forall_fin_zero,and_true]
    exact (blockLaw_real μ 0 hS).symm.trans ((congrArg (fun ρ : Measure (OverlapBlock 0) => ρ.real S) hblock).trans (blockLaw_real ν 0 hS))
  · have : NeZero r := ⟨hr⟩
    obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ t Finset.univ_nonempty
    have hj' : ∀ i, t i ≤ t j := fun i => hj i (Finset.mem_univ i)
    have h1 := GG_row_tail_identity hG hgg hu hS t j hj'
    have h2 := GG_row_tail_identity hG' hgg' hu' hS t j hj'
    rw [hblock,hz] at h1
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hr) (h1.trans h2.symm)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def overlapTails : Set (Set OverlapEntry) := Set.range (fun t : ℝ => {x : OverlapEntry | t<(x:ℝ)})

lemma overlapTails_measurable {S : Set OverlapEntry} (hS : S∈overlapTails) : MeasurableSet S := by
  obtain ⟨t,rfl⟩ := hS
  exact measurableSet_lt measurable_const (by fun_prop)

lemma overlapTails_generate : MeasurableSpace.generateFrom overlapTails=(inferInstance : MeasurableSpace OverlapEntry) := by
  apply le_antisymm (generateFrom_le (fun _ h => overlapTails_measurable h))
  have h : @Measurable OverlapEntry ℝ (MeasurableSpace.generateFrom overlapTails) inferInstance Subtype.val := by
    apply measurable_of_Ioi
    intro t
    exact measurableSet_generateFrom ⟨t,rfl⟩
  have hi : @Measurable OverlapEntry OverlapEntry (MeasurableSpace.generateFrom overlapTails) inferInstance id :=
    h.subtype_mk
  simpa only [MeasurableSpace.comap_id] using hi.comap_le

lemma overlapTails_pi : IsPiSystem overlapTails := by
  rintro A ⟨a,rfl⟩ B ⟨b,rfl⟩ _
  refine ⟨max a b,?_⟩
  ext x
  change max a b <(x:ℝ) ↔ a<(x:ℝ) ∧ b<(x:ℝ)
  exact max_lt_iff

lemma overlapTails_univ : (Set.univ : Set OverlapEntry)∈overlapTails := by
  refine ⟨-2,?_⟩
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  have := x.2.1
  linarith

lemma overlapTails_spanning : IsCountablySpanning overlapTails :=
  ⟨fun _ : ℕ => Set.univ,fun _ => overlapTails_univ,by exact Set.iUnion_const Set.univ⟩

def rowTailBoxes (r : ℕ) : Set (Set (Fin r → OverlapEntry)) :=
  Set.pi Set.univ '' Set.pi Set.univ (fun _ : Fin r => overlapTails)

lemma rowTailBoxes_generate (r : ℕ) : MeasurableSpace.generateFrom (rowTailBoxes r)=(inferInstance : MeasurableSpace (Fin r → OverlapEntry)) :=
  generateFrom_eq_pi (fun _ => overlapTails_generate) (fun _ => overlapTails_spanning)

lemma rowTailBoxes_pi (r : ℕ) : IsPiSystem (rowTailBoxes r) :=
  IsPiSystem.pi (fun _ => overlapTails_pi)

lemma rowTailBoxes_spanning (r : ℕ) : IsCountablySpanning (rowTailBoxes r) :=
  IsCountablySpanning.pi (fun _ => overlapTails_spanning)

lemma rowTailBoxes_characterization {r : ℕ} {S : Set (Fin r → OverlapEntry)} (hS : S∈rowTailBoxes r) :
    ∃ t : Fin r → ℝ, S={x | ∀ i, t i<(x i:ℝ)} := by
  obtain ⟨s,hs,rfl⟩ := hS
  have ht (i : Fin r) : ∃ t : ℝ, s i={x : OverlapEntry | t<(x:ℝ)} := by
    obtain ⟨t,ht⟩ := hs i (Set.mem_univ i)
    exact ⟨t,ht.symm⟩
  choose t ht using ht
  refine ⟨t,?_⟩
  ext x
  simp only [Set.mem_pi,Set.mem_univ,true_implies,ht,Set.mem_ofPred_eq]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def blockRowMap (r : ℕ) (R : OverlapArray) : OverlapBlock r × (Fin r → OverlapEntry) :=
  (blockOfArray r R,fun i => R i r)

lemma continuous_blockRowMap (r : ℕ) : Continuous (blockRowMap r) := by
  exact (continuous_blockOfArray r).prodMk (by fun_prop)

def blockRowLaw (μ : ProbabilityMeasure OverlapArray) (r : ℕ) : Measure (OverlapBlock r × (Fin r → OverlapEntry)) :=
  (μ:Measure OverlapArray).map (blockRowMap r)

instance blockRowLaw_probability (μ : ProbabilityMeasure OverlapArray) (r : ℕ) : IsProbabilityMeasure (blockRowLaw μ r) := by
  unfold blockRowLaw
  infer_instance

lemma blockRowLaw_eq {μ ν : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    (hG' : (ν:Measure OverlapArray) GramArrays=1) (hgg' : GGIdentities ν)
    (hu' : (ν:Measure OverlapArray) UltrametricArrays=1)
    (hz : entryLaw μ 0 1=entryLaw ν 0 1) (r : ℕ) (hblock : blockLaw μ r=blockLaw ν r) :
    blockRowLaw μ r=blockRowLaw ν r := by
  apply ext_of_generate_finite
    (Set.image2 (· ×ˢ ·) {S : Set (OverlapBlock r) | MeasurableSet S} (rowTailBoxes r))
    (generateFrom_eq_prod generateFrom_measurableSet (rowTailBoxes_generate r)
      isCountablySpanning_measurableSet (rowTailBoxes_spanning r)).symm
    (isPiSystem_measurableSet.prod (rowTailBoxes_pi r))
  · rintro _ ⟨S,hS,T,hT,rfl⟩
    change MeasurableSet S at hS
    obtain ⟨t,rfl⟩ := rowTailBoxes_characterization hT
    have hT' : MeasurableSet {x : Fin r → OverlapEntry | ∀ i, t i<(x i:ℝ)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (by fun_prop)
    rw [blockRowLaw,blockRowLaw,Measure.map_apply (continuous_blockRowMap r).measurable (hS.prod hT'),
      Measure.map_apply (continuous_blockRowMap r).measurable (hS.prod hT')]
    have he := row_tail_unique hG hgg hu hG' hgg' hu' hz r hblock hS t
    have he' := congrArg ENNReal.ofReal he
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),blockRowMap,Set.preimage,Set.mem_prod,Set.mem_ofPred_eq] using he'
  · simp

def joinBlock (r : ℕ) (z : OverlapBlock r × (Fin r → OverlapEntry)) : OverlapBlock (r+1) :=
  fun i j => Fin.lastCases (Fin.lastCases (⟨1,by norm_num⟩ : OverlapEntry) (fun b => z.2 b) j)
    (fun a => Fin.lastCases (z.2 a) (fun b => z.1 a b) j) i

lemma continuous_joinBlock (r : ℕ) : Continuous (joinBlock r) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [joinBlock,Fin.lastCases_last]; exact continuous_const
    | cast j => simp only [joinBlock,Fin.lastCases_last,Fin.lastCases_castSucc]; fun_prop
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp only [joinBlock,Fin.lastCases_last,Fin.lastCases_castSucc]; fun_prop
    | cast j => simp only [joinBlock,Fin.lastCases_castSucc]; fun_prop

lemma joinBlock_blockRowMap {R : OverlapArray} (hG : R∈GramArrays) (r : ℕ) :
    joinBlock r (blockRowMap r R)=blockOfArray (r+1) R := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa only [joinBlock,Fin.lastCases_last,blockOfArray,Fin.val_last] using (hG.2.1 r).symm
    | cast j => simpa only [joinBlock,Fin.lastCases_last,Fin.lastCases_castSucc,blockRowMap,blockOfArray,Fin.val_last,Fin.val_castSucc] using congrArg Subtype.val (hG.1 j r)
  | cast i =>
    induction j using Fin.lastCases <;> simp only [joinBlock,Fin.lastCases_last,Fin.lastCases_castSucc,blockRowMap,blockOfArray,Fin.val_last,Fin.val_castSucc]

lemma joinBlock_map_law {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (r : ℕ) :
    (blockRowLaw μ r).map (joinBlock r)=blockLaw μ (r+1) := by
  rw [blockRowLaw,Measure.map_map (continuous_joinBlock r).measurable (continuous_blockRowMap r).measurable]
  exact Measure.map_congr ((ae_full_probability μ isClosed_GramArrays.measurableSet hG).mono
    (fun R hR => joinBlock_blockRowMap hR r))

lemma blockLaw_zero (μ ν : ProbabilityMeasure OverlapArray) : blockLaw μ 0=blockLaw ν 0 := by
  have hc : blockOfArray 0=(fun _ : OverlapArray => (fun i : Fin 0 => Fin.elim0 i : OverlapBlock 0)) := by
    funext R i
    exact Fin.elim0 i
  simp only [blockLaw,hc,Measure.map_const,measure_univ,one_smul]

 

theorem GG_ultrametric_blocks_unique {μ ν : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    (hG' : (ν:Measure OverlapArray) GramArrays=1) (hgg' : GGIdentities ν)
    (hu' : (ν:Measure OverlapArray) UltrametricArrays=1)
    (hz : entryLaw μ 0 1=entryLaw ν 0 1) (r : ℕ) : blockLaw μ r=blockLaw ν r := by
  induction r with
  | zero => exact blockLaw_zero μ ν
  | succ r ih =>
    rw [← joinBlock_map_law hG r,← joinBlock_map_law hG' r,
      blockRowLaw_eq hG hgg hu hG' hgg' hu' hz r ih]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma abs_log_sub_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    |Real.log a-Real.log b| ≤ |a-b| *(a⁻¹+b⁻¹) := by
  have hab := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have hba := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div ha.ne' hb.ne'] at hab
  rw [Real.log_div hb.ne' ha.ne'] at hba
  have h1 : a/b-1=(a-b)*b⁻¹ := by field_simp
  have h2 : b/a-1=(b-a)*a⁻¹ := by field_simp
  rw [h1] at hab
  rw [h2] at hba
  have h3 := mul_le_mul_of_nonneg_right (le_abs_self (a-b)) (inv_nonneg.mpr hb.le)
  have h4 := mul_le_mul_of_nonneg_right (neg_le_abs (a-b)) (inv_nonneg.mpr ha.le)
  have h5 := mul_nonneg (abs_nonneg (a-b)) (inv_nonneg.mpr ha.le)
  have h6 := mul_nonneg (abs_nonneg (a-b)) (inv_nonneg.mpr hb.le)
  rw [abs_le]
  constructor <;> nlinarith

omit [Nonempty ι] in
lemma inv_sq_weighted_le (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i,p i=1)
    (u : ι → ℝ) (hu : ∀ i,0<u i) :
    (∑ i,p i*u i)⁻¹^2 ≤ ∑ i,p i*(u i)⁻¹^2 := by
  have h := (convexOn_zpow (𝕜:=ℝ) (-2)).map_sum_le (t:=Finset.univ)
    (w:=p) (p:=u) (fun i _ => hp i) hs (fun i _ => hu i)
  simpa only [smul_eq_mul,zpow_neg,zpow_natCast,inv_pow] using! h

lemma log_error_young {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : 0<t) :
    |Real.log a-Real.log b| ≤ t*(a-b)^2+(a⁻¹^2+b⁻¹^2)/(2*t) := by
  have h0 := sq_nonneg (2*t*|a-b|-(a⁻¹+b⁻¹))
  rw [sub_sq,mul_pow,mul_pow,sq_abs] at h0
  have h1 : |a-b| * (a⁻¹+b⁻¹) ≤ t*(a-b)^2+(a⁻¹+b⁻¹)^2/(4*t) := by
    have h : |a-b| * (a⁻¹+b⁻¹)-t*(a-b)^2 ≤ (a⁻¹+b⁻¹)^2/(4*t) := by
      apply (le_div_iff₀ (by positivity : 0<4*t)).mpr
      nlinarith only [h0]
    linarith only [h]
  have h2 := sq_nonneg (a⁻¹-b⁻¹)
  have h3 : (a⁻¹+b⁻¹)^2/(4*t) ≤ (a⁻¹^2+b⁻¹^2)/(2*t) := by
    apply (div_le_div_iff₀ (by positivity : 0<4*t) (by positivity : 0<2*t)).mpr
    nlinarith
  exact (abs_log_sub_le ha hb).trans (h1.trans (add_le_add_right h3 _))

lemma replicaMean_mono {r : ℕ} (x : ι → ℝ) {f g : (Fin r → ι) → ℝ}
    (h : ∀ σ,f σ≤g σ) : replicaMean x f≤replicaMean x g := by
  apply Finset.sum_le_sum
  intro σ _
  exact mul_le_mul_of_nonneg_left (h σ) (replicaWeight_nonneg _ _)

omit [Nonempty ι] in
lemma replicaMean_finiteSum {r : ℕ} {L : Type*} [Fintype L] (x : ι → ℝ)
    (f : L → (Fin r → ι) → ℝ) :
    replicaMean x (fun σ => ∑ i,f i σ)=∑ i,replicaMean x (f i) := by
  simp only [replicaMean,Finset.mul_sum]
  exact Finset.sum_comm

lemma replicaMean_centered_sq_sum (x f : ι → ℝ) (hf : ∑ s,weight x s*f s=0) (r : ℕ) :
    replicaMean x (fun σ : Fin r → ι => (∑ i,f (σ i))^2)=
      (r:ℝ)*∑ s,weight x s*(f s)^2 := by
  induction r with
  | zero => simp [replicaMean,replicaWeight]
  | succ r ih =>
    rw [replicaMean_snoc]
    have he (σ : Fin r → ι) :
        (∑ s,weight x s*(∑ i : Fin (r+1),f ((Fin.snoc σ s : Fin (r+1) → ι) i))^2)=
          (∑ i,f (σ i))^2+∑ s,weight x s*(f s)^2 := by
      simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
      have he' (s : ι) : weight x s*((∑ i,f (σ i))+f s)^2=
          weight x s*(∑ i,f (σ i))^2 + 2*(∑ i,f (σ i))*(weight x s*f s)+weight x s*(f s)^2 := by ring
      simp_rw [he']
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,sum_weight,hf]
      ring
    simp_rw [he]
    change replicaMean x (fun σ : Fin r → ι => (∑ i,f (σ i))^2+∑ s,weight x s*(f s)^2)=_
    rw [replicaMean_add,ih,replicaMean_const]
    push_cast
    ring

def empiricalMean {r : ℕ} (f : ι → ℝ) (σ : Fin r → ι) : ℝ := (∑ i,f (σ i))/(r:ℝ)

omit [Fintype ι] [Nonempty ι] in
lemma empiricalMean_positive {r : ℕ} (hr : 0<r) {f : ι → ℝ} (hf : ∀ i,0<f i)
    (σ : Fin r → ι) : 0<empiricalMean f σ := by
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  exact div_pos (Finset.sum_pos (fun i _ => hf (σ i)) Finset.univ_nonempty) (Nat.cast_pos.mpr hr)

lemma empiricalMean_variance {r : ℕ} (hr : 0<r) (x f : ι → ℝ) :
    replicaMean x (fun σ : Fin r → ι => (empiricalMean f σ-average x f)^2)=
      (average x (fun s => (f s-average x f)^2))/(r:ℝ) := by
  have hr' : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr hr.ne'
  have hcenter : ∑ s,weight x s*(f s-average x f)=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,sum_weight,one_mul,average]
    ring
  have he (σ : Fin r → ι) : (empiricalMean f σ-average x f)^2=
      ((r:ℝ)^2)⁻¹*(∑ i,(f (σ i)-average x f))^2 := by
    simp only [empiricalMean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  simp_rw [he]
  rw [replicaMean_const_mul,replicaMean_centered_sq_sum x _ hcenter]
  change _=(∑ s,weight x s*(f s-average x f)^2)/(r:ℝ)
  field_simp

lemma average_variance_le (x f : ι → ℝ) :
    average x (fun s => (f s-average x f)^2)≤average x (fun s => (f s)^2) := by
  have he (s) : weight x s*(f s-average x f)^2=weight x s*(f s)^2-
      2*average x f*(weight x s*f s)+(average x f)^2*weight x s := by ring
  simp only [average] at he ⊢
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,sum_weight,mul_one]
  nlinarith [sq_nonneg (∑ s,weight x s*f s)]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma replicaMean_empirical {r : ℕ} (hr : 0<r) (x f : ι → ℝ) :
    replicaMean x (empiricalMean (r:=r) f)=average x f := by
  have hr' : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr hr.ne'
  change replicaMean x (fun σ : Fin r → ι => (∑ i,f (σ i))/(r:ℝ))=average x f
  simp only [div_eq_inv_mul,replicaMean_const_mul,replicaMean_sum_same]
  change _=∑ s,weight x s*f s
  field_simp

omit [Fintype ι] [Nonempty ι] in
lemma empiricalMean_inv_sq {r : ℕ} (hr : 0<r) (f : ι → ℝ) (hf : ∀ i,0<f i)
    (σ : Fin r → ι) :
    (empiricalMean f σ)⁻¹^2≤empiricalMean (fun i => (f i)⁻¹^2) σ := by
  have hr' : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr hr.ne'
  have h := inv_sq_weighted_le (ι:=Fin r) (fun _ => (r:ℝ)⁻¹) (fun _ => by positivity)
    (by simp [hr']) (fun i => f (σ i)) (fun i => hf (σ i))
  simpa only [empiricalMean,← Finset.mul_sum,div_eq_inv_mul] using h

lemma replicaMean_inv_sq_empirical {r : ℕ} (hr : 0<r) (x f : ι → ℝ) (hf : ∀ i,0<f i) :
    replicaMean x (fun σ : Fin r → ι => (empiricalMean f σ)⁻¹^2)≤average x (fun i => (f i)⁻¹^2) := by
  exact (replicaMean_mono x (empiricalMean_inv_sq hr f hf)).trans_eq (replicaMean_empirical hr x _)

lemma average_inv_sq (x f : ι → ℝ) (hf : ∀ i,0<f i) :
    (average x f)⁻¹^2≤average x (fun i => (f i)⁻¹^2) :=
  inv_sq_weighted_le (weight x) (fun s => (weight_pos x s).le) (sum_weight x) f hf

lemma replicaMean_abs (x : ι → ℝ) {r : ℕ} (f : (Fin r → ι) → ℝ) :
    |replicaMean x f|≤replicaMean x (fun σ => |f σ|) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro σ _
  rw [abs_mul,abs_of_nonneg (replicaWeight_nonneg _ _)]

 

theorem empirical_log_error {r : ℕ} (hr : 0<r) (x f : ι → ℝ) (hf : ∀ i,0<f i)
    {t : ℝ} (ht : 0<t) :
    replicaMean x (fun σ : Fin r → ι => |Real.log (empiricalMean f σ)-Real.log (average x f)|) ≤
      (t/(r:ℝ))*average x (fun s => (f s)^2)+t⁻¹*average x (fun s => (f s)⁻¹^2) := by
  have h := replicaMean_mono x (fun σ : Fin r → ι =>
    log_error_young (empiricalMean_positive hr hf σ) (average_pos x f hf) ht)
  have he (σ : Fin r → ι) :
      t*(empiricalMean f σ-average x f)^2+((empiricalMean f σ)⁻¹^2+(average x f)⁻¹^2)/(2*t)=
      t*(empiricalMean f σ-average x f)^2+(2*t)⁻¹*(empiricalMean f σ)⁻¹^2+
        (2*t)⁻¹*(average x f)⁻¹^2 := by ring
  simp_rw [he] at h
  rw [replicaMean_add,replicaMean_add,replicaMean_const_mul,replicaMean_const_mul,
    replicaMean_const,empiricalMean_variance hr] at h
  have hv := div_le_div_of_nonneg_right (average_variance_le x f) (Nat.cast_nonneg r)
  have h1 := mul_le_mul_of_nonneg_left hv ht.le
  have h2 := mul_le_mul_of_nonneg_left (replicaMean_inv_sq_empirical hr x f hf)
    (by positivity : 0≤(2*t)⁻¹)
  have h3 := mul_le_mul_of_nonneg_left (average_inv_sq x f hf) (by positivity : 0≤(2*t)⁻¹)
  have h4 : (2*t)⁻¹+(2*t)⁻¹=t⁻¹ := by field_simp; norm_num
  calc
    _ ≤ t*((average x (fun s => (f s)^2))/(r:ℝ))+
        (2*t)⁻¹*average x (fun s => (f s)⁻¹^2)+(2*t)⁻¹*average x (fun s => (f s)⁻¹^2) :=
      h.trans (add_le_add (add_le_add h1 h2) h3)
    _ = _ := by rw [add_assoc,← add_mul,h4]; ring

lemma empirical_log_mean_error {r : ℕ} (hr : 0<r) (x f : ι → ℝ) (hf : ∀ i,0<f i)
    {t : ℝ} (ht : 0<t) :
    |replicaMean x (fun σ : Fin r → ι => Real.log (empiricalMean f σ))-Real.log (average x f)| ≤
      (t/(r:ℝ))*average x (fun s => (f s)^2)+t⁻¹*average x (fun s => (f s)⁻¹^2) := by
  rw [← replicaMean_const (r:=r) x (Real.log (average x f)),← replicaMean_sub]
  exact (replicaMean_abs x _).trans (empirical_log_error hr x f hf ht)

end SKCavity

end

end OAI
