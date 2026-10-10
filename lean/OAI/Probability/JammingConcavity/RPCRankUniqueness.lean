import Mathlib
import OAI.Probability.JammingConcavity.RPCPatternInsertionEvents

namespace OAI

/-! R P C Rank Uniqueness. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace MicroscopicJamming

lemma measurable_rpcStepLevel (ms : List ℝ) : Measurable (rpcStepLevel ms) := by
  induction ms with
  | nil => change Measurable (fun _ : ℝ => (0:ℕ)); exact measurable_const
  | cons m ms ih =>
    have he : rpcStepLevel (m::ms) = fun u => if m≤u then rpcStepLevel ms u+1 else rpcStepLevel ms u := by
      funext u
      simp only [rpcStepLevel,List.filter_cons,decide_eq_true_eq]
      split_ifs <;> simp
    rw [he]
    exact Measurable.ite (measurableSet_le measurable_const measurable_id) (ih.add_const 1) ih

lemma measurable_rankCovarianceArray (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ) :
    Measurable (rankCovarianceArray ms q Q) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hij : i=j
  · simp only [rankCovarianceArray,ite_eq_left hij]
    exact measurable_const
  · simp only [rankCovarianceArray,ite_eq_right hij]
    exact (measurable_of_countable q).comp ((measurable_rpcStepLevel ms).comp (by fun_prop))

def rankMeshArray (n : ℕ) : RankArray → RankArray :=
  rankCovarianceArray (rankMesh n) (fun i => (i:ℝ)/((n:ℝ)+1)) 1

lemma measurable_rankMeshArray (n : ℕ) : Measurable (rankMeshArray n) :=
  measurable_rankCovarianceArray _ _ _

lemma rankMeshArray_tendsto {U : RankArray} (hb : ∀ i j, U i j ∈ Set.Icc (0:ℝ) 1)
    (hd : ∀ i, U i i=1) : Tendsto (fun n => rankMeshArray n U) atTop (𝓝 U) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i=j
  · subst j
    simp only [rankMeshArray,rankCovarianceArray,ite_true,hd]
    exact tendsto_const_nhds
  · simpa only [rankMeshArray,rankCovarianceArray,ite_eq_right hij,rankMeshValue] using
      rankMeshValue_tendsto (hb i j)

lemma hasRPC_rankMesh_law {μ ν : Measure RankArray} (hμ : HasRPCFiniteRankLaws μ)
    (hν : HasRPCFiniteRankLaws ν) (n : ℕ) : μ.map (rankMeshArray n)=ν.map (rankMeshArray n) := by
  have hq0 : (0:ℝ)≤(0:ℕ)/((n:ℝ)+1) := by positivity
  have hqmon : ∀ i j : ℕ, i≤j → j≤(rankMesh n).length →
      (i:ℝ)/((n:ℝ)+1)≤(j:ℝ)/((n:ℝ)+1) := by
    intro i j hij _
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hqtop : ((rankMesh n).length:ℝ)/((n:ℝ)+1)≤1 := by
    simp only [rankMesh,List.length_map,List.length_range]
    rw [div_le_one (by positivity)]
    linarith
  exact (hμ _ (rankMesh_increasing n) (rankMesh_valid n) _ 1 hq0 hqmon hqtop).trans
    (hν _ (rankMesh_increasing n) (rankMesh_valid n) _ 1 hq0 hqmon hqtop).symm

 

theorem rpcRankLaw_unique (μ ν : Measure RankArray) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hbμ : ∀ᵐ U ∂μ, ∀ i j, 0≤U i j ∧ U i j≤1)
    (hbν : ∀ᵐ U ∂ν, ∀ i j, 0≤U i j ∧ U i j≤1)
    (hdμ : ∀ᵐ U ∂μ, ∀ i, U i i=1) (hdν : ∀ᵐ U ∂ν, ∀ i, U i i=1)
    (hrμ : HasRPCFiniteRankLaws μ) (hrν : HasRPCFiniteRankLaws ν) : μ=ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hlim (ξ : Measure RankArray) [IsProbabilityMeasure ξ]
      (hb : ∀ᵐ U ∂ξ, ∀ i j, 0≤U i j ∧ U i j≤1)
      (hd : ∀ᵐ U ∂ξ, ∀ i, U i i=1) :
      Tendsto (fun n => ∫ U, f (rankMeshArray n U) ∂ξ) atTop (𝓝 (∫ U, f U ∂ξ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (f.continuous.measurable.comp (measurable_rankMeshArray n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ fun U => f.norm_coe_le_norm _
    · filter_upwards [hb,hd] with U hb hd
      exact f.continuous.continuousAt.tendsto.comp (rankMeshArray_tendsto hb hd)
  have he (n : ℕ) : (∫ U, f (rankMeshArray n U) ∂μ)=(∫ U, f (rankMeshArray n U) ∂ν) := by
    rw [← integral_map (measurable_rankMeshArray n).aemeasurable f.continuous.aestronglyMeasurable,
      ← integral_map (measurable_rankMeshArray n).aemeasurable f.continuous.aestronglyMeasurable,
      hasRPC_rankMesh_law hrμ hrν]
  have hm := hlim μ hbμ hdμ
  simp_rw [he] at hm
  exact tendsto_nhds_unique hm (hlim ν hbν hdν)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def rankLabelEvent {n : ℕ} (ms : List ℝ) (h : PatternLabelling ms.length n) :
    Set (Fin (n+1) → Fin (n+1) → ℝ) := {R | ∀ i j, rpcStepLevel ms (R i j)=h.signature i j}

lemma measurableSet_rankLabelEvent {n : ℕ} (ms : List ℝ) (h : PatternLabelling ms.length n) :
    MeasurableSet (rankLabelEvent ms h) := by
  simp only [rankLabelEvent,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_eq_fun ((measurable_rpcStepLevel ms).comp (by fun_prop)) measurable_const

lemma rankLabelEvent_iff_sample {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, m ≤ 1) (h : PatternLabelling ms.length n)
    (hh : ValidReplicaPattern ms.length h.pattern) :
    R ∈ rankLabelEvent ms h ↔ RPCSamplePattern ms.length h.pattern
      (fun j => rankProfilePath ms (R (h.index.symm j))) := by
  rw [h.sample_iff_signature hh (fun i => rankProfilePath ms (R i))]
  exact forall_congr' fun i => forall_congr' fun j => by
    rw [rankProfilePath_rows hR ms hms h01]

lemma cascadeSharedEdges_symm (k : ℕ) (x y : CascadePath k) :
    cascadeSharedEdges k x y=cascadeSharedEdges k y x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cascadeSharedEdges]
    by_cases h : x.1=y.1
    · rw [ite_eq_left h,ite_eq_left h.symm,ih]
    · rw [ite_eq_right h,ite_eq_right (Ne.symm h)]

def rankMixedSample {n : ℕ} (R : Fin (n+1) → Fin (n+1) → ℝ) (ms : List ℝ)
    (z : Fin (n+1) × ℝ) : Fin (n+2) → CascadePath ms.length :=
  Fin.lastCases (rankProfilePath ms (rankLink R z.1 z.2)) (fun i => rankProfilePath ms (R i))

lemma rankMixedSample_signature {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, m ≤ 1) (z : Fin (n+1) × ℝ) (i j : Fin (n+2)) :
    cascadeSharedEdges ms.length (rankMixedSample R ms z i) (rankMixedSample R ms z j)=
      rpcStepLevel ms (rankInsert R z.1 z.2 i j) := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp only [rankMixedSample,rankInsert,Fin.lastCases_last,Fin.lastCases_castSucc]
  · rw [cascadeSharedEdges_self]
    unfold rpcStepLevel
    rw [List.filter_eq_self.mpr (fun m hm => by simpa using h01 m hm)]
  · exact rankProfilePath_link hR ms hms h01 j z.1 z.2
  · rw [cascadeSharedEdges_symm]
    exact rankProfilePath_link hR ms hms h01 i z.1 z.2
  · exact rankProfilePath_rows hR ms hms h01 i j

lemma rankLabelEvent_insert_iff {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, m ≤ 1) (h : PatternLabelling ms.length n)
    (hh : ValidReplicaPattern ms.length h.pattern) (s : PatternSite ms.length h.pattern)
    (z : Fin (n+1) × ℝ) :
    rankInsert R z.1 z.2 ∈ rankLabelEvent ms (h.extend s) ↔
      RPCSamplePattern ms.length (patternExtension ms.length h.pattern s).next
        (insertedSample (patternExtension ms.length h.pattern s)
          (fun j => rankProfilePath ms (R (h.index.symm j))) (rankProfilePath ms (rankLink R z.1 z.2))) := by
  have he := h.extend_sample s (rankMixedSample R ms z)
  simp only [rankMixedSample,Fin.lastCases_castSucc,Fin.lastCases_last] at he
  rw [he]
  change _ ↔ RPCSamplePattern ms.length (h.extend s).pattern
    (fun j => rankMixedSample R ms z ((h.extend s).index.symm j))
  rw [(h.extend s).sample_iff_signature (patternExtension_valid_generic _ _ hh s) (rankMixedSample R ms z)]
  exact forall_congr' fun i => forall_congr' fun j => by
    rw [rankMixedSample_signature hR ms hms h01]

lemma rankLabelEvent_insert_parent {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, m ≤ 1) (h : PatternLabelling ms.length n)
    (hh : ValidReplicaPattern ms.length h.pattern) (s : PatternSite ms.length h.pattern)
    (z : Fin (n+1) × ℝ) (hz : rankInsert R z.1 z.2 ∈ rankLabelEvent ms (h.extend s)) :
    R ∈ rankLabelEvent ms h := by
  have hn := (rankLabelEvent_insert_iff hR ms hms h01 h hh s z).mp hz
  exact (rankLabelEvent_iff_sample hR ms hms h01 h hh).mpr
    (rpcSamplePattern_delete _ _ hh s _ _ hn)

lemma rankLabelEvent_kernel {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (h : PatternLabelling ms.length n)
    (hh : ValidReplicaPattern ms.length h.pattern) (s : PatternSite ms.length h.pattern) :
    (rankInnovationLaw n) {z | rankInsert R z.1 z.2 ∈ rankLabelEvent ms (h.extend s)} =
      if R ∈ rankLabelEvent ms h then ENNReal.ofReal (patternSiteWeight ms 0 h.pattern s/((n:ℝ)+1)) else 0 := by
  have hmax : ∀ m ∈ ms, m ≤ 1 := fun m hm => (h01 m hm).2.le
  by_cases hx : R ∈ rankLabelEvent ms h
  · rw [ite_eq_left hx]
    have he : {z : Fin (n+1) × ℝ | rankInsert R z.1 z.2 ∈ rankLabelEvent ms (h.extend s)} =
        rankPatternInsertEvent R ms 0 0 h.pattern h.index.symm s := by
      ext z
      change (rankInsert R z.1 z.2 ∈ rankLabelEvent ms (h.extend s)) ↔ _
      rw [rankLabelEvent_insert_iff hR ms hms hmax h hh s z]
      change _ ↔ 0 ≤ rankLink R z.1 z.2 0 ∧ _
      exact (and_iff_right (le_min (hR.2.2.1 0 z.1).1 (le_max_of_le_left (rankBirth_nonneg R z.1)))).symm
    rw [he]
    have hc (q : Fin (n+1)) : 0 ≤ R 0 q ↔ ∃ j, h.index.symm j=q := by
      exact iff_of_true (hR.2.2.1 0 q).1 (h.index.symm.surjective q)
    have hr := rankPatternInsertEvent_real hR ms hms h01 0 le_rfl zero_le_one
      (fun m hm => (h01 m hm).1) 0 h.pattern hh h.index.symm h.index.symm.injective hc
      ((rankLabelEvent_iff_sample hR ms hms hmax h hh).mp hx) s
    rw [← hr]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  · rw [ite_eq_right hx]
    have he : {z : Fin (n+1) × ℝ | rankInsert R z.1 z.2 ∈ rankLabelEvent ms (h.extend s)}=∅ := by
      ext z
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      intro hz
      exact hx (rankLabelEvent_insert_parent hR ms hms hmax h hh s z hz)
    rw [he,measure_empty]

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma rankGrowing_congr (n : ℕ) {z z' : RankSeed} (h : ∀ i < n, z i=z' i) :
    rankGrowing n z=rankGrowing n z' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rankGrowing,ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),h n (Nat.lt_succ_self _)]

def rankPastEmbed (n : ℕ) (z : (i : ↑(Finset.range n)) → Fin (i.val+1) × ℝ) : RankSeed :=
  fun i => if h : i < n then z ⟨i,Finset.mem_range.mpr h⟩ else (0,0)

lemma continuous_rankPastEmbed (n : ℕ) : Continuous (rankPastEmbed n) := by
  apply continuous_pi
  intro i
  by_cases h : i < n
  · simpa only [rankPastEmbed,dite_eq_left h] using
      (continuous_apply (⟨i,Finset.mem_range.mpr h⟩ : ↑(Finset.range n)))
  · simpa only [rankPastEmbed,dite_eq_right h] using
      (continuous_const : Continuous (fun _ : (i : ↑(Finset.range n)) → Fin (i.val+1) × ℝ => ((0,0) : Fin (i+1) × ℝ)))

lemma rankGrowing_past (n : ℕ) (z : RankSeed) :
    rankGrowing n (rankPastEmbed n (fun i => z i))=rankGrowing n z := by
  apply rankGrowing_congr
  intro i hi
  simp [rankPastEmbed,hi]

lemma rankGrowing_indep_innovation (n : ℕ) :
    IndepFun (rankGrowing n) (fun z : RankSeed => z n) rankSeedLaw := by
  have hcoords : iIndepFun (fun i (z : RankSeed) => z i) rankSeedLaw :=
    iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  have hdis : Disjoint (Finset.range n) {n} := by simp
  have h := hcoords.indepFun_finset (Finset.range n) {n} hdis (fun _ => measurable_pi_apply _)
  have hc := h.comp ((continuous_rankGrowing n).comp (continuous_rankPastEmbed n)).measurable
    (measurable_pi_apply (⟨n,by simp⟩ : ↑({n} : Finset ℕ)))
  convert hc using 1
  · funext z
    exact (rankGrowing_past n z).symm
  · rfl

lemma rankGrowing_joint_law (n : ℕ) :
    rankSeedLaw.map (fun z => (rankGrowing n z,z n)) =
      (rankSeedLaw.map (rankGrowing n)).prod (rankInnovationLaw n) := by
  rw [(rankGrowing_indep_innovation n).map_prod_eq_prod_map_map
    (continuous_rankGrowing n).measurable.aemeasurable (measurable_pi_apply n).aemeasurable]
  congr 1
  exact Measure.infinitePi_map_eval rankInnovationLaw n

lemma rankGrowing_succ_law (n : ℕ) :
    rankSeedLaw.map (rankGrowing (n+1)) =
      ((rankSeedLaw.map (rankGrowing n)).prod (rankInnovationLaw n)).map
        (fun z => rankInsert z.1 z.2.1 z.2.2) := by
  rw [← rankGrowing_joint_law,Measure.map_map (continuous_rankInsert _).measurable
    ((continuous_rankGrowing n).measurable.prodMk (measurable_pi_apply n))]
  rfl

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma measurableSet_finiteRank (n : ℕ) :
    MeasurableSet {R : Fin n → Fin n → ℝ | FiniteRank R} := by
  simp only [FiniteRank,ofPred_and,ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) measurable_const
  · apply MeasurableSet.inter
    · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_eq_fun (by fun_prop) (by fun_prop)
    · apply MeasurableSet.inter
      · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
          (measurableSet_le measurable_const (by fun_prop)).inter (measurableSet_le (by fun_prop) measurable_const)
      · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
          measurableSet_le (by fun_prop) (by fun_prop)

lemma rankGrowing_law_finiteRank (n : ℕ) :
    ∀ᵐ R ∂rankSeedLaw.map (rankGrowing n), FiniteRank R := by
  apply (ae_map_iff (continuous_rankGrowing n).measurable.aemeasurable (measurableSet_finiteRank (n+1))).mpr
  exact rankSeed_valid.mono fun z hz => rankGrowing_finiteRank hz n

lemma rankGrowing_pattern (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) {n : ℕ} (h : PatternLabelling ms.length n)
    (hh : ReachablePatternLabelling ms.length h) :
    (rankSeedLaw.map (rankGrowing n)) (rankLabelEvent ms h)=
      ENNReal.ofReal (rpcPatternProduct ms 0 h.pattern) := by
  induction hh with
  | singleton =>
    rw [Measure.map_apply (continuous_rankGrowing 0).measurable (measurableSet_rankLabelEvent ms _)]
    have hs : rankGrowing 0 ⁻¹' rankLabelEvent ms (PatternLabelling.singleton ms.length)=univ := by
      apply Set.eq_univ_of_forall
      intro z
      have hR : FiniteRank (rankGrowing 0 z) := by
        refine ⟨fun _ => rfl,fun _ _ => rfl,fun _ _ => ?_,fun _ _ _ => ?_⟩ <;> norm_num [rankGrowing]
      apply (rankLabelEvent_iff_sample hR ms hms (fun m hm => (h01 m hm).2.le) _
        (singletonReplicaPattern_valid _)).mpr
      exact rpcSamplePattern_singleton _ _
    rw [hs]
    simp [PatternLabelling.singleton,singletonReplicaPattern_product]
  | @extend n h hh s ih =>
    have hm := measurableSet_rankLabelEvent ms (h.extend s)
    have hf : Measurable (fun z : (Fin (n+1) → Fin (n+1) → ℝ) × (Fin (n+1) × ℝ) =>
        rankInsert z.1 z.2.1 z.2.2) := (continuous_rankInsert _).measurable
    rw [rankGrowing_succ_law,Measure.map_apply hf hm,Measure.prod_apply (hf hm)]
    have hp : (∫⁻ R, (rankInnovationLaw n) (Prod.mk R ⁻¹'
          ((fun z : (Fin (n+1) → Fin (n+1) → ℝ) × (Fin (n+1) × ℝ) =>
            rankInsert z.1 z.2.1 z.2.2) ⁻¹' rankLabelEvent ms (h.extend s)))
          ∂rankSeedLaw.map (rankGrowing n)) =
        ∫⁻ R, (rankLabelEvent ms h).indicator
          (fun _ => ENNReal.ofReal (patternSiteWeight ms 0 h.pattern s/((n:ℝ)+1))) R
          ∂rankSeedLaw.map (rankGrowing n) := by
      apply lintegral_congr_ae
      filter_upwards [rankGrowing_law_finiteRank n] with R hR
      exact rankLabelEvent_kernel hR ms hms h01 h hh.valid s
    rw [hp,lintegral_indicator_const (measurableSet_rankLabelEvent ms h),ih]
    have hp := (rpcInsertion_properties (patternExtension_insertion ms 0 h.pattern s) hms h01
      le_rfl zero_lt_one (fun m hm => (h01 m hm).1) hh.valid).2.2.2
    have hn := rpcPatternProduct_nonneg ms hms h01 0 (fun m hm => (h01 m hm).1) h.pattern
    change _=ENNReal.ofReal (rpcPatternProduct ms 0 (patternExtension ms.length h.pattern s).next)
    rw [hp,h.size,Nat.cast_add,Nat.cast_one,sub_zero,ENNReal.ofReal_mul hn,mul_comm]

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace MicroscopicJamming

def rankReindex (p : Equiv.Perm ℕ) (U : RankArray) : RankArray := fun i j => U (p i) (p j)
lemma measurable_rankReindex (p : Equiv.Perm ℕ) : Measurable (rankReindex p) := by
  unfold rankReindex
  fun_prop

lemma infinitePi_exchangeable {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsProbabilityMeasure μ] (p : Equiv.Perm ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).map (fun x i => x (p i)) = Measure.infinitePi (fun _ : ℕ => μ) := by
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) p.symm
  convert h using 1
  congr 1
  funext x i
  simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft_apply]

lemma cascadeReplicaLaw_exchangeable (ms : List ℝ) (p : Equiv.Perm ℕ) :
    (cascadeReplicaLaw ms).map (fun x i => x (p i)) = cascadeReplicaLaw ms := by
  let := cascadeLeafLaw_probability ms
  have hS : Measurable (fun x : ℕ → CascadePath ms.length => fun i => x (p i)) := by fun_prop
  ext A hA
  rw [Measure.map_apply hS hA,cascadeReplicaLaw,
    Measure.bind_apply (hS hA) (measurable_cascadeReplicaKernel ms).aemeasurable,
    Measure.bind_apply hA (measurable_cascadeReplicaKernel ms).aemeasurable]
  apply lintegral_congr
  intro ω
  rw [← Measure.map_apply hS hA,infinitePi_exchangeable]

lemma measurable_cascadeCovarianceArray (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ) :
    Measurable (cascadeCovarianceArray ms q Q) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hij : i=j
  · simp only [cascadeCovarianceArray,ite_eq_left hij]; exact measurable_const
  · simp only [cascadeCovarianceArray,ite_eq_right hij]
    exact (measurable_of_countable (fun z : CascadePath ms.length × CascadePath ms.length =>
      q (cascadeSharedEdges ms.length z.1 z.2))).comp
        (show Measurable (fun x : ℕ → CascadePath ms.length => (x i,x j)) by fun_prop)

lemma rankReindex_cascadeCovariance (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ) (p : Equiv.Perm ℕ) :
    rankReindex p ∘ cascadeCovarianceArray ms q Q =
      cascadeCovarianceArray ms q Q ∘ (fun x i => x (p i)) := by
  funext x i j
  simp [rankReindex,cascadeCovarianceArray,p.injective.eq_iff]

lemma cascadeCovarianceLaw_exchangeable (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ) (p : Equiv.Perm ℕ) :
    ((cascadeReplicaLaw ms).map (cascadeCovarianceArray ms q Q)).map (rankReindex p)=
      (cascadeReplicaLaw ms).map (cascadeCovarianceArray ms q Q) := by
  rw [Measure.map_map (measurable_rankReindex p) (measurable_cascadeCovarianceArray _ _ _),
    rankReindex_cascadeCovariance,
    ← Measure.map_map (measurable_cascadeCovarianceArray _ _ _) (by fun_prop),
    cascadeReplicaLaw_exchangeable]

lemma hasRPCFiniteRankLaws_reindex {μ : Measure RankArray} (hμ : HasRPCFiniteRankLaws μ)
    (p : Equiv.Perm ℕ) : HasRPCFiniteRankLaws (μ.map (rankReindex p)) := by
  intro ms hms h01 q Q hq0 hq hQ
  have he : rankCovarianceArray ms q Q ∘ rankReindex p =
      rankReindex p ∘ rankCovarianceArray ms q Q := by
    funext U i j
    simp [rankReindex,rankCovarianceArray,p.injective.eq_iff]
  rw [Measure.map_map (measurable_rankCovarianceArray _ _ _) (measurable_rankReindex p),he,
    ← Measure.map_map (measurable_rankReindex p) (measurable_rankCovarianceArray _ _ _),
    hμ ms hms h01 q Q hq0 hq hQ,cascadeCovarianceLaw_exchangeable]

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def cascadeFiniteEdges {n : ℕ} (ms : List ℝ) (x : ℕ → CascadePath ms.length) :
    Fin (n+1) → Fin (n+1) → ℕ :=
  fun i j => cascadeSharedEdges ms.length (x i) (x j)

lemma measurable_cascadeFiniteEdges (n : ℕ) (ms : List ℝ) :
    Measurable (cascadeFiniteEdges (n:=n) ms) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (measurable_of_countable (fun z : CascadePath ms.length × CascadePath ms.length =>
    cascadeSharedEdges ms.length z.1 z.2)).comp
      (show Measurable (fun x : ℕ → CascadePath ms.length => (x i.val,x j.val)) by fun_prop)

lemma cascadeReplicaLaw_pattern (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) {n : ℕ} (h : PatternLabelling ms.length n)
    (hh : ValidReplicaPattern ms.length h.pattern) :
    (cascadeReplicaLaw ms) {x | cascadeFiniteEdges ms x=h.signature} =
      ENNReal.ofReal (rpcPatternProduct ms 0 h.pattern) := by
  let f (x : ℕ → CascadePath ms.length) (j : PatternIndex ms.length h.pattern) := x (h.index.symm j).val
  have hf : Measurable f := by unfold f; fun_prop
  have hA : MeasurableSet {x | RPCSamplePattern ms.length h.pattern x} := Set.to_countable _ |>.measurableSet
  have he : {x | cascadeFiniteEdges ms x=h.signature} = f ⁻¹' {x | RPCSamplePattern ms.length h.pattern x} := by
    ext x
    change (cascadeFiniteEdges ms x=h.signature) ↔
      RPCSamplePattern ms.length h.pattern (fun j => x (h.index.symm j).val)
    rw [h.sample_iff_signature hh (fun i => x i.val)]
    exact funext_iff.trans (forall_congr' fun i => funext_iff)
  rw [he,cascadeReplicaLaw,Measure.bind_apply (hf hA) (measurable_cascadeReplicaKernel ms).aemeasurable]
  have hi (ω : CascadeTree ms.length) :
      (Measure.infinitePi (fun _ : ℕ => cascadeLeafLaw ms ω))
        (f ⁻¹' {x | RPCSamplePattern ms.length h.pattern x}) = sampledPatternProbability ms h.pattern ω := by
    let := cascadeLeafLaw_probability ms ω
    have hm := Measure.map_infinitePi_infinitePi_of_inj
      (P:=fun _ : ℕ => cascadeLeafLaw ms ω)
      (f:=fun j : PatternIndex ms.length h.pattern => (h.index.symm j).val)
      (Fin.val_injective.comp h.index.symm.injective)
    rw [← Measure.map_apply hf hA,hm,Measure.infinitePi_eq_pi]
    rfl
  simp_rw [hi]
  have hp := (rpcSamplePattern ms hms h01).2 0 le_rfl (fun m hm => (h01 m hm).1) h.pattern hh
  simpa using hp

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def rankFiniteSteps {n : ℕ} (ms : List ℝ) (R : Fin (n+1) → Fin (n+1) → ℝ) :
    Fin (n+1) → Fin (n+1) → ℕ := fun i j => rpcStepLevel ms (R i j)

lemma measurable_rankFiniteSteps (n : ℕ) (ms : List ℝ) : Measurable (rankFiniteSteps (n:=n) ms) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (measurable_rpcStepLevel ms).comp (by fun_prop)

lemma rankFiniteSteps_preimage {n : ℕ} (ms : List ℝ) (h : PatternLabelling ms.length n) :
    rankFiniteSteps ms ⁻¹' {h.signature}=rankLabelEvent ms h := by
  ext R
  simp only [Set.mem_preimage,Set.mem_singleton_iff,rankFiniteSteps,rankLabelEvent,Set.mem_ofPred_eq,funext_iff]

lemma rankFiniteSteps_covered {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, m ≤ 1) :
    ∃ h : PatternLabelling ms.length n, ReachablePatternLabelling ms.length h ∧
      rankFiniteSteps ms R=h.signature := by
  obtain ⟨h,hh,hx⟩ := reachablePatternLabelling_covers ms.length n (fun i => rankProfilePath ms (R i))
  refine ⟨h,hh,?_⟩
  have hr := (h.sample_iff_signature hh.valid (fun i => rankProfilePath ms (R i))).mp hx
  funext i j
  exact (rankProfilePath_rows hR ms hms h01 i j).symm.trans (hr i j)

lemma cascadeFiniteEdges_covered (n : ℕ) (ms : List ℝ) (x : ℕ → CascadePath ms.length) :
    ∃ h : PatternLabelling ms.length n, ReachablePatternLabelling ms.length h ∧
      cascadeFiniteEdges ms x=h.signature := by
  obtain ⟨h,hh,hx⟩ := reachablePatternLabelling_covers ms.length n (fun i => x i.val)
  exact ⟨h,hh,funext fun i => funext fun j => (h.sample_iff_signature hh.valid (fun i => x i.val)).mp hx i j⟩

 

lemma rankGrowing_finiteSteps_law (n : ℕ) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    (rankSeedLaw.map (rankGrowing n)).map (rankFiniteSteps ms)=
      (cascadeReplicaLaw ms).map (cascadeFiniteEdges (n:=n) ms) := by
  apply Measure.ext_of_singleton
  intro B
  rw [Measure.map_apply (measurable_rankFiniteSteps n ms) (measurableSet_singleton _),
    Measure.map_apply (measurable_cascadeFiniteEdges n ms) (measurableSet_singleton _)]
  by_cases hb : ∃ h : PatternLabelling ms.length n, ReachablePatternLabelling ms.length h ∧ h.signature=B
  · obtain ⟨h,hh,rfl⟩ := hb
    rw [rankFiniteSteps_preimage,rankGrowing_pattern ms hms h01 h hh]
    exact (cascadeReplicaLaw_pattern ms hms h01 h hh.valid).symm
  · have hl : (rankSeedLaw.map (rankGrowing n)) (rankFiniteSteps ms ⁻¹' {B})=0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [rankGrowing_law_finiteRank n] with R hR hB
      obtain ⟨h,hh,hs⟩ := rankFiniteSteps_covered hR ms hms (fun m hm => (h01 m hm).2.le)
      exact hb ⟨h,hh,hs.symm.trans hB⟩
    have hr : cascadeFiniteEdges (n:=n) ms ⁻¹' {B}=∅ := by
      ext x
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
      intro hB
      obtain ⟨h,hh,hs⟩ := cascadeFiniteEdges_covered n ms x
      exact hb ⟨h,hh,hs.symm.trans hB⟩
    rw [hl,hr,measure_empty]

end MicroscopicJamming

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def coordinateLaw (ε : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • gaussianReal 0 (Real.toNNReal (1 - ε)) +
  (1 / 2 : ℝ≥0∞) • gaussianReal 0 (Real.toNNReal (1 + ε))

instance coordinateLaw_probability (ε : ℝ) : IsProbabilityMeasure (coordinateLaw ε) := by
  constructor
  simpa [coordinateLaw] using ENNReal.inv_two_add_inv_two

lemma coordinateLaw_mgf {ε : ℝ} (he : ε ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    mgf id (coordinateLaw ε) t =
      (Real.exp ((1-ε)*t^2/2) + Real.exp ((1+ε)*t^2/2))/2 := by
  have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal (1-ε)) t
  have h2 := integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal (1+ε)) t
  unfold coordinateLaw mgf
  simp only [id_eq]
  rw [integral_add_measure (h1.smul_measure (by norm_num))
    (h2.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure]
  change (1/2 : ℝ≥0∞).toReal * mgf id (gaussianReal 0 (Real.toNNReal (1-ε))) t +
    (1/2 : ℝ≥0∞).toReal * mgf id (gaussianReal 0 (Real.toNNReal (1+ε))) t = _
  simp only [mgf_id_gaussianReal, zero_mul, zero_add,
    Real.coe_toNNReal _ (by linarith [he.2] : 0 ≤ 1-ε),
    Real.coe_toNNReal _ (by linarith [he.1] : 0 ≤ 1+ε)]
  norm_num
  ring

lemma coordinateLaw_subGaussian {ε : ℝ} (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) :
    HasSubgaussianMGF id (3/2) (coordinateLaw ε) := by
  constructor
  · intro t
    apply Integrable.add_measure
    · exact (integrable_exp_mul_gaussianReal t).smul_measure (by norm_num)
    · exact (integrable_exp_mul_gaussianReal t).smul_measure (by norm_num)
  · intro t
    rw [coordinateLaw_mgf ⟨he.1, by linarith [he.2]⟩]
    have hl : Real.exp ((1-ε)*t^2/2) ≤ Real.exp ((3/2:ℝ)*t^2/2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg t, mul_nonneg he.1 (sq_nonneg t)]
    have hr : Real.exp ((1+ε)*t^2/2) ≤ Real.exp ((3/2:ℝ)*t^2/2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr he.2) (sq_nonneg t)]
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith

lemma mixture_linear_subGaussian {ι : Type*} [Fintype ι] {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (w : ι → ℝ) :
    HasSubgaussianMGF (fun a : ι → ℝ => ∑ i, w i * a i)
      (∑ i, (NNReal.mk ((w i)^2) (sq_nonneg (w i))) * (3/2))
      (Measure.pi fun _ : ι => coordinateLaw ε) := by
  classical
  have hi := iIndepFun_pi (μ := fun _ : ι => coordinateLaw ε)
    (X := fun i x => w i * x) (fun _ => (measurable_const.mul measurable_id).aemeasurable)
  have hc : ∀ i ∈ (Finset.univ : Finset ι),
      HasSubgaussianMGF (fun a : ι → ℝ => w i * a i)
        ((NNReal.mk ((w i)^2) (sq_nonneg (w i))) * (3/2))
        (Measure.pi fun _ : ι => coordinateLaw ε) := by
    intro i _
    have h := (coordinateLaw_subGaussian he).const_mul (w i)
    rw [← (measurePreserving_eval (fun _ : ι => coordinateLaw ε) i).map_eq] at h
    exact h.of_map (measurable_pi_apply i).aemeasurable
  simpa using HasSubgaussianMGF.sum_of_iIndepFun hi hc

end MicroscopicJamming

end

end OAI
