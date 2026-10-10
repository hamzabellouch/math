import OAI.Analysis.StrictMeans.CriticalRanks

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

instance diskFamily_standardBorel : StandardBorelSpace DiskFamily := by
  let := TopologicalSpace.metrizableSpaceMetric DiskFamily
  infer_instance

instance rankParameters_standardBorel (k : ℝ) : StandardBorelSpace (RankParameters k) :=
  ((measurableSet_goodPairs k).preimage measurable_fst).standardBorel

def RankPairRelation (k : ℝ) (p : RankParameters k) (w : UpperHalfPlane) : Prop :=
  p.1.2 ∈ signedCriticalFiber k p.1.1.1 p.1.1.2 true ∧
  w ∈ signedCriticalFiber k p.1.1.1 p.1.1.2 false ∧
  criticalRank k p.1.1.1 p.1.1.2 false w = criticalRank k p.1.1.1 p.1.1.2 true p.1.2 ∧
  criticalHeight k (halfPlaneFunction p.1.1.1) p.1.2 <
    criticalHeight k (halfPlaneFunction p.1.1.1) w

lemma measurableSet_rankPairRelation {k : ℝ} (hk : 0 < k) :
    MeasurableSet {q : RankParameters k × UpperHalfPlane | RankPairRelation k q.1 q.2} := by
  have hGz := (continuous_criticalMap k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hGw := (continuous_criticalMap k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hξ : Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  have hJz := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hJw := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hHz := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hHw := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  let replace : RankParameters k × UpperHalfPlane → RankParameters k :=
    fun q => ⟨(q.1.1.1,q.2),q.1.2⟩
  have hr : Measurable replace :=
    ((measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
      measurable_snd).subtype_mk
  have hm1 := (measurable_criticalRank hk false).comp hr
  have hm2 : Measurable (fun q : RankParameters k × UpperHalfPlane =>
      criticalRank k q.1.1.1.1 q.1.1.1.2 true q.1.1.2) :=
    (measurable_criticalRank hk true).comp measurable_fst
  exact ((isClosed_eq hGz hξ).measurableSet.inter (isOpen_lt continuous_const hJz).measurableSet).inter
    (((isClosed_eq hGw hξ).measurableSet.inter (isOpen_lt hJw continuous_const).measurableSet).inter
      ((measurableSet_eq_fun hm1 hm2).inter (isOpen_lt hHz hHw).measurableSet))

lemma rankPairRelation_unique {k : ℝ} (hk : 0 < k) {p : RankParameters k}
    {v w : UpperHalfPlane} (hv : RankPairRelation k p v) (hw : RankPairRelation k p w) : v = w := by
  exact criticalRank_injOn hk p.2 false hv.2.1 hw.2.1 (hv.2.2.1.trans hw.2.2.1.symm)

def rankPairingDomain (k : ℝ) : Set (RankParameters k) :=
  {p | ∃ w, RankPairRelation k p w}

lemma measurableSet_rankPairingDomain {k : ℝ} (hk : 0 < k) :
    MeasurableSet (rankPairingDomain k) := by
  let R := {q : RankParameters k × UpperHalfPlane | RankPairRelation k q.1 q.2}
  have hR : MeasurableSet R := measurableSet_rankPairRelation hk
  let : StandardBorelSpace R := hR.standardBorel
  let π : R → RankParameters k := fun q => q.1.1
  have hπ : MeasurableEmbedding π :=
    (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (by
      intro q r he
      apply Subtype.ext
      apply Prod.ext he
      have hr : RankPairRelation k q.1.1 r.1.2 := by
        change q.val.fst = r.val.fst at he
        rw [he]
        exact r.property
      exact rankPairRelation_unique hk q.2 hr)
  have he : π '' univ = rankPairingDomain k := by
    ext p
    constructor
    · rintro ⟨q,_,rfl⟩
      exact ⟨q.1.2,q.2⟩
    · rintro ⟨w,hw⟩
      exact ⟨⟨(p,w),hw⟩,mem_univ _,rfl⟩
  rw [← he]
  exact hπ.measurableSet_image.mpr MeasurableSet.univ

abbrev AvailableRankPair (k : ℝ) := rankPairingDomain k

def availableRankPartner (k : ℝ) (p : AvailableRankPair k) : UpperHalfPlane :=
  Classical.choose p.2

lemma availableRankPartner_spec (k : ℝ) (p : AvailableRankPair k) :
    RankPairRelation k p.1 (availableRankPartner k p) := Classical.choose_spec p.2

lemma measurable_availableRankPartner {k : ℝ} (hk : 0 < k) :
    Measurable (availableRankPartner k) := by
  let : StandardBorelSpace (AvailableRankPair k) := (measurableSet_rankPairingDomain hk).standardBorel
  apply measurable_of_borel_graph
  let π : AvailableRankPair k × UpperHalfPlane → RankParameters k × UpperHalfPlane :=
    fun q => (q.1.1, q.2)
  have hπ : Measurable π := by
    exact (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hm := (measurableSet_rankPairRelation hk).preimage hπ
  convert hm using 1
  ext q
  constructor
  · intro he
    change RankPairRelation k q.1.1 q.2
    rw [← he]
    exact availableRankPartner_spec k q.1
  · intro hr
    exact rankPairRelation_unique hk (availableRankPartner_spec k q.1) hr

lemma availableRankPartner_injOn_fiber {k : ℝ} (hk : 0 < k)
    {p q : AvailableRankPair k} (hf : p.1.1.1 = q.1.1.1)
    (he : availableRankPartner k p = availableRankPartner k q) : p.1.1.2 = q.1.1.2 := by
  have hp := availableRankPartner_spec k p
  have hq := availableRankPartner_spec k q
  have hff := congrArg Prod.fst hf
  have hfξ := congrArg Prod.snd hf
  have hq' : q.1.1.2 ∈ signedCriticalFiber k p.1.1.1.1 p.1.1.1.2 true := by
    rw [hff, hfξ]
    exact hq.1
  apply criticalRank_injOn hk p.1.2 true hp.1 hq'
  calc
    _ = criticalRank k p.1.1.1.1 p.1.1.1.2 false (availableRankPartner k p) := hp.2.2.1.symm
    _ = criticalRank k q.1.1.1.1 q.1.1.1.2 false (availableRankPartner k q) := by rw [he, hff, hfξ]
    _ = _ := by rw [hff, hfξ]; exact hq.2.2.1

end
end StrictInverseFirstPower

end

end OAI
