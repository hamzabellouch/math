import OAI.Analysis.StrictMeans.RankCovariance

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def availableSource (k : ℝ) (p : AvailableRankPair k) : DiskFamily × UpperHalfPlane :=
  (p.1.1.1.1,p.1.1.2)

lemma availableSource_injective {k : ℝ} : Function.Injective (availableSource k) := by
  intro p q he
  have hf : p.1.1.1.1 = q.1.1.1.1 := congrArg (fun q : DiskFamily × UpperHalfPlane => q.1) he
  have hz : p.1.1.2 = q.1.1.2 := congrArg (fun q : DiskFamily × UpperHalfPlane => q.2) he
  have hp := (availableRankPartner_spec k p).1.1
  have hq := (availableRankPartner_spec k q).1.1
  have hξ : p.1.1.1.2 = q.1.1.1.2 := by
    rw [← hp,← hq,hf,hz]
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Prod.ext hf hξ) hz

lemma measurable_availableSource (k : ℝ) : Measurable (availableSource k) := by
  exact (measurable_fst.comp (measurable_fst.comp (measurable_subtype_coe.comp measurable_subtype_coe))).prodMk
    (measurable_snd.comp (measurable_subtype_coe.comp measurable_subtype_coe))

lemma measurableEmbedding_availableSource {k : ℝ} (hk : 0 < k) :
    MeasurableEmbedding (availableSource k) := by
  let : StandardBorelSpace (AvailableRankPair k) := (measurableSet_rankPairingDomain hk).standardBorel
  exact (measurable_availableSource k).measurableEmbedding availableSource_injective

def sourcePairingDomain (k : ℝ) : Set (DiskFamily × UpperHalfPlane) := range (availableSource k)

lemma measurableSet_sourcePairingDomain {k : ℝ} (hk : 0 < k) :
    MeasurableSet (sourcePairingDomain k) := (measurableEmbedding_availableSource hk).measurableSet_range

def sourcePair (k : ℝ) (q : sourcePairingDomain k) : AvailableRankPair k := q.2.choose

lemma sourcePair_apply (k : ℝ) (q : sourcePairingDomain k) :
    availableSource k (sourcePair k q) = q.1 := q.2.choose_spec

lemma measurable_sourcePair {k : ℝ} (hk : 0 < k) : Measurable (sourcePair k) := by
  have he : sourcePair k = (measurableEmbedding_availableSource hk).equivRange.symm := by
    funext q
    apply availableSource_injective
    have ha := (measurableEmbedding_availableSource hk).equivRange.apply_symm_apply q
    have hb := congrArg Subtype.val ha
    rw [MeasurableEmbedding.equivRange_apply] at hb
    exact (sourcePair_apply k q).trans hb.symm
  rw [he]
  exact (measurableEmbedding_availableSource hk).equivRange.symm.measurable

def sourcePartnerOn (k : ℝ) (q : sourcePairingDomain k) : UpperHalfPlane :=
  availableRankPartner k (sourcePair k q)

lemma measurable_sourcePartnerOn {k : ℝ} (hk : 0 < k) : Measurable (sourcePartnerOn k) :=
  (measurable_availableRankPartner hk).comp (measurable_sourcePair hk)

def sourcePartner (k : ℝ) (q : DiskFamily × UpperHalfPlane) : UpperHalfPlane :=
  by
    classical
    exact if h : q ∈ sourcePairingDomain k then sourcePartnerOn k ⟨q,h⟩ else UpperHalfPlane.I

lemma sourcePartner_of_mem (k : ℝ) {q : DiskFamily × UpperHalfPlane}
    (hq : q ∈ sourcePairingDomain k) : sourcePartner k q = sourcePartnerOn k ⟨q,hq⟩ := by
  classical
  simp only [sourcePartner,dite_eq_left hq]

lemma measurable_sourcePartner {k : ℝ} (hk : 0 < k) : Measurable (sourcePartner k) := by
  classical
  exact (measurable_sourcePartnerOn hk).dite measurable_const (measurableSet_sourcePairingDomain hk)

lemma sourcePairingDomain_iff (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    (f,z) ∈ sourcePairingDomain k ↔
      ∃ hg : GoodPair k (f,criticalMap k (halfPlaneFunction f) z),
        (⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩ : RankParameters k) ∈ rankPairingDomain k := by
  constructor
  · rintro ⟨p,hp⟩
    have hf : p.1.1.1.1 = f := congrArg Prod.fst hp
    have hz : p.1.1.2 = z := congrArg Prod.snd hp
    have hξ : p.1.1.1.2 = criticalMap k (halfPlaneFunction f) z := by
      rw [← (availableRankPartner_spec k p).1.1,hf,hz]
    have hg : GoodPair k (f,criticalMap k (halfPlaneFunction f) z) := by
      rw [← hξ,← hf]
      exact p.1.2
    refine ⟨hg,?_⟩
    have he : (⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩ : RankParameters k) = p.1 := by
      apply Subtype.ext
      exact (Prod.ext (Prod.ext hf hξ) hz).symm
    rw [he]
    exact p.2
  · rintro ⟨hg,hp⟩
    exact ⟨⟨⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩,hp⟩,rfl⟩

lemma sourcePartner_spec (k : ℝ) {f : DiskFamily} {z : UpperHalfPlane}
    (hq : (f,z) ∈ sourcePairingDomain k) :
    GoodPair k (f,criticalMap k (halfPlaneFunction f) z) ∧
    0 < jacobianExpression k (halfPlaneFunction f) z ∧
    jacobianExpression k (halfPlaneFunction f) (sourcePartner k (f,z)) < 0 ∧
    criticalMap k (halfPlaneFunction f) (sourcePartner k (f,z)) =
      criticalMap k (halfPlaneFunction f) z ∧
    criticalHeight k (halfPlaneFunction f) z <
      criticalHeight k (halfPlaneFunction f) (sourcePartner k (f,z)) := by
  let p := sourcePair k ⟨(f,z),hq⟩
  have hp := availableRankPartner_spec k p
  have hsource := sourcePair_apply k ⟨(f,z),hq⟩
  have hf : p.1.1.1.1 = f := congrArg Prod.fst hsource
  have hz : p.1.1.2 = z := congrArg Prod.snd hsource
  have hξ : p.1.1.1.2 = criticalMap k (halfPlaneFunction f) z := by
    rw [← hp.1.1,hf,hz]
  have hr : sourcePartner k (f,z) = availableRankPartner k p := sourcePartner_of_mem k hq
  have hg := p.1.2
  change GoodPair k (p.1.1.1.1,p.1.1.1.2) at hg
  simp only [RankPairRelation,signedCriticalFiber,mem_ofPred_eq] at hp
  rw [hf,hz,hξ] at hp
  rw [hf,hξ] at hg
  rw [hr]
  exact ⟨hg,hp.1.2,hp.2.1.2,hp.2.1.1,hp.2.2.2⟩

lemma sourcePartner_injOn_fiber {k : ℝ} (hk : 0 < k) (f : DiskFamily)
    {z w : UpperHalfPlane} (hz : (f,z) ∈ sourcePairingDomain k)
    (hw : (f,w) ∈ sourcePairingDomain k)
    (hG : criticalMap k (halfPlaneFunction f) z = criticalMap k (halfPlaneFunction f) w)
    (he : sourcePartner k (f,z) = sourcePartner k (f,w)) : z = w := by
  let p := sourcePair k ⟨(f,z),hz⟩
  let q := sourcePair k ⟨(f,w),hw⟩
  have hp := sourcePair_apply k ⟨(f,z),hz⟩
  have hq := sourcePair_apply k ⟨(f,w),hw⟩
  have hpf : p.1.1.1.1 = f := congrArg Prod.fst hp
  have hqf : q.1.1.1.1 = f := congrArg Prod.fst hq
  have hpz : p.1.1.2 = z := congrArg Prod.snd hp
  have hqw : q.1.1.2 = w := congrArg Prod.snd hq
  have hξ : p.1.1.1.2 = q.1.1.1.2 := by
    rw [← (availableRankPartner_spec k p).1.1,← (availableRankPartner_spec k q).1.1,
      hpf,hqf,hpz,hqw,hG]
  have hf := Prod.ext (hpf.trans hqf.symm) hξ
  have he' : availableRankPartner k p = availableRankPartner k q := by
    simpa only [sourcePartner_of_mem k hz,sourcePartner_of_mem k hw,sourcePartnerOn] using he
  have h := availableRankPartner_injOn_fiber hk hf he'
  exact hpz.symm.trans (h.trans hqw)

end
end StrictInverseFirstPower

end

end OAI
