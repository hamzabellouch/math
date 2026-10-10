import OAI.Analysis.StrictMeans.TransportPairing

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma goodPair_rank_partner {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {z : UpperHalfPlane}
    (hz : z ∈ signedCriticalFiber k f ξ true) :
    ∃ w, RankPairRelation k ⟨((f,ξ),z),hg⟩ w := by
  let v := fun w : UpperHalfPlane => criticalHeight k (halfPlaneFunction f) w
  let A := signedCriticalFiber k f ξ true
  let B := signedCriticalFiber k f ξ false
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro w ha hb
    exact (not_lt_of_gt ha.2) hb.2
  have hv : InjOn v (A ∪ B) := (goodPair_criticalHeight_injOn hg).mono (by
    intro w hw
    rcases hw with hw | hw <;> exact hw.1)
  have hA : {w | w ∈ A ∧ v z ≤ v w} = saddleCut k f ξ (v z) := by
    ext w
    change ((_ = _ ∧ 0 < _) ∧ _ ≤ _) ↔ ((_ = _ ∧ _ ≤ _) ∧ 0 < _)
    tauto
  have hB : {w | w ∈ B ∧ v z ≤ v w} = maximaCut k f ξ (v z) := by
    ext w
    change ((_ = _ ∧ _ < 0) ∧ _ ≤ _) ↔ ((_ = _ ∧ _ ≤ _) ∧ _ < 0)
    tauto
  have hp : 0 < v z := criticalHeight_pos hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  have hfinA : {w | w ∈ A ∧ v z ≤ v w}.Finite := by
    rw [hA]
    exact saddleCut_finite hk hg hp
  have hfinB : {w | w ∈ B ∧ v z ≤ v w}.Finite := by
    rw [hB]
    exact maximaCut_finite hk hg hp
  have hcount : {w | w ∈ A ∧ v z ≤ v w}.ncard ≤ {w | w ∈ B ∧ v z ≤ v w}.ncard := by
    rw [hA,hB]
    exact goodPair_superlevel_count hk hg hp
  obtain ⟨w,hw,hh,hr⟩ := higher_partner_of_cut_domination hdisj hv hz hfinA hfinB hcount
  exact ⟨w,hz,hw,hr,hh⟩

lemma sourcePairingDomain_eq_good_positive {k : ℝ} (hk : 0 < k)
    (f : DiskFamily) (z : UpperHalfPlane) :
    (f,z) ∈ sourcePairingDomain k ↔
      GoodPair k (f,criticalMap k (halfPlaneFunction f) z) ∧
        0 < jacobianExpression k (halfPlaneFunction f) z := by
  constructor
  · intro hz
    exact ⟨(sourcePartner_spec k hz).1,(sourcePartner_spec k hz).2.1⟩
  · rintro ⟨hg,hJ⟩
    apply (sourcePairingDomain_iff k f z).mpr
    exact ⟨hg,goodPair_rank_partner hk hg ⟨rfl,hJ⟩⟩

end
end StrictInverseFirstPower

end

end OAI
