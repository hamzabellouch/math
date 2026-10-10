import OAI.Analysis.StrictMeans.PairingCoverage

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma sourcePartner_eq_available (k : ℝ) {f : DiskFamily} {ξ : ℂ} {z : UpperHalfPlane}
    (hg : GoodPair k (f,ξ))
    (hp : (⟨((f,ξ),z),hg⟩ : RankParameters k) ∈ rankPairingDomain k) :
    sourcePartner k (f,z) = availableRankPartner k ⟨⟨((f,ξ),z),hg⟩,hp⟩ := by
  let p : AvailableRankPair k := ⟨⟨((f,ξ),z),hg⟩,hp⟩
  have hq : (f,z) ∈ sourcePairingDomain k := ⟨p,rfl⟩
  rw [sourcePartner_of_mem k hq]
  unfold sourcePartnerOn
  congr 1
  exact availableSource_injective (sourcePair_apply k ⟨(f,z),hq⟩)

lemma sourcePairingDomain_rebase_iff (k : ℝ) (f : DiskFamily) (t w : UpperHalfPlane) :
    (rebase f t,w) ∈ sourcePairingDomain k ↔ (f,affineProduct t w) ∈ sourcePairingDomain k := by
  rw [sourcePairingDomain_iff,sourcePairingDomain_iff,criticalMap_rebase]
  constructor
  · rintro ⟨hg',hp⟩
    have hg := (goodPair_rebase_iff k f _ t).mp hg'
    exact ⟨hg,(rankPairingDomain_rebase_iff hg t w).mp hp⟩
  · rintro ⟨hg,hp⟩
    exact ⟨goodPair_rebase hg t,(rankPairingDomain_rebase_iff hg t w).mpr hp⟩

lemma sourcePartner_rebase {k : ℝ} (hk : 0 < k) (f : DiskFamily) (t w : UpperHalfPlane)
    (hp : (rebase f t,w) ∈ sourcePairingDomain k) :
    sourcePartner k (f,affineProduct t w) = affineProduct t (sourcePartner k (rebase f t,w)) := by
  obtain ⟨hg',hp'⟩ := (sourcePairingDomain_iff k _ _).mp hp
  rw [criticalMap_rebase] at hg'
  have hg := (goodPair_rebase_iff k f _ t).mp hg'
  have hpr : (⟨((rebase f t,targetRebase f t (criticalMap k (halfPlaneFunction f) (affineProduct t w))),w),
      goodPair_rebase hg t⟩ : RankParameters k) ∈ rankPairingDomain k := by
    simpa only [criticalMap_rebase] using hp'
  rw [sourcePartner_eq_available k (goodPair_rebase hg t) hpr,
    sourcePartner_eq_available k hg ((rankPairingDomain_rebase_iff hg t w).mp hpr)]
  exact availableRankPartner_rebase hk hg t w hpr

def partnerRatio (k : ℝ) (q : DiskFamily × UpperHalfPlane) : ℝ :=
  by
    classical
    exact if q ∈ sourcePairingDomain k then
    (criticalHeight k (halfPlaneFunction q.1) (sourcePartner k q) /
      criticalHeight k (halfPlaneFunction q.1) q.2)^3 else 0

lemma measurable_partnerRatio {k : ℝ} (hk : 0 < k) : Measurable (partnerRatio k) := by
  have hnum : Measurable (fun q : DiskFamily × UpperHalfPlane =>
      criticalHeight k (halfPlaneFunction q.1) (sourcePartner k q)) :=
    (continuous_criticalHeight k).measurable.comp (measurable_fst.prodMk (measurable_sourcePartner hk))
  exact ((hnum.div (continuous_criticalHeight k).measurable).pow_const 3).piecewise
    (measurableSet_sourcePairingDomain hk) measurable_const

lemma partnerRatio_gt_one {k : ℝ} (hk : 0 < k) {q : DiskFamily × UpperHalfPlane}
    (hq : q ∈ sourcePairingDomain k) : 1 < partnerRatio k q := by
  have hs := sourcePartner_spec k hq
  have hp : 0 < criticalHeight k (halfPlaneFunction q.1) q.2 := criticalHeight_pos hk q.2.im_pos (halfPlaneFunction_deriv_ne_zero q.1 q.2.im_pos)
  rw [partnerRatio,ite_eq_left hq]
  have hd : 1 < criticalHeight k (halfPlaneFunction q.1) (sourcePartner k q) /
      criticalHeight k (halfPlaneFunction q.1) q.2 := (one_lt_div hp).mpr hs.2.2.2.2
  exact one_lt_pow₀ hd (by norm_num)

lemma partnerRatio_nonneg {k : ℝ} (hk : 0 < k) (q : DiskFamily × UpperHalfPlane) : 0 ≤ partnerRatio k q := by
  classical
  by_cases hq : q ∈ sourcePairingDomain k
  · exact (partnerRatio_gt_one hk hq).le.trans' (by norm_num)
  · simp only [partnerRatio,ite_eq_right hq,le_refl]

lemma partnerRatio_rebase {k : ℝ} (hk : 0 < k) (f : DiskFamily) (t w : UpperHalfPlane) :
    partnerRatio k (rebase f t,w) = partnerRatio k (f,affineProduct t w) := by
  classical
  by_cases hp : (rebase f t,w) ∈ sourcePairingDomain k
  · have hp' := (sourcePairingDomain_rebase_iff k f t w).mp hp
    rw [partnerRatio,ite_eq_left hp,partnerRatio,ite_eq_left hp']
    simp only
    rw [criticalHeight_rebase,criticalHeight_rebase,sourcePartner_rebase hk f t w hp]
    congr 1
    exact mul_div_mul_left _ _ (heightRebaseScale_pos k f t).ne'
  · have hp' : (f,affineProduct t w) ∉ sourcePairingDomain k :=
      fun h => hp ((sourcePairingDomain_rebase_iff k f t w).mpr h)
    simp only [partnerRatio,ite_eq_right hp,ite_eq_right hp']

def truncatedPairingDomain (k N : ℝ) : Set (DiskFamily × UpperHalfPlane) :=
  {q | q ∈ sourcePairingDomain k ∧ 1/N ≤ (sourcePartner k q).im / q.2.im ∧
    (sourcePartner k q).im / q.2.im ≤ N ∧
    |(sourcePartner k q).re - q.2.re| ≤ N*q.2.im}

lemma measurableSet_truncatedPairingDomain {k : ℝ} (hk : 0 < k) (N : ℝ) :
    MeasurableSet (truncatedPairingDomain k N) := by
  have hR := measurable_sourcePartner hk
  have hi := (UpperHalfPlane.continuous_im.measurable.comp hR).div
    (UpperHalfPlane.continuous_im.measurable.comp measurable_snd)
  have hr := ((UpperHalfPlane.continuous_re.measurable.comp hR).sub
    (UpperHalfPlane.continuous_re.measurable.comp measurable_snd)).abs
  exact (measurableSet_sourcePairingDomain hk).inter ((measurableSet_le measurable_const hi).inter
    ((measurableSet_le hi measurable_const).inter (measurableSet_le hr
      (measurable_const.mul (UpperHalfPlane.continuous_im.measurable.comp measurable_snd)))))

@[simp] lemma affineProduct_re (t w : UpperHalfPlane) :
    (affineProduct t w).re = t.re+t.im*w.re := by simp [affineProduct,affineAt]

lemma truncatedPairingDomain_rebase {k : ℝ} (hk : 0 < k) (N : ℝ)
    (f : DiskFamily) (t w : UpperHalfPlane) :
    (rebase f t,w) ∈ truncatedPairingDomain k N ↔
      (f,affineProduct t w) ∈ truncatedPairingDomain k N := by
  by_cases hp : (rebase f t,w) ∈ sourcePairingDomain k
  · have hp' := (sourcePairingDomain_rebase_iff k f t w).mp hp
    simp only [truncatedPairingDomain,mem_ofPred_eq,hp,hp',true_and]
    rw [sourcePartner_rebase hk f t w hp]
    simp only [affineProduct_im,affineProduct_re]
    rw [mul_div_mul_left _ _ t.im_ne_zero]
    have he : t.re+t.im*(sourcePartner k (rebase f t,w)).re-(t.re+t.im*w.re) =
        t.im*((sourcePartner k (rebase f t,w)).re-w.re) := by ring
    rw [he,abs_mul,abs_of_pos t.im_pos]
    have heN : N*(t.im*w.im) = t.im*(N*w.im) := by ring
    rw [heN,mul_le_mul_iff_right₀ t.im_pos]
  · have hp' : (f,affineProduct t w) ∉ sourcePairingDomain k :=
      fun h => hp ((sourcePairingDomain_rebase_iff k f t w).mpr h)
    simp only [truncatedPairingDomain,mem_ofPred_eq,hp,hp',false_and]

end
end StrictInverseFirstPower

end

end OAI
