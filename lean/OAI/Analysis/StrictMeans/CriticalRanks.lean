import OAI.Analysis.StrictMeans.BorelRanks

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def signedCriticalFiber (k : ℝ) (f : DiskFamily) (ξ : ℂ) (positive : Bool) : Set UpperHalfPlane :=
  {z | criticalMap k (halfPlaneFunction f) z = ξ ∧
    if positive then 0 < jacobianExpression k (halfPlaneFunction f) z
    else jacobianExpression k (halfPlaneFunction f) z < 0}

def criticalRank (k : ℝ) (f : DiskFamily) (ξ : ℂ) (positive : Bool) (z : UpperHalfPlane) : ℕ :=
  descendingRank (fun w : UpperHalfPlane => criticalHeight k (halfPlaneFunction f) w)
    (signedCriticalFiber k f ξ positive) z

lemma signedCriticalFiber_strictCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (positive : Bool) (z : UpperHalfPlane) :
    {w | w ∈ signedCriticalFiber k f ξ positive ∧
      criticalHeight k (halfPlaneFunction f) z < criticalHeight k (halfPlaneFunction f) w}.Finite := by
  apply (goodPair_criticalCut_finite hk hg
    (criticalHeight_pos hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos))).subset
  intro w hw
  exact ⟨hw.1.1,hw.2.le⟩

lemma goodPair_criticalHeight_injOn {k : ℝ} {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) :
    InjOn (fun w : UpperHalfPlane => criticalHeight k (halfPlaneFunction f) w)
      {w : UpperHalfPlane | criticalMap k (halfPlaneFunction f) w = ξ} := by
  intro z hz w hw he
  exact hg.2.2 z w hz hw he

lemma criticalRank_injOn {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (positive : Bool) :
    InjOn (criticalRank k f ξ positive) (signedCriticalFiber k f ξ positive) := by
  apply descendingRank_injOn
    ((goodPair_criticalHeight_injOn hg).mono (fun _ hz => hz.1))
  intro z _
  exact signedCriticalFiber_strictCut_finite hk hg positive z

abbrev RankParameters (k : ℝ) := {p : (DiskFamily × ℂ) × UpperHalfPlane | GoodPair k p.1}

def rankClosedRelation (k : ℝ) : Set (RankParameters k × UpperHalfPlane) :=
  {q | criticalMap k (halfPlaneFunction q.1.1.1.1) q.2 = q.1.1.1.2}

def rankOpenRelation (k : ℝ) (positive : Bool) : Set (RankParameters k × UpperHalfPlane) :=
  {q | (if positive then 0 < jacobianExpression k (halfPlaneFunction q.1.1.1.1) q.2
    else jacobianExpression k (halfPlaneFunction q.1.1.1.1) q.2 < 0) ∧
    criticalHeight k (halfPlaneFunction q.1.1.1.1) q.1.1.2 <
      criticalHeight k (halfPlaneFunction q.1.1.1.1) q.2}

lemma continuous_rank_f (k : ℝ) :
    Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.1) :=
  continuous_fst.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))

lemma continuous_rank_z (k : ℝ) :
    Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.2) :=
  continuous_snd.comp (continuous_subtype_val.comp continuous_fst)

lemma isClosed_rankClosedRelation (k : ℝ) : IsClosed (rankClosedRelation k) := by
  have hG := (continuous_criticalMap k).comp ((continuous_rank_f k).prodMk continuous_snd)
  have hξ : Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  exact isClosed_eq hG hξ

lemma isOpen_rankOpenRelation (k : ℝ) (positive : Bool) :
    IsOpen (rankOpenRelation k positive) := by
  have hJ := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hVz := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hVw := (continuous_criticalHeight k).comp ((continuous_rank_f k).prodMk continuous_snd)
  apply IsOpen.inter _ (isOpen_lt hVz hVw)
  cases positive
  · exact isOpen_lt hJ continuous_const
  · exact isOpen_lt continuous_const hJ

lemma rankRelation_finite {k : ℝ} (hk : 0 < k) (positive : Bool) (p : RankParameters k) :
    {w | (p,w) ∈ rankClosedRelation k ∩ rankOpenRelation k positive}.Finite := by
  convert signedCriticalFiber_strictCut_finite hk p.2 positive p.1.2 using 1
  ext w
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

lemma measurable_criticalRank {k : ℝ} (hk : 0 < k) (positive : Bool) :
    Measurable (fun p : RankParameters k =>
      criticalRank k p.1.1.1 p.1.1.2 positive p.1.2) := by
  have hr := measurable_ncard_locally_closed_fiber
    (isClosed_rankClosedRelation k) (isOpen_rankOpenRelation k positive)
    (rankRelation_finite hk positive)
  convert hr using 1
  funext p
  unfold criticalRank descendingRank
  congr 1
  ext w
  change ((_ ∧ _) ∧ _) ↔ (_ ∧ _ ∧ _)
  tauto

end
end StrictInverseFirstPower

end

end OAI
