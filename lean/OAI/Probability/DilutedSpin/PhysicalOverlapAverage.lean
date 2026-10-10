import OAI.Probability.DilutedSpin.PhysicalOverlapConcentration
import OAI.Probability.DilutedSpin.RootOverlapBounds

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance physicalOverlapAverageDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p L : ℕ}

lemma physicalOverlapVariance_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (q : S.Vertex → Fin (L+1)) :
    0≤physicalOverlapVariance M C H N L u S q := by
  unfold physicalOverlapVariance scheduledOverlapVariance
  exact root_overlapVariance_nonneg _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

lemma physicalOverlapVariance_le_one (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (q : S.Vertex → Fin (L+1)) :
    physicalOverlapVariance M C H N L u S q≤1 := by
  unfold physicalOverlapVariance scheduledOverlapVariance
  exact root_overlapVariance_le_one _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

noncomputable def physicalOverlapAverage (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  DepthAverage.average (regularOverlapDomain S (L+1) η) (physicalOverlapVariance M C H N L u S)

lemma physicalOverlapAverage_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalOverlapAverage M C H N L u S η :=
  DepthAverage.average_nonneg _ _ (physicalOverlapVariance_nonneg M C H N L u S)

lemma physicalOverlapAverage_le_one (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    physicalOverlapAverage M C H N L u S η≤1 :=
  DepthAverage.average_le_const _ _ (by norm_num) (fun q _ => physicalOverlapVariance_le_one M C H N L u S q)

lemma physicalOverlapAverage_le_marker (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) {η : ℝ}
    (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L+1:ℕ)) :
    (η/8)*physicalOverlapAverage M C H N L u S η≤
      Real.sqrt (physicalShapeAverage M C H N L u S (η/8))+
      DepthAverage.average (regularShapeDomain S (L+1) (η/8))
        (fun Q => |physicalMarkerDefect M C H N L u S Q|) := by
  apply regular_overlap_average_bound S hη hη1 hlarge
    (physicalOverlapVariance M C H N L u S) (physicalScheduledEnergy M C H N L u S)
    (fun Q => |physicalMarkerDefect M C H N L u S Q|)
    (physicalOverlapVariance_nonneg M C H N L u S)
    (physicalScheduledEnergy_nonneg M C H N L u S) (fun _ => abs_nonneg _) ?_
  intro Q hQ
  apply physicalOverlapVariance_le_marker
  intro v
  exact admissible_lower S _ hQ.2 v

end DilutedSpinGlass.UniversalDictionary

end

end OAI
