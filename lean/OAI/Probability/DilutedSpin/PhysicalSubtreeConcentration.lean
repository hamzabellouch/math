import OAI.Probability.DilutedSpin.SubsetTree
import OAI.Probability.DilutedSpin.TopologyDecay

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance physicalSubtreeConcentrationDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
variable {p L : ℕ}

noncomputable def physicalTreeVariance (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) : ℝ :=
  overlapVariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

lemma physicalTreeVariance_realize (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (q : S.Vertex → Fin (L+1)) :
    physicalTreeVariance M C H N L u (S.realize (L+1) 0 (fun v => q v))=
      physicalOverlapVariance M C H N L u S q := rfl

lemma physicalTreeVariance_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    0≤physicalTreeVariance M C H N L u T := by
  unfold physicalTreeVariance
  exact root_overlapVariance_nonneg _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

lemma physicalTreeVariance_le_one (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    physicalTreeVariance M C H N L u T≤1 := by
  unfold physicalTreeVariance
  exact root_overlapVariance_le_one _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

/-- The actual physical subsequence, not a newly assumed concentration law. -/
theorem physicalSubtree_limsup_tendsto (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (K k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (subtreePotential K (physicalTreeVariance M C H (Ns L n+1) L (us L n)))
      k (single (L+1))) atTop) atTop (𝓝 0) := by
  apply qSubtree_limsup_tendsto K k
    (fun L n => physicalTreeVariance M C H (Ns L n+1) L (us L n))
    (fun L n => physicalTreeVariance_nonneg _ _ _ _ _ _)
    (fun L n => physicalTreeVariance_le_one _ _ _ _ _ _)
  intro S η hη
  exact physicalOverlapLimsup_tendsto M C H Ns us hcontrol S hη

end DilutedSpinGlass.UniversalDictionary

end

end OAI
