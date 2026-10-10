import OAI.Probability.DilutedSpin.FiniteTowerPi
import OAI.Probability.DilutedSpin.PhysicalShapeError
import OAI.Probability.DilutedSpin.RealEncoding

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p : ℕ}
lemma reservoirShapeDeviation_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    reservoirShapeDeviation M C H N L u S ≤ (2:ℝ)^S.leaves*2 := by
  unfold reservoirShapeDeviation
  exact shapeDeviation_bound _ _ _ _ _ (fun z y i => readVector_bound _ _ _)
lemma physicalShapeDeviation_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    physicalShapeDeviation M C H N L u S ≤ (2:ℝ)^S.leaves*2 := by
  unfold physicalShapeDeviation
  exact shapeDeviation_bound _ _ _ _ _ (fun z y i => readVector_bound _ _ _)

lemma reservoirShapeError_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
      atTop (𝓝 0) := by
  let f := fun L n => qExpect (grid (L+1) 0 (L+1))
    (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  let g := fun L n => qExpect (grid (L+1) 0 (L+1))
    (physicalShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  have hf (L n : ℕ) : 0≤f L n := qExpect_nonneg _
    (grid_strictMono (by omega)).monotone grid_nonneg _
    (reservoirShapeDeviation_nonneg _ _ _ _ _ _) _ _
  have hfb (L : ℕ) : IsBoundedUnder (·≤·) atTop (f L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact reservoirShapeDeviation_bound _ _ _ _ _ _ _
  have hgb (L : ℕ) : IsBoundedUnder (·≤·) atTop (g L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact physicalShapeDeviation_bound _ _ _ _ _ _ _
  apply squeeze_zero (fun L => le_limsup_of_frequently_le ((Eventually.of_forall (hf L)).frequently) (hfb L)) _
    (physicalShapeError_tendsto M C H Ns us hcontrol k)
  intro L
  exact limsup_le_of_vanishing_error (f L) (g L) (fun n => -(g L n-f L n)) (hf L) (hgb L)
    (by simpa only [neg_zero] using
      (reservoirShape_qExpect_difference_tendsto M hα C H L (Ns L) (hNs L) (us L) k).neg)
    (fun n => by linarith)
end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω Ξ : Type}

lemma sampleMap_fst {n : ℕ} (S : PrescribedTree n) (x : Sample (Ω×Ξ) S) :
    sampleMap Prod.fst S x=sampleFst S x := by
  induction S with
  | leaf => rfl
  | node k C ih => funext j; exact Prod.ext rfl (ih j (x j).2)

lemma sampleMap_snd {n : ℕ} (S : PrescribedTree n) (x : Sample (Ω×Ξ) S) :
    sampleMap Prod.snd S x=sampleSnd S x := by
  induction S with
  | leaf => rfl
  | node k C ih => funext j; exact Prod.ext rfl (ih j (x j).2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
