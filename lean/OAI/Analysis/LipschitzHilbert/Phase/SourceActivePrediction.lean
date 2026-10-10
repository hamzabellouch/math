import OAI.Analysis.LipschitzHilbert.Trees.SourcePathValues
import OAI.Analysis.LipschitzHilbert.Trees.SourceInsignificantShrink

namespace OAI

/-! Removing the zero snapshot children preserves the exact prediction.
The remaining children have significant representatives, with precisely the
one allowed unshrunk path exception. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

abbrev SourceActive {ι E : Type} [Zero E] (A : ι → E) := {i : ι // A i ≠ 0}

theorem sum_source_active {ι E M : Type} [Fintype ι] [Zero E] [DecidableEq E] [AddCommMonoid M]
    (A : ι → E) (F : ι → M) (hF : ∀ i, A i = 0 → F i = 0) :
    (∑ i : SourceActive A, F i) = ∑ i, F i := by
  have hz : (∑ i : {i : ι // ¬A i ≠ 0}, F i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hF i (not_not.mp i.property)
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => A i ≠ 0) F
  simpa only [hz,add_zero] using hs

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_prediction_active {p μ n : ℝ} (hp : 0 < p)
    (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) :
    sourcePredictionValue p μ n (fun i : SourceActive A => c i)
      (fun i => A i) (fun i => lam i) = sourcePredictionValue p μ n c A lam := by
  unfold sourcePredictionValue
  dsimp only
  apply congrArg₂ (energyRatio p)
  · apply congrArg (fun t : ℝ => 1+t)
    exact sum_source_active A (fun i => (c i/n)*‖(c i)^(μ-1) • A i‖^p)
      (fun i hi => by simp only [hi,smul_zero,norm_zero,Real.zero_rpow hp.ne',mul_zero])
  · exact sum_source_active A
      (fun i => (((c i/n)^(1-μ):ℝ):ℂ) • (lam i • ((c i)^(μ-1) • A i)))
      (fun i hi => by simp only [hi,smul_zero])

theorem source_snapshot_active {p μ n : ℝ} (hp : 0 < p)
    (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (f : ι → κ → ℝ) (b : ℝ) :
    sourceSnapshotPrediction p μ n (fun i : SourceActive A => c i)
      (fun i => A i) (fun i => lam i) (fun i => f i) b =
      sourceSnapshotPrediction p μ n c A lam f b := by
  unfold sourceSnapshotPrediction
  dsimp only
  apply congrArg₂ (energyRatio p)
  · apply congrArg (fun t : ℝ => 1+t)
    exact sum_source_active A (fun i => (c i/n)*‖(c i)^(μ-1) • A i‖^p)
      (fun i hi => by simp only [hi,smul_zero,norm_zero,Real.zero_rpow hp.ne',mul_zero])
  · have hzero (i : ι) : diagonalModulation (f i) (0 : EuclideanSpace ℂ κ) b = 0 :=
      (diagonalModulationIsometry (f i) b).map_zero
    exact sum_source_active A
      (fun i => (((c i/n)^(1-μ):ℝ):ℂ) •
        (lam i • diagonalModulation (f i) ((c i)^(μ-1) • A i) b))
      (fun i hi => by simp only [hi,smul_zero,hzero])

/-- Nonzero shrunken children must be significant, except for the one
path child that the source deliberately leaves unshrunk. -/
theorem eventually_source_active_significant (Q : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι κ : Type) [Fintype κ]
      (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (significant : ι → Prop) (path : ι),
      (∀ i, 0 ≤ c i) →
      (∀ i, ¬significant i → ‖A i‖ ≤ (L^Q*Real.exp (-L*Real.log L))*c i) →
      let shrink := fun i => if i = path then A i else
        radialShrink (2*SourceParameters.step L^(-(1/8:ℝ))*c i) (A i)
      ∀ i : SourceActive shrink, significant i ∨ (i:ι) = path := by
  filter_upwards [eventually_source_insignificant_shrink Q] with L hL
  intro ι κ _ c A significant path hc hsmall
  dsimp only
  intro i
  by_cases hi : (i:ι) = path
  · exact Or.inr hi
  · apply Or.inl
    by_contra hsig
    have hz := hL (EuclideanSpace ℂ κ) (c i) (A i) (hc i) (hsmall i hsig)
    exact i.property (by simpa only [ite_eq_right hi] using hz)

end LipschitzHilbert

end

end OAI
