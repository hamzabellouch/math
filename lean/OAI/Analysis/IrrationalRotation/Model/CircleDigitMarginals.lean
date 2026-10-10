import OAI.Analysis.IrrationalRotation.Model.CircleCoupling
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData

def hybridDigits (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) (ω : Sample) :
    MixedRadix.Digits (MixedRadix.radices p.q) :=
  fun i => observedDigit p hr (ε i) i (ω i)

def hybridPoint (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) (ω : Sample) : Circle :=
  MixedRadix.circleValue (hybridDigits p hr ε ω)

def rawDensity (p : CircleParameterData) (j : ℕ) (side : Bool) (i : ℕ) : ℝ → ℝ :=
  if i = 0 then fun _ => 1 else
    marginalDensity side (kappa (p.blockIndex i)) (p.m (p.blockIndex i))
      (p.a (p.blockIndex i)) (p.b (p.blockIndex i)) (tag j (p.blockIndex i))

def digitDensity (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (j : ℕ) (side : Bool) (i : ℕ) : Fin (MixedRadix.radices p.q i) → ℝ := by
  letI : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  exact UniformQuantization.binAverage (MixedRadix.radices p.q i) (rawDensity p j side i)

def digitReference (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (i : ℕ) : Measure (Fin (MixedRadix.radices p.q i)) := by
  letI : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  exact (PMF.uniformOfFintype (Fin (MixedRadix.radices p.q i))).toMeasure

def marginalBound : ℝ := Real.exp (25 * ((∑' s : ℕ, kappa s ^ 2) + 1))

def DigitMarginalLaws (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : Prop :=
  0 < marginalBound ∧ ∀ (j : ℕ) (ε : ℕ → Bool),
    ∃ H : Circle → ℝ, MemLp H 2 volume ∧ (0 ≤ᵐ[volume] H) ∧
      (∫ x, H x) = 1 ∧ eLpNorm H 2 volume ≤ ENNReal.ofReal marginalBound ∧
      (law p j).map (hybridPoint p hr ε) =
        volume.withDensity (fun x => ENNReal.ofReal (H x))

end Invariant233.CircleCoupling

end

end OAI
