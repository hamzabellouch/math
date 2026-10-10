import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Passing from derivatives along each initial frame to a derivative in
the space of continuous fields. The fundamental theorem of calculus avoids
any separate uniform remainder assumption. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance : NormedAddCommGroup C(Ω, E) := ContinuousMap.instNormedAddCommGroup
local instance : NormedSpace ℝ C(Ω, E) := ContinuousMap.normedSpace

/-- A continuous family of pointwise derivatives is the derivative in the
supremum norm on continuous fields. -/
theorem continuousField_hasDerivAt {F G : ℝ → C(Ω, E)}
    (hG : Continuous G)
    (hpoint : ∀ t x, HasDerivAt (fun s => F s x) (G t x) t) (t : ℝ) :
    HasDerivAt F (G t) t := by
  let K : ℝ → C(Ω, E) := fun s => F 0 + ∫ u in (0 : ℝ)..s, G u
  have hK (s : ℝ) : HasDerivAt K (G s) s :=
    (hG.integral_hasStrictDerivAt 0 s).hasDerivAt.const_add (F 0)
  have hFK : F = K := by
    funext s
    apply ContinuousMap.ext
    intro x
    have hd (u : ℝ) : HasDerivAt (fun u => F u x - K u x) 0 u := by
      let ev : C(Ω, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ x
      have he : HasDerivAt (fun u => K u x) (G u x) u :=
        ev.hasFDerivAt.comp_hasDerivAt u (hK u)
      convert (hpoint u x).sub he using 1
      simp
    have hc := is_const_of_deriv_eq_zero
      (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) s 0
    have hz : F 0 x - K 0 x = 0 := by simp [K]
    exact sub_eq_zero.mp (hc.trans hz)
  rw [hFK]
  exact hK t

/-- Joint continuity in time and the compact parameter gives exactly the
continuity required by `continuousField_hasDerivAt`. -/
theorem continuousField_hasDerivAt_of_joint {F G : ℝ → C(Ω, E)}
    (hG : Continuous (fun p : ℝ × Ω => G p.1 p.2))
    (hpoint : ∀ t x, HasDerivAt (fun s => F s x) (G t x) t) (t : ℝ) :
    HasDerivAt F (G t) t :=
  continuousField_hasDerivAt
    (ContinuousMap.continuous_of_continuous_uncurry G hG) hpoint t

end

end PositiveEinsteinFour.Averages

end OAI
