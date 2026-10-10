import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelEllipsoid
import OAI.Probability.MemoryPrecision.StreamArithmetic
import OAI.Probability.MemoryPrecision.StreamZero

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision Policy

def SourceStreamStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 0 < d₀ ∧
  ∀ d M T : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ L : Ω → MemoryPrecision.Kernel.Policy d M T,
    MemoryPrecision.Kernel.Policy.Admissible L ρ (MemoryPrecision.Kernel.UniformSphere d) →
    MemoryPrecision.Kernel.Policy.Success L ρ (MemoryPrecision.Kernel.UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      ((2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(MemoryPrecision.Kernel.BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2)))

lemma source_stream_explicit :
  ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ L : Ω → Policy d M T, Admissible L ρ (UniformSphere d) →
    Success L ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      ((2*ε*Real.exp (StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2))) := by
  intro d M T hd ε hε hε1 Ω _ ρ hρ L hL
  have : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  refine le_min (Policy.success_le_one L ρ (UniformSphere d) ε) ?_
  apply (Policy.success_le_chord L ρ (UniformSphere d) ε).trans
  by_cases hT : T = 0
  · subst T
    simp only [BlockCount, Nat.ceil_zero, zero_div, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact (Policy.chord_zero_bound L ρ hL (by omega) hε).trans
      (ENNReal.ofReal_le_ofReal (zero_cap_precise hd hε hε1))
  · apply (chord_half_sphere_bound L ρ hL (by omega) hε hε1).trans
    apply ENNReal.ofReal_le_ofReal
    let a := ((d:ℝ)-1)/2
    let X := StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)
    have ha : 0 ≤ a := by
      dsimp [a]
      have : (32:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have he : Real.exp (a*X) = (Real.exp X)^a := by rw [← Real.exp_mul, mul_comm]
    have h2 : ε^a ≤ (2*ε)^a := Real.rpow_le_rpow hε.le (by linarith) ha
    calc
      _ = ε^a * ((4:ℝ)^d * (SuccessConstant^d *
        (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^BlockCount T (d/8)) := by dsimp [a, BlockCount, MemoryPrecision.BlockCount]; ring
      _ ≤ ε^a * Real.exp (a*X) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [a, X, BlockCount, MemoryPrecision.BlockCount, mul_assoc] using stream_full_factor hd (by omega : 0 < T)
      _ ≤ (2*ε)^a * Real.exp (a*X) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (2*ε*Real.exp X)^a := by
        rw [he]
        exact (Real.mul_rpow (by positivity : (0:ℝ) ≤ 2*ε) (Real.exp_pos X).le).symm
theorem source_stream_success : SourceStreamStatement :=
  ⟨StreamConstant, streamConstant_pos, 32, by norm_num, source_stream_explicit⟩
end MemoryPrecision.Kernel


end

end OAI
