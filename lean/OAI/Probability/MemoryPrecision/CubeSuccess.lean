import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeArithmetic
import OAI.Probability.MemoryPrecision.KernelCube
import OAI.Probability.MemoryPrecision.Precision

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression Policy

lemma source_cube_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 16 ≤ d) (hL : Admissible L ρ (CubePrior (by omega)))
    (hM : M ≤ d^2) {ε : ℝ} (hε : 0 < ε) :
    Success L ρ (CubePrior (by omega)) ε ≤ min 1 (ENNReal.ofReal
      (CubeSuccessConstant^((d/2)*(BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ))) := by
  refine le_min (Policy.success_le_one L ρ (CubePrior (by omega)) ε) ?_
  have hb := (Policy.success_le_chord L ρ (CubePrior (by omega)) ε).trans
    (Policy.source_cube_chord_bound L ρ hd hL hε)
  have he : (T+1:ℝ≥0∞) * ENNReal.ofReal
      ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) * CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) =
      ENNReal.ofReal ((T+1:ℝ) *
        ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) * CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4))) := by
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ T+1)]
    congr 1
    simp [ENNReal.ofReal_add]
  rw [he] at hb
  apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ = ((T+1:ℝ) * ((12:ℝ)^(d/2) * CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4))) *
        ε^((d/2:ℕ)/4:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (cube_whole_factor hd hM T) (by positivity)

lemma cubePrior_dimension {d₀ d : ℕ} (hd₀ : 16 ≤ d₀) (hd : d₀ ≤ d) : 2 ≤ d :=
  Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_trans hd₀ hd)

def CubeSuccessEstimate {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (D : ℝ) (hd : 2 ≤ d) (ε : ℝ) (K : Ω → Policy d M T) (ρ : Measure Ω) : Prop :=
  Policy.Success K ρ (CubePrior hd) ε ≤ min 1 (ENNReal.ofReal
    (D^((d/2)*(MemoryPrecision.Kernel.BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ)))

def PointwisePrecisionEstimate {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (c ε : ℝ) (K : Ω → Policy d M T) (ρ : Measure Ω) : Prop :=
  (∀ signal : MemoryPrecision.Kernel.Sphere d,
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) /
      (@OfNat.ofNat ℝ≥0∞ 3
        (@instOfNatAtLeastTwo ℝ≥0∞ 3 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) ≤
        Policy.FixedSuccess K ρ ε signal) → c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)

abbrev SourceCubeStatement : Prop :=
  ∃ D : ℝ, Real.exp 1 ≤ D ∧ ∃ d₀ : ℕ, ∃ hd₀ : 16 ≤ d₀, ∃ c : ℝ, 0 < c ∧
  ∀ d M T : ℕ, ∀ hd : d₀ ≤ d, M ≤ d^2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ K : Ω → MemoryPrecision.Kernel.Policy d M T, Policy.ModelAdmissible.{u} K ρ →
    CubeSuccessEstimate.{u} D (cubePrior_dimension hd₀ hd) ε K ρ ∧
    PointwisePrecisionEstimate.{u} c ε K ρ

theorem source_cube_success : SourceCubeStatement := by
  refine ⟨CubeSuccessConstant,cubeSuccessConstant_exp,32,by norm_num,
    1/(8+20*StreamConstant*(1+1)),by have := streamConstant_pos; positivity,?_⟩
  intro d M T hd hM ε hε hε1 Ω _ ρ hρ L hL
  have : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  refine ⟨source_cube_bound L ρ (by omega) (hL _ inferInstance) hM hε, ?_⟩
  intro hs
  apply Policy.source_precision L ρ hd (hL _ inferInstance) (by norm_num : (0:ℝ) < 1)
    (by exact_mod_cast (by simpa using hM : M ≤ 1*d^2)) hε hε1
  exact Policy.source_uniform_of_pointwise L ρ (by omega) (hL _ inferInstance) ε hs
end MemoryPrecision.Kernel


end

end OAI
