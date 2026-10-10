import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.SuccessArithmetic
import OAI.Probability.MemoryPrecision.ZeroHorizon

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma chord_real_coefficient {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ} (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    uniformChordSuccess L ρ ε ≤ ENNReal.ofReal
      ((T+1:ℝ) * ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d (2^M)^BlockCount T (d/8))) := by
  apply (chord_real_bound L ρ hL hd hε hαlo hαhi).trans_eq
  rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ T+1)]
  congr 1
  simp [ENNReal.ofReal_add]

lemma chord_half_sphere_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/10) :
    uniformChordSuccess L ρ ε ≤ ENNReal.ofReal
      (4^d * ε^(((d:ℝ)-1)/2) *
        (SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^BlockCount T (d/8)) := by
  by_cases hT : T = 0
  · subst T
    simp only [blockCount_zero, pow_zero, mul_one]
    exact (chord_zero_bound L ρ hL (by omega) hε).trans
      (ENNReal.ofReal_le_ofReal (terminal_angular_zero_bound hd hε hε1))
  · have hb := chord_real_coefficient L ρ hL hd hε (le_refl (((d:ℝ)-1)/2)) (by linarith)
    have he : (d:ℝ)-1-((d:ℝ)-1)/2 = ((d:ℝ)-1)/2 := by ring
    rw [he] at hb
    apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hN : 1 ≤ 2^M := one_le_pow₀ (by norm_num)
    have hNK : 2^M ≤ (d/8+2)*2^M := by
      simp
    have hs := stopping_step_bound_three hd hN hNK (by omega : 0 < T)
    calc
      _ = (4^d * ε^(((d:ℝ)-1)/2)) * (3*((T+1:ℝ)*RealStep d (2^M)^BlockCount T (d/8))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

lemma chord_half_ambient_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    uniformChordSuccess L ρ ε ≤ ENNReal.ofReal
      (12^d * ε^((d:ℝ)/2-1) *
        (SuccessConstant^d * (((2*(d/8)+4)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^BlockCount T (d/8)) := by
  have hb := chord_real_coefficient L ρ hL hd hε (by linarith : ((d:ℝ)-1)/2 ≤ (d:ℝ)/2) le_rfl
  have he : (d:ℝ)-1-(d:ℝ)/2 = (d:ℝ)/2-1 := by ring
  rw [he] at hb
  apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have hN : 1 ≤ 2^M := one_le_pow₀ (by norm_num)
  have hNK : 2^M ≤ (2*(d/8)+4)*2^M := by
    simp
  have hR := realStep_pos d hN
  have hs := stopping_step_bound hd hN hNK T
  have hSp := stepConstant_pos
  have hK : 2*StepConstant ≤ SuccessConstant := by dsimp [SuccessConstant]; linarith
  have hroot : 0 ≤ (((2*(d/8)+4)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) := by positivity
  have hbase := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ 2*StepConstant) hK d) hroot
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (2*StepConstant)^d *
    (((2*(d/8)+4)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ))) hbase (BlockCount T (d/8))
  calc
    _ = ((3*4^d:ℝ)*ε^((d:ℝ)/2-1))*((T+1:ℝ)*RealStep d (2^M)^BlockCount T (d/8)) := by ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_right (cap_constant_le (by omega : 1 ≤ d)) (by positivity))
      (hs.trans hpow) (by positivity) (by positivity)

def EllipsoidSuccessStatement : Prop :=
  ∃ C C₀ : ℝ, 1 ≤ C ∧ 1 ≤ C₀ ∧
  ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ L : Learner d M T Ω, L.Admissible ρ →
    L.uniformSuccess ρ ε ≤ min 1 (ENNReal.ofReal
      (4^d * ε^(((d:ℝ)-1)/2) *
        (C^d * (((d/8+2)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    uniformChordSuccess L ρ ε ≤ min 1 (ENNReal.ofReal
      (C₀^d * ε^((d:ℝ)/2-1) *
        (C^d * (((2*(d/8)+4)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    {z : UnitSphere d × (Ω × Samples d T) |
      Learner.angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} ⊆
    {z | dist (L.estimate z.1 z.2.1 z.2.2).val z.1.val ≤ ε}

theorem ellipsoid_success : EllipsoidSuccessStatement := by
  refine ⟨SuccessConstant, 12, successConstant_one, by norm_num, ?_⟩
  intro d M T hd ε hε hε1 Ω _ ρ hρ L hL
  have : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  refine ⟨le_min ?_ ?_, le_min ?_ ?_, angular_event_subset_chord L ε⟩
  · exact prob_le_one
  · exact (angular_le_chord L ρ ε).trans (chord_half_sphere_bound L ρ hL hd hε hε1)
  · exact prob_le_one
  · exact chord_half_ambient_bound L ρ hL hd hε
end MemoryPrecision


end

end OAI
