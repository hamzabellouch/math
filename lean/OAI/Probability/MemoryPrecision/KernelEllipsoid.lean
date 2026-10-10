import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.EllipsoidSuccess

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision Policy

lemma chord_real_coefficient {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : Admissible L ρ (UniformSphere d)) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ} (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal
      ((T+1:ℝ) * ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d (2^M)^BlockCount T (d/8))) := by
  apply (Policy.chord_real_bound L ρ hL hd hε hαlo hαhi).trans_eq
  rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ T+1)]
  congr 1
  simp [ENNReal.ofReal_add]

lemma chord_half_sphere_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : Admissible L ρ (UniformSphere d)) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/10) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal
      (4^d * ε^(((d:ℝ)-1)/2) *
        (SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^BlockCount T (d/8)) := by
  by_cases hT : T = 0
  · subst T
    simp only [blockCount_zero, pow_zero, mul_one]
    exact (Policy.chord_zero_bound L ρ hL (by omega) hε).trans
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
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : Admissible L ρ (UniformSphere d)) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal
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

end MemoryPrecision.Kernel

namespace MemoryPrecision.Kernel
open Policy
def BlockCount (T p : ℕ) : ℕ := ⌈(T:ℝ)/(p:ℝ)⌉₊
def SourceEllipsoidStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let four : ℝ := @OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))
  let ten : ℝ := @OfNat.ofNat ℝ 10 (@instOfNatAtLeastTwo ℝ 10 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 8)))
  ∃ C C₀ : ℝ, 1 ≤ C ∧ 1 ≤ C₀ ∧
  ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/ten →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ K : Ω → Policy d M T, Policy.Admissible K ρ (UniformSphere d) →
    Policy.Success K ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      (four^d * ε^(((d:ℝ)-1)/two) *
        (C^d * (((d/8+2)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    Policy.ChordSuccess K ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      (C₀^d * ε^((d:ℝ)/two-1) *
        (C^d * (((2*(d/8)+4)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    {x : Sphere d × Sphere d | Real.arccos (@inner ℝ (Vector d)
      (@InnerProductSpace.toInner ℝ (Vector d) _
        (PiLp.seminormedAddCommGroup
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
          (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      x.2.val x.1.val) ≤ ε} ⊆
    {x | @Dist.dist (Vector d)
      (PiLp.instDist (p := @OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
        (α := fun _ : Fin d => ℝ)) x.2.val x.1.val ≤ ε}

theorem source_ellipsoid_success : SourceEllipsoidStatement := by
  refine ⟨MemoryPrecision.SuccessConstant, 12, MemoryPrecision.successConstant_one, by norm_num, ?_⟩
  intro d M T hd ε hε hε1 Ω _ ρ hρ L hL
  have : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  refine ⟨le_min (Policy.success_le_one L ρ (UniformSphere d) ε) ?_,
    le_min (Policy.chordSuccess_le_one L ρ (UniformSphere d) ε) ?_, ?_⟩
  · exact (Policy.success_le_chord L ρ (UniformSphere d) ε).trans
      (chord_half_sphere_bound L ρ hL hd hε hε1)
  · exact chord_half_ambient_bound L ρ hL hd hε
  · intro x hx
    exact (NoiselessRegression.chord_le_arccos x.2 x.1).trans hx
end MemoryPrecision.Kernel


end

end OAI
