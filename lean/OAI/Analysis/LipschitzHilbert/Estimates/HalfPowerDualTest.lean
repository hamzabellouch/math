import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionL4

namespace OAI

/-! The explicit dual test for exponent three-halves, with its second,
fourth and third moments. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def halfPowerDualTest (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*g x

theorem halfPowerDualTest_measurable (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (halfPowerDualTest g) := by unfold halfPowerDualTest; fun_prop

theorem halfPowerDualTest_norm (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖=‖g x‖^(1/2:ℝ) := by
  by_cases hz : g x=0
  · simp [halfPowerDualTest,hz]
  have hp : 0<‖g x‖ := norm_pos_iff.mpr hz
  rw [halfPowerDualTest,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  conv_lhs => rhs; rw [←Real.rpow_one ‖g x‖]
  rw [←Real.rpow_add hp]
  norm_num

theorem halfPowerDualTest_norm_sq (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^2=‖g x‖ := by
  rw [halfPowerDualTest_norm,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem halfPowerDualTest_norm_fourth (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^4=‖g x‖^2 := by
  rw [show (4:ℕ)=2*2 by decide,pow_mul,halfPowerDualTest_norm_sq]

theorem halfPowerDualTest_norm_cube (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^3=‖g x‖^(3/2:ℝ) := by
  rw [halfPowerDualTest_norm,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem halfPowerDualTest_pair (g : ℝ → ℂ) (x : ℝ) :
    g x*conj (halfPowerDualTest g x)=((‖g x‖^(3/2:ℝ):ℝ):ℂ) := by
  by_cases hz : g x=0
  · simp [halfPowerDualTest,hz]
  have hp : 0<‖g x‖ := norm_pos_iff.mpr hz
  simp only [halfPowerDualTest,map_mul,Complex.conj_ofReal]
  calc
    _ = ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*(g x*conj (g x)) := by ring
    _ = ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*(‖g x‖:ℂ)^2 := by rw [Complex.mul_conj']
    _ = ((‖g x‖^(3/2:ℝ):ℝ):ℂ) := by
      rw [←Complex.ofReal_pow,←Complex.ofReal_mul,←Real.rpow_natCast,←Real.rpow_add hp]
      norm_num

theorem halfPowerDualTest_memLp (g : ℝ → ℂ) (hgm : Measurable g)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    MemLp (halfPowerDualTest g) 2 volume ∧ MemLp (halfPowerDualTest g) 4 volume := by
  have hm := halfPowerDualTest_measurable g hgm
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    simpa only [halfPowerDualTest_norm_sq] using hg1.norm
  · apply (memLp_fourth_iff _ hm.aestronglyMeasurable).2
    simpa only [halfPowerDualTest_norm_fourth] using hg2.integrable_norm_pow (by decide : 2≠0)

theorem halfPowerDualTest_bound (g : ℝ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖≤B) :
    ∀ x, ‖halfPowerDualTest g x‖≤B+1 := by
  have hBp : 0≤B := (norm_nonneg _).trans (hB 0)
  intro x
  have hs : ‖halfPowerDualTest g x‖^2≤B := by rw [halfPowerDualTest_norm_sq]; exact hB x
  nlinarith [norm_nonneg (halfPowerDualTest g x),sq_nonneg B]

end LipschitzHilbert.PacketRepresentation

end

end OAI
