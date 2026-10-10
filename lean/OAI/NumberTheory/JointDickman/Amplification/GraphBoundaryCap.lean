import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphPointCap
import OAI.NumberTheory.JointDickman.Counting.GraphCountingSupport
import OAI.NumberTheory.JointDickman.Probability.CutNormParameter
import OAI.NumberTheory.JointDickman.Counting.BlockCutNorm

namespace OAI

/-! # A uniform bound for the finitely many left boundary blocks -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem rawArithmeticGraphKernel_uniform_bound {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T N : ℕ) (j : ℤ) (n : ℕ),
      rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ (arithmeticGraphTriples B T).card := by
  filter_upwards [graphTripleWeight_le_one hL hτ hτsmall] with B hb
  intro C T N j n
  unfold rawArithmeticGraphKernel
  rw [sum_div]
  calc
    _ ≤ ∑ _g ∈ arithmeticGraphTriples B T, (1 : ℝ) := by
      apply sum_le_sum
      intro g _
      split_ifs
      · exact hb C T n g
      · simp
    _ = _ := by simp

theorem arithmeticBlockMatrix_entry_bound {B L T N H M : ℕ} {τ C R : ℝ}
    (hR : 0 ≤ R)
    (hraw : ∀ j n, rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ R)
    (s : ℤ) (i k : Fin M) :
    |arithmeticBlockMatrix B L τ C T N H M s i k| ≤ R/((T : ℝ)*N) := by
  unfold arithmeticBlockMatrix
  dsimp only
  split_ifs
  · have hp := rawArithmeticGraphKernel_nonneg B L τ C T N
      (((k.val : ℤ)+1)-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)).toNat
    rw [abs_of_nonneg (div_nonneg hp (by positivity)),
      show (B : ℝ)*T*N = (B : ℝ)*((T : ℝ)*N) by ring,← div_div]
    exact div_le_div_of_nonneg_right (hraw _ _) (by positivity)
  · simp only [abs_zero]
    positivity

theorem arithmeticBlockMatrix_energy_cap {B L T N H M : ℕ} {τ C R : ℝ}
    (hM : 0 < M) (hR : 0 ≤ R)
    (hraw : ∀ j n, rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ R)
    (s : ℤ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) :
    |(complexEnergy (arithmeticBlockMatrix B L τ C T N H M s) (blockLabels M s F)).re|/(M : ℝ) ≤
      16*(M : ℝ)*(R/((T : ℝ)*N)) := by
  apply (complexEnergy_re_cutNorm_le M _ _ (fun i => hF _)).trans
  have hc := kernelAbsoluteMass_entry_bound hM (arithmeticBlockMatrix B L τ C T N H M s)
    (arithmeticBlockMatrix_entry_bound hR hraw s)
  exact (mul_le_mul_of_nonneg_left ((kernelCutNorm_le_absolute_mass _).trans hc)
    (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring)

theorem complexEnergy_div_real {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) (c : ℝ) :
    complexEnergy (fun i k => K i k/c) z = complexEnergy K z/(c : ℂ) := by
  simp only [complexEnergy,Complex.ofReal_div,div_mul_eq_mul_div,sum_div]

theorem arithmeticBlockMatrix_energy_scale (B L T H M N u : ℕ) (τ C : ℝ) (F : ℕ → ℂ) :
    (complexEnergy (arithmeticBlockMatrix B L τ C T N H M (u : ℤ))
      (blockLabels M (u : ℤ) F)).re =
    (complexEnergy (finiteGraphKernel B L T H M N u τ C) (fun i => F (u+(i.val+1)))).re/
      ((T : ℝ)*N) := by
  have hmat := funext (fun i => funext (fun k => arithmeticBlockMatrix_eq_finiteGraph B L T H M N u τ C i k))
  have hz : blockLabels M (u : ℤ) F = fun i => F (u+(i.val+1)) := by
    funext i
    apply congrArg F
    omega
  rw [hmat,hz,complexEnergy_div_real]
  generalize complexEnergy (finiteGraphKernel B L T H M N u τ C) (fun i => F (u+(i.val+1))) = z
  change (z/(((T : ℝ)*N : ℝ) : ℂ)).re = z.re/((T : ℝ)*N)
  rw [Complex.div_ofReal_re]

end JointDickman

end OAI
