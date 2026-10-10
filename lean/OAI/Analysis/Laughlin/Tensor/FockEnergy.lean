import OAI.Analysis.Laughlin.Operators.PhysicalPairCounting
import OAI.Analysis.Laughlin.Pair.EnergyReturn

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem tensorExterior_energy (n Q : ℕ) (ψ : State (n+2) Q) (hψ : Antisymmetric ψ) :
    sourceFockEnergy Q (tensorExterior (n+2) Q ψ) = ((n+2).factorial : ℝ)*energy ψ := by
  have hn : ‖((n+2 : ℂ)*(n+1))/(Real.sqrt 2 : ℂ)‖^2 =
      ((n+2 : ℝ)*(n+1))^2/2 := by
    rw [norm_div,norm_mul,div_pow,mul_pow]
    have h2 : ‖(Real.sqrt 2 : ℂ)‖^2 = (2 : ℝ) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by norm_num)]
    rw [h2]
    have hn2 : (n+2 : ℂ) = ((n+2 : ℝ) : ℂ) := by push_cast; rfl
    have hn1 : (n+1 : ℂ) = ((n+1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hn2,hn1,Complex.norm_of_nonneg (by positivity),Complex.norm_of_nonneg (by positivity)]
    ring
  simp only [sourceFockEnergy,sourcePairEnd_tensorExterior n Q ψ hψ,
    occupationNormSq_smul,hn,tensorExterior_norm n Q _ (headPairAmplitude_antisymmetric ψ hψ _)]
  rw [energy_head_pair n Q ψ hψ]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,← Finset.mul_sum]
  ring

theorem normalizedTensorExterior_energy (n Q : ℕ) (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) :
    sourceFockEnergy Q (normalizedTensorExterior (n+2) Q ψ) = energy ψ := by
  have hp : 0 < ((n+2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n+2)
  have hs : (Real.sqrt ((n+2).factorial : ℝ))^2 = ((n+2).factorial : ℝ) :=
    Real.sq_sqrt (le_of_lt hp)
  have he (c : ℂ) (x : Space Q) : sourceFockEnergy Q (c • x) = ‖c‖^2*sourceFockEnergy Q x := by
    simp only [sourceFockEnergy,map_smul,occupationNormSq_smul,Finset.mul_sum]
  rw [normalizedTensorExterior,he,tensorExterior_energy n Q ψ hψ]
  have hn : ‖((Real.sqrt ((n+2).factorial : ℝ))⁻¹ : ℂ)‖^2 =
      (((n+2).factorial : ℝ))⁻¹ := by
    rw [norm_inv,inv_pow]
    congr 1
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hs
  rw [hn]
  field_simp

end Laughlin.Fock

end OAI
