import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBudget

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_kernelCoefficient_intervals :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T/2 ≤ Real.log Z →
      let X := parameterX T
      let k := evenMomentParameter X Z
      let S := (2*Z)^k
      X*Z^10 ≤ S ∧ S ≤ X*Z^13 := by
  filter_upwards [eventually_tuple_product_scale,
    parameterX_tendsto.eventually_gt_atTop 0] with T htuple hXpos
  intro Z hZl
  dsimp only
  have hs := htuple Z hZl (fun _ => 2*Z) (by intro i; omega)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hs
  have hlo : parameterX T*Z^10 ≤ (2*Z)^evenMomentParameter (parameterX T) Z := by
    have hh := (le_div_iff₀ (by exact_mod_cast hXpos : (0 : ℝ) < parameterX T)).mp hs.1
    have hn : Z^10*parameterX T ≤ (2*Z)^evenMomentParameter (parameterX T) Z := by exact_mod_cast hh
    simpa only [mul_comm] using hn
  have hhi : (2*Z)^evenMomentParameter (parameterX T) Z ≤ parameterX T*Z^13 := by
    have hh := (div_le_iff₀ (by exact_mod_cast hXpos : (0 : ℝ) < parameterX T)).mp hs.2
    have hn : (2*Z)^evenMomentParameter (parameterX T) Z ≤ Z^13*parameterX T := by exact_mod_cast hh
    simpa only [mul_comm] using hn
  exact ⟨hlo, hhi⟩

end Ostmann.QuadraticCenter

end

end OAI
