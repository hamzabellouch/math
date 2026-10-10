import OAI.NumberTheory.Ostmann.ZeroDensity.Density

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem exists_actual_zero_density_exponential_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q H : ℕ) (exception : Option (PrimitiveFamily Q)) (y : ℝ),
      0 < Q → 0 < H → 0 ≤ y → y ≤ 1/2 →
      (totalZeroCount Q exception (1-y) (H : ℝ) : ℝ) ≤
        (C*(1+Real.log (Q*H : ℕ))^11) *
          Real.exp ((10*Real.log ((Q^2*H : ℕ) : ℝ))*y) := by
  obtain ⟨C,hC,hdensity⟩ := exists_actual_zero_density_constant
  refine ⟨C,hC,?_⟩
  intro Q H exception y hQ hH hy hy1
  have hp : (0 : ℝ) < (Q^2*H : ℕ) := by exact_mod_cast (by positivity : 0 < Q^2*H)
  have hd := hdensity Q H exception (1-y) hQ hH (by linarith) (by linarith)
  rw [Real.rpow_def_of_pos hp] at hd
  have he : Real.log ((Q^2*H : ℕ) : ℝ)*(10*(1-(1-y))) =
      (10*Real.log ((Q^2*H : ℕ) : ℝ))*y := by ring
  rw [he] at hd
  convert hd using 1
  ring

theorem exists_actual_weighted_zero_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q H : ℕ) (exception : Option (PrimitiveFamily Q)) (M u : ℝ),
      0 < Q → 0 < H → 0 < M → 0 ≤ u → u ≤ 1/2 →
      2*(10*Real.log ((Q^2*H : ℕ) : ℝ)) ≤ M →
      (∀ z ∈ retainedZeros Q exception (1/2) (H : ℝ), u ≤ 1-z.point.re) →
      (∑ z ∈ retainedZeros Q exception (1/2) (H : ℝ),
        Real.exp (-M*(1-z.point.re))) ≤
        (⌊M/2⌋₊+1 : ℝ)*(C*(1+Real.log (Q*H : ℕ))^11)*Real.exp (1-M*u/2) := by
  obtain ⟨C,hC,hcum⟩ := exists_actual_zero_density_exponential_constant
  refine ⟨C,hC,?_⟩
  intro Q H exception M u hQ hH hM hu hu1 hscale hstrip
  have hbase : (1 : ℝ) ≤ (Q^2*H : ℕ) := by
    have hp : 0 < Q^2*H := by positivity
    exact_mod_cast hp
  have hlog : 0 ≤ Real.log ((Q^2*H : ℕ) : ℝ) := Real.log_nonneg hbase
  have hlogQH : 0 ≤ Real.log (Q*H : ℕ) := by
    apply Real.log_nonneg
    have hp : 0 < Q*H := by positivity
    exact_mod_cast hp
  apply actual_zero_density_exp_sum_le Q exception hM (by positivity) (by positivity)
    hscale hu1 hstrip
  intro y hy
  exact hcum Q H exception y hQ hH (hu.trans hy.1) hy.2

end Ostmann.ZeroDensity

end

end OAI
