import Mathlib.Topology.Algebra.InfiniteSum.Real
import OAI.Analysis.Laughlin.Asymptotics.Basic
import OAI.Analysis.Laughlin.Asymptotics.Bound

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1/2 : ℝ)^z)) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range z,
      ((-(i : ℝ) + 1*(Q : ℝ))/(-(2+(i : ℝ))+2*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range z, (1/2 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) (-(2+(i : ℝ))) 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range z,
      ((-(i : ℝ) + 1*(Q : ℝ))/(-(2+(i : ℝ))+2*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => fallingRatio Q z) := by
    filter_upwards [eventually_ge_atTop (max z 4)] with Q hQ
    have hzQ : z ≤ Q := le_trans (le_max_left _ _) hQ
    have h4 : 4 ≤ Q := le_trans (le_max_right _ _) hQ
    unfold fallingRatio
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    simp only [Nat.cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hiQ : i ≤ Q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hzQ
    rw [Nat.cast_sub hiQ, Nat.cast_sub (by omega : i ≤ 2*Q-2),
      Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    congr 1 <;> ring
  have hh := hp.congr' he
  simpa [div_pow] using hh

theorem gramEigenvalueFormula_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => gramEigenvalueFormula Q z) atTop
      (𝓝 ((3*(z : ℝ)-1)*(-1/2 : ℝ)^z)) := by
  have hb : Tendsto (fun Q : ℕ =>
      (3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ))) atTop (𝓝 (3*(z : ℝ)-1)) := by
    have hh := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((z : ℝ)*((z : ℝ)+1))
    simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hh
  have hh := ((fallingRatio_tendsto z).const_mul ((-1 : ℝ)^z)).mul hb
  have he : (-1 : ℝ)^z * (1/2 : ℝ)^z * (3*(z : ℝ)-1) =
      (3*(z : ℝ)-1)*(-1/2 : ℝ)^z := by
    rw [← mul_pow]
    ring
  simpa only [gramEigenvalueFormula, he] using hh

theorem tail_majorant_summable :
    Summable (fun z : ℕ => 6*(z : ℝ)*((z : ℝ)+1)*(2/3 : ℝ)^z) := by
  have hr : ‖(2/3 : ℝ)‖ < 1 := by norm_num
  have hs := ((summable_pow_mul_geometric_of_norm_lt_one 2 hr).add
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr)).mul_left (6 : ℝ)
  convert! hs using 1
  ext z
  ring

end Laughlin

end OAI
