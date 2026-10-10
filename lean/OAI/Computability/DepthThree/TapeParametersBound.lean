import OAI.Computability.DepthThree.TapeParameters
import OAI.Computability.DepthThree.TapeParameterCost

namespace OAI

namespace DepthThreeLowerBound
namespace TapeParameters

theorem cost_le (n : ℕ) : cost n ≤ 600 * (n + 3) ^ 8 := by
  have hd : dataDimension n ≤ n := Nat.div_le_self n 5
  have hbase : (dataDimension n + 3) ^ 8 ≤ (n + 3) ^ 8 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hd 3) 8
  have hc := Nat.le_trans (TapeParameterCost.cube_cost (dataDimension n))
    (Nat.mul_le_mul_left 200 hbase)
  have hs := Nat.le_trans (TapeParameterCost.sixth_cost (dataDimension n))
    (Nat.mul_le_mul_left 200 hbase)
  have hpbase : (dataDimension n + 1) ^ 7 ≤ (n + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : dataDimension n + 1 ≤ n + 3) 7)
      (Nat.pow_le_pow_right (by omega : 0 < n + 3) (by decide : 7 ≤ 8))
  have hp := Nat.le_trans (TapeParameterCost.power_cost (by decide : 2 ≤ 6)
    (dataDimension n)) (Nat.mul_le_mul_left 108 hpbase)
  have hn : n ≤ (n + 3) ^ 8 := by
    calc
      n ≤ n + 3 := by omega
      _ = (n + 3) ^ 1 := by simp
      _ ≤ (n + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hd2 : (dataDimension n) ^ 2 ≤ (n + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : dataDimension n ≤ n + 3) 2)
      (Nat.pow_le_pow_right (by omega : 0 < n + 3) (by decide : 2 ≤ 8))
  have hpos : 1 ≤ (n + 3) ^ 8 := Nat.pow_pos (by omega)
  unfold cost
  omega

end TapeParameters
end DepthThreeLowerBound

end OAI
