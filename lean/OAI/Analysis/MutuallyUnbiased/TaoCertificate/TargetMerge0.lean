import OAI.Analysis.MutuallyUnbiased.TaoCertificate.CubeTarget
import OAI.Analysis.MutuallyUnbiased.TaoCertificate.KnownTarget0

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def targetCombined0_part0 : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -3, 0, 0, 0, 3, 0], 36), ([0, -3, 0, 0, 3, 0, 0], 36), ([0, -3, 0, 3, 0, 0, 0], 36), ([0, -3, 3, 0, 0, 0, 0], 36), ([0, -2, 0, 0, 1, 0, 1], 36), ([0, -2, 0, 1, 0, 0, 1], 36), ([0, -2, 0, 1, 0, 1, 0], 36), ([0, -2, 1, 0, 0, 1, 0], 36), ([0, -2, 1, 0, 1, 0, 0], 36), ([0, -1, -1, 0, 0, 0, 2], 36), ([0, -1, -1, 2, 0, 0, 0], 36), ([0, 0, -3, 0, 0, 0, 3], 36), ([0, 0, -3, 0, 0, 3, 0], 36), ([0, 0, -3, 0, 3, 0, 0], 36), ([0, 0, -3, 3, 0, 0, 0], 36), ([0, 0, 0, -3, 0, 0, 3], 36), ([0, 0, 0, -3, 0, 3, 0], 36), ([0, 0, 0, -3, 3, 0, 0], 36), ([0, 0, 0, 0, -3, 0, 3], 36), ([0, 0, 0, 0, -3, 3, 0], 36), ([0, 0, 0, 0, 0, -3, 3], 36), ([0, 0, 0, 0, 0, 3, -3], 36), ([0, 0, 0, 0, 3, -3, 0], 36)]

def targetCombined0_part1 : Sparse := [([0, 0, 0, 0, 3, 0, -3], 36), ([0, 0, 0, 3, -3, 0, 0], 36), ([0, 0, 0, 3, 0, -3, 0], 36), ([0, 0, 0, 3, 0, 0, -3], 36), ([0, 0, 3, -3, 0, 0, 0], 36), ([0, 0, 3, 0, -3, 0, 0], 36), ([0, 0, 3, 0, 0, -3, 0], 36), ([0, 0, 3, 0, 0, 0, -3], 36), ([0, 3, -3, 0, 0, 0, 0], 36), ([0, 3, 0, -3, 0, 0, 0], 36), ([0, 3, 0, 0, -3, 0, 0], 36), ([0, 3, 0, 0, 0, -3, 0], 36), ([0, 3, 0, 0, 0, 0, -3], 36), ([1, -2, 0, 0, 0, 1, 1], -36), ([1, -2, 0, 0, 1, 0, 1], 36), ([1, -2, 0, 0, 1, 1, 0], -36), ([1, -2, 0, 1, 0, 0, 1], 36), ([1, -2, 0, 1, 0, 1, 0], 36), ([1, -2, 0, 1, 1, 0, 0], -36), ([1, -2, 1, 0, 0, 0, 1], -36), ([1, -2, 1, 0, 0, 1, 0], 36), ([1, -2, 1, 0, 1, 0, 0], 36), ([1, -2, 1, 1, 0, 0, 0], -36), ([1, -1, -1, 0, 0, 0, 2], 36)]

def targetCombined0_part2 : Sparse := [([1, -1, -1, 0, 0, 2, 0], -36), ([1, -1, -1, 0, 2, 0, 0], -36), ([1, -1, -1, 2, 0, 0, 0], 36), ([1, -1, 0, -1, 0, 0, 2], -36)]

def targetCombined0 : Sparse := targetCombined0_part0 ++ targetCombined0_part1 ++ targetCombined0_part2

theorem targetCombined0_checked : Certificate.Integer.Sparse.merge cubeTarget knownTarget0 = targetCombined0 := by
  decide +kernel

theorem targetCombined0_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined0 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-54) := by
  rw [← targetCombined0_checked, Certificate.Integer.Sparse.eval_merge,
    cubeTarget_value f, knownTarget0_value f hf]

end MUB6.TaoCertificate

end OAI
