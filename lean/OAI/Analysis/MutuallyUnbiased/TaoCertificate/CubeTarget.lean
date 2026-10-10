import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def cubeTarget : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -3, 0, 0, 0, 3, 0], 36), ([0, -3, 0, 0, 3, 0, 0], 36), ([0, -3, 0, 3, 0, 0, 0], 36), ([0, -3, 3, 0, 0, 0, 0], 36), ([0, 0, -3, 0, 0, 0, 3], 36), ([0, 0, -3, 0, 0, 3, 0], 36), ([0, 0, -3, 0, 3, 0, 0], 36), ([0, 0, -3, 3, 0, 0, 0], 36), ([0, 0, 0, -3, 0, 0, 3], 36), ([0, 0, 0, -3, 0, 3, 0], 36), ([0, 0, 0, -3, 3, 0, 0], 36), ([0, 0, 0, 0, -3, 0, 3], 36), ([0, 0, 0, 0, -3, 3, 0], 36), ([0, 0, 0, 0, 0, -3, 3], 36), ([0, 0, 0, 0, 0, 3, -3], 36), ([0, 0, 0, 0, 3, -3, 0], 36), ([0, 0, 0, 0, 3, 0, -3], 36), ([0, 0, 0, 3, -3, 0, 0], 36), ([0, 0, 0, 3, 0, -3, 0], 36), ([0, 0, 0, 3, 0, 0, -3], 36), ([0, 0, 3, -3, 0, 0, 0], 36), ([0, 0, 3, 0, -3, 0, 0], 36), ([0, 0, 3, 0, 0, -3, 0], 36), ([0, 0, 3, 0, 0, 0, -3], 36), ([0, 3, -3, 0, 0, 0, 0], 36), ([0, 3, 0, -3, 0, 0, 0], 36), ([0, 3, 0, 0, -3, 0, 0], 36), ([0, 3, 0, 0, 0, -3, 0], 36), ([0, 3, 0, 0, 0, 0, -3], 36)]

theorem cubeTarget_checked : normalize cubeTerms = cubeTarget := by decide +kernel

theorem cubeTarget_value (f : Charge → ℂ) :
    Certificate.Integer.Sparse.eval cubeTarget (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) := by
  rw [← cubeTarget_checked, eval_normalize, eval_cubeTerms]

end MUB6.TaoCertificate

end OAI
