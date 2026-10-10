import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge15

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined128_part0 : Sparse := [([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 2, 0], -36), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 27), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 2, 0], -27), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, 0, -2, 1, 1, 0], -36), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -27), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, 0, -2, -1, 2, 1, 0], -36), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, -2, 1, 2, 0], 27)]

def combined128_part1 : Sparse := [([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, -1, 0, 2, 0], -27), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], 27), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], -36), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], -27)]

def combined128 : Sparse := combined128_part0 ++ combined128_part1

theorem combined128_checked : Certificate.Integer.Sparse.merge source62 source199 = combined128 := by
  decide +kernel

theorem combined128_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined128 (momentValues f) = 0 := by
  rw [← combined128_checked, Certificate.Integer.Sparse.eval_merge,
    source62_zero f hcross, source199_zero f hcross, add_zero]

def combined129_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 2, 0], -27), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 27), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, 0, -2, 1, 1, 0], -18), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 27), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -18), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], -27)]

def combined129_part1 : Sparse := [([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], -27), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, -2, 1, 2, 0], 27), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], 18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, 0, -2, 1, 1, 0], -18), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], 27), ([1, 1, -1, -1, 1, 1, -1], -18)]

def combined129 : Sparse := combined129_part0 ++ combined129_part1

theorem combined129_checked : Certificate.Integer.Sparse.merge combined128 source259 = combined129 := by
  decide +kernel

theorem combined129_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined129 (momentValues f) = 0 := by
  rw [← combined129_checked, Certificate.Integer.Sparse.eval_merge,
    combined128_zero f hcross, source259_zero f hcross, add_zero]

def combined130_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 18), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -2, -1, 1, 2, 0], -18), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 2, 1, 0], -27), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 2, 0], -18), ([0, 0, -1, -1, 1, 2, -1], -18), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 0, 1, 1, -1], -27), ([0, 0, 0, -2, 1, 1, 0], -9), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], 27), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 1, 0, 0], -27), ([0, 1, -1, -1, 1, 1, -1], -9), ([1, -1, -1, -1, 1, 1, 1], 9)]

def combined130_part1 : Sparse := [([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], -27), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -2, 1, 2, 0], 18), ([1, 0, -1, -1, 0, 2, 0], -18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, -1, 1, 2, -1], -18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], -9), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 1, -2, -1, 1, 1, 0], -9), ([1, 1, -1, -2, 1, 1, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18), ([1, 1, -1, -1, 1, 1, -1], -9)]

def combined130 : Sparse := combined130_part0 ++ combined130_part1

theorem combined130_checked : Certificate.Integer.Sparse.merge combined129 source342 = combined130 := by
  decide +kernel

theorem combined130_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined130 (momentValues f) = 0 := by
  rw [← combined130_checked, Certificate.Integer.Sparse.eval_merge,
    combined129_zero f hcross, source342_zero f hcross, add_zero]

def combined131_part0 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, 0, -2, -1, 1, 2, 0], -18), ([0, 0, -1, -2, 1, 1, 1], 18), ([0, 0, -1, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 2, 1, 0], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, -1, 1, 2, -1], -18), ([0, 0, -1, -1, 2, 1, -1], 18), ([0, 0, -1, 0, 0, 1, 0], 18), ([0, 0, -1, 0, 1, 1, -1], -18), ([0, 0, 0, -1, 0, 1, 0], -18), ([0, 0, 0, -1, 1, 0, 0], 18), ([0, 0, 0, -1, 1, 1, -1], 18), ([0, 1, -2, -1, 1, 1, 0], 18), ([0, 1, -1, -2, 1, 1, 0], -18), ([0, 1, -1, -1, 0, 1, 0], 18), ([0, 1, -1, -1, 1, 0, 0], -18), ([1, -1, -1, -1, 2, 1, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, 0, -2, -1, 1, 1, 1], 18), ([1, 0, -2, -1, 2, 1, 0], -18), ([1, 0, -1, -2, 1, 2, 0], 18), ([1, 0, -1, -1, 1, 0, 1], -18)]

def combined131_part1 : Sparse := [([1, 0, -1, -1, 1, 2, -1], -18), ([1, 0, -1, 0, 1, 0, 0], 18), ([1, 0, 0, -1, 0, 1, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18), ([1, 1, -1, -2, 1, 1, 0], -18), ([1, 1, -1, -1, 0, 1, 0], 18)]

def combined131 : Sparse := combined131_part0 ++ combined131_part1

theorem combined131_checked : Certificate.Integer.Sparse.merge combined130 source402 = combined131 := by
  decide +kernel

theorem combined131_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined131 (momentValues f) = 0 := by
  rw [← combined131_checked, Certificate.Integer.Sparse.eval_merge,
    combined130_zero f hcross, source402_zero f hcross, add_zero]

def combined132_part0 : Sparse := [([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -2, 0, -1, 1, 2], -36), ([0, 0, -2, 0, -1, 2, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, 0, -2, 1, 2], -27), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -27), ([0, 0, -1, 0, -1, 2, 0], -27), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -27), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -27)]

def combined132_part1 : Sparse := [([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, 0, -1, 0, 2], -27), ([1, 0, -1, 0, -1, 2, 0], -27), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -2, 1, 1], -36), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], -27), ([1, 1, -1, 0, -2, 1, 1], 9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 1, 0], 9)]

def combined132 : Sparse := combined132_part0 ++ combined132_part1

theorem combined132_checked : Certificate.Integer.Sparse.merge source63 source215 = combined132 := by
  decide +kernel

theorem combined132_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined132 (momentValues f) = 0 := by
  rw [← combined132_checked, Certificate.Integer.Sparse.eval_merge,
    source63_zero f hcross, source215_zero f hcross, add_zero]

def combined133_part0 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, 0, -2, 0, -1, 1, 2], -27), ([0, 0, -2, 0, -1, 2, 1], -27), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -2, 1, 2], -27), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 0, -1, 2, 0], -18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -18), ([0, 1, -1, -1, -1, 1, 1], -18), ([0, 1, -1, 0, -1, 0, 1], -27), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 1, 2], 9), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -2, 1, -1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], 9)]

def combined133_part1 : Sparse := [([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, -1, 2, 0], -18), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, 0, 0, -2, 1, 1], -18), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -18), ([1, 1, -1, 0, -2, 1, 1], 9)]

def combined133 : Sparse := combined133_part0 ++ combined133_part1

theorem combined133_checked : Certificate.Integer.Sparse.merge combined132 source323 = combined133 := by
  decide +kernel

theorem combined133_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined133 (momentValues f) = 0 := by
  rw [← combined133_checked, Certificate.Integer.Sparse.eval_merge,
    combined132_zero f hcross, source323_zero f hcross, add_zero]

def combined134_part0 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, 0, -2, 0, -1, 1, 2], -18), ([0, 0, -2, 0, -1, 2, 1], -27), ([0, 0, -2, 0, 0, 1, 1], -9), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -2, 1, 2], -18), ([0, 0, -1, 0, -2, 2, 1], -27), ([0, 0, -1, 0, -1, 0, 2], -18), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -9), ([0, 1, -2, 0, -1, 1, 1], -9), ([0, 1, -1, -1, -1, 1, 1], -9), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 1, 0], -27), ([1, -1, -1, 0, -1, 1, 2], 18), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 0, 0, 1, 1], -9)]

def combined134_part1 : Sparse := [([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], -9), ([1, 0, -2, 1, -1, 1, 1], 18), ([1, 0, -1, -1, -1, 1, 2], 18), ([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, 0, -1, 0, 2], -18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, 0, -2, 1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], -9), ([1, 1, -1, 0, -2, 1, 1], 18)]

def combined134 : Sparse := combined134_part0 ++ combined134_part1

theorem combined134_checked : Certificate.Integer.Sparse.merge combined133 source416 = combined134 := by
  decide +kernel

theorem combined134_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined134 (momentValues f) = 0 := by
  rw [← combined134_checked, Certificate.Integer.Sparse.eval_merge,
    combined133_zero f hcross, source416_zero f hcross, add_zero]

def combined135 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, 0, -2, 0, -1, 1, 2], -18), ([0, 0, -2, 0, -1, 2, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -2, 1, 2], -18), ([0, 0, -1, 0, -2, 2, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 1, -1, 0, -1, 0, 1], -18), ([0, 1, -1, 0, -1, 1, 0], -18), ([1, -1, -1, 0, -1, 1, 2], 18), ([1, -1, -1, 0, -1, 2, 1], 18), ([1, 0, -2, 1, -1, 1, 1], 18), ([1, 0, -1, -1, -1, 1, 2], 18), ([1, 0, -1, -1, -1, 2, 1], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, -1, 1, -2, 1, 1], 18), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 0, -1, 1, 0], 18), ([1, 1, -2, 0, -1, 1, 1], 18), ([1, 1, -1, 0, -2, 1, 1], 18)]

theorem combined135_checked : Certificate.Integer.Sparse.merge combined134 source476 = combined135 := by
  decide +kernel

theorem combined135_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined135 (momentValues f) = 0 := by
  rw [← combined135_checked, Certificate.Integer.Sparse.eval_merge,
    combined134_zero f hcross, source476_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
