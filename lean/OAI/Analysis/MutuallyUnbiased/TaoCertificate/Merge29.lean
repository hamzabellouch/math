import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge28

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined232_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 2, -1, 0, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 1, -2, 0, 0], -27), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 1, -2], -9), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 1, 1, 0, 0, -2], -27), ([0, 0, 1, 2, -2, 0, -1], -27), ([0, 0, 1, 2, -1, 0, -2], -27), ([0, 0, 2, 0, -1, 0, -1], -18), ([0, 0, 2, 1, -2, 0, -1], -36), ([0, 0, 2, 1, -1, 0, -2], -36), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 1, -2, 0, -1], -9), ([0, 1, 1, 1, -1, -1, -1], -27), ([0, 1, 1, 1, -1, 0, -2], 9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], -27)]

def combined232_part1 : Sparse := [([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 2, -1, 0, -1], -36), ([1, 0, 1, 1, -2, 0, 0], -27), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 1, 1, 0, 0, -2], -27), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], -18), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, -1, 0, -2], 9)]

def combined232 : Sparse := combined232_part0 ++ combined232_part1

theorem combined232_checked : Certificate.Integer.Sparse.merge source88 source200 = combined232 := by
  decide +kernel

theorem combined232_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined232 (momentValues f) = 0 := by
  rw [← combined232_checked, Certificate.Integer.Sparse.eval_merge,
    source88_zero f hcross, source200_zero f hcross, add_zero]

def combined233_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 2, -1, 0, -1], -18), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 1, -2, 0, 0], -18), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 2, -2, 0, -1], -27), ([0, 0, 1, 2, -1, 0, -2], -27), ([0, 0, 2, 0, -1, 0, -1], -18), ([0, 0, 2, 1, -2, 0, -1], -27), ([0, 0, 2, 1, -1, 0, -2], -27), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 1, 1, -1, -1, -1], -18), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, -1, 2, 1, -1, 0, -1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 2, -1, 0, -1], -18)]

def combined233_part1 : Sparse := [([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 1, -2, 0, 0], -18), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, 1, -2], 9), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], -18), ([1, 0, 2, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -2, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 1, 1, -1, 0, -2], 9)]

def combined233 : Sparse := combined233_part0 ++ combined233_part1

theorem combined233_checked : Certificate.Integer.Sparse.merge combined232 source260 = combined233 := by
  decide +kernel

theorem combined233_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined233 (momentValues f) = 0 := by
  rw [← combined233_checked, Certificate.Integer.Sparse.eval_merge,
    combined232_zero f hcross, source260_zero f hcross, add_zero]

def combined234_part0 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -1, 0, -1], 9), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 2, -1, 0, -1], -9), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 2, -2, 0, -1], -27), ([0, 0, 1, 2, -1, -1, -1], 9), ([0, 0, 1, 2, -1, 0, -2], -18), ([0, 0, 2, 0, -1, 0, -1], -9), ([0, 0, 2, 1, -2, 0, -1], -27), ([0, 0, 2, 1, -1, -1, -1], -9), ([0, 0, 2, 1, -1, 0, -2], -18), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 1, 1, -1, -1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, -1, 2, 1, -1, 0, -1], 18)]

def combined234_part1 : Sparse := [([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 0, 0, 2, -1, 0, -1], -9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, 1, -2], 18), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 2, -1, -1, -1], 18), ([1, 0, 2, 0, -1, 0, -1], -9), ([1, 0, 2, 1, -1, -1, -1], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 1, -2, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 1, 1, -1, 0, -2], 18)]

def combined234 : Sparse := combined234_part0 ++ combined234_part1

theorem combined234_checked : Certificate.Integer.Sparse.merge combined233 source355 = combined234 := by
  decide +kernel

theorem combined234_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined234 (momentValues f) = 0 := by
  rw [← combined234_checked, Certificate.Integer.Sparse.eval_merge,
    combined233_zero f hcross, source355_zero f hcross, add_zero]

def combined235 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 0, 1, 2, -2, 0, -1], -18), ([0, 0, 1, 2, -1, 0, -2], -18), ([0, 0, 2, 1, -2, 0, -1], -18), ([0, 0, 2, 1, -1, 0, -2], -18), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 1, 1, 0, -1, 0, -1], -18), ([1, -1, 1, 2, -1, 0, -1], 18), ([1, -1, 2, 1, -1, 0, -1], 18), ([1, 0, 0, 1, -1, 0, 0], 18), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 0, 1, 0, -1, 0, 0], 18), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 1, -2, 1, -1], 18), ([1, 0, 1, 1, -1, 1, -2], 18), ([1, 0, 1, 2, -1, -1, -1], 18), ([1, 0, 2, 1, -1, -1, -1], 18), ([1, 1, 1, 1, -2, 0, -1], 18), ([1, 1, 1, 1, -1, 0, -2], 18)]

theorem combined235_checked : Certificate.Integer.Sparse.merge combined234 source463 = combined235 := by
  decide +kernel

theorem combined235_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined235 (momentValues f) = 0 := by
  rw [← combined235_checked, Certificate.Integer.Sparse.eval_merge,
    combined234_zero f hcross, source463_zero f hcross, add_zero]

def combined236_part0 : Sparse := [([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, 0, 0, -2], -27), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], -27), ([0, 0, 1, 2, 0, -1, -2], 27), ([0, 0, 2, 1, 0, -1, -2], -36), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -27), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 2, 0, -1, -1], -36), ([1, 0, 1, 0, 1, -1, -1], -36)]

def combined236_part1 : Sparse := [([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -2, 0], 27), ([1, 0, 1, 1, 0, 0, -2], -27), ([1, 0, 1, 1, 1, -1, -2], -9), ([1, 0, 1, 2, -1, -1, -1], -9), ([1, 0, 1, 2, 0, -1, -2], 27), ([1, 0, 2, 0, 0, -1, -1], 18), ([1, 0, 2, 1, 0, -2, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, 0, -2, -1], -9), ([1, 1, 1, 1, 0, -1, -2], -9)]

def combined236 : Sparse := combined236_part0 ++ combined236_part1

theorem combined236_checked : Certificate.Integer.Sparse.merge source89 source202 = combined236 := by
  decide +kernel

theorem combined236_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined236 (momentValues f) = 0 := by
  rw [← combined236_checked, Certificate.Integer.Sparse.eval_merge,
    source89_zero f hcross, source202_zero f hcross, add_zero]

def combined237_part0 : Sparse := [([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 1, 1, -1, -2], 9), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], -27), ([0, 0, 1, 2, 0, -1, -2], 27), ([0, 0, 2, 1, -1, -1, -1], 9), ([0, 0, 2, 1, 0, -1, -2], -27), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 1, -1, -1, -1], -18), ([0, 1, 1, 1, 0, -2, -1], 9), ([0, 1, 1, 1, 0, -1, -2], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 2, 1, 0, -1, -1], 9)]

def combined237_part1 : Sparse := [([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 2, 0, -1, -1], -18), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 1, 1, 0, -2, 0], 18), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 1, 2, -1, -1, -1], -9), ([1, 0, 1, 2, 0, -1, -2], 27), ([1, 0, 2, 0, 0, -1, -1], 18), ([1, 0, 2, 1, 0, -2, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 1, 1, 0, -1, -2], -9)]

def combined237 : Sparse := combined237_part0 ++ combined237_part1

theorem combined237_checked : Certificate.Integer.Sparse.merge combined236 source262 = combined237 := by
  decide +kernel

theorem combined237_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined237 (momentValues f) = 0 := by
  rw [← combined237_checked, Certificate.Integer.Sparse.eval_merge,
    combined236_zero f hcross, source262_zero f hcross, add_zero]

def combined238_part0 : Sparse := [([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, -1, 2, 1, 0, -1, -1], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -9), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 0, 0, -2], -18), ([0, 0, 1, 1, 1, -1, -2], 18), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], -27), ([0, 0, 1, 2, 0, -1, -2], 18), ([0, 0, 2, 1, -1, -1, -1], 9), ([0, 0, 2, 1, 0, -1, -2], -18), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 1, -1, -1, -1], -9), ([0, 1, 1, 1, 0, -2, -1], 9), ([0, 1, 1, 1, 0, -1, -2], -18), ([1, -1, 1, 1, 0, -1, 0], -27)]

def combined238_part1 : Sparse := [([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 1, 0, -1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 0, 2, 0, -1, -1], -9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 0, 1, 1, 0, 0, -2], -18), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 1, 2, -1, -1, -1], -18), ([1, 0, 1, 2, 0, -1, -2], 18), ([1, 0, 2, 0, 0, -1, -1], 9), ([1, 0, 2, 1, -1, -1, -1], -9), ([1, 0, 2, 1, 0, -2, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 1, 1, 0, -1, -2], -18)]

def combined238 : Sparse := combined238_part0 ++ combined238_part1

theorem combined238_checked : Certificate.Integer.Sparse.merge combined237 source415 = combined238 := by
  decide +kernel

theorem combined238_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined238 (momentValues f) = 0 := by
  rw [← combined238_checked, Certificate.Integer.Sparse.eval_merge,
    combined237_zero f hcross, source415_zero f hcross, add_zero]

def combined239_part0 : Sparse := [([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 2, 0, -1, -1], 18), ([0, 0, 0, 1, 0, -1, 0], 18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 1, 1, 1, -1, -2], 18), ([0, 0, 1, 2, -1, -1, -1], -18), ([0, 0, 1, 2, 0, -2, -1], -18), ([0, 0, 1, 2, 0, -1, -2], 18), ([0, 0, 2, 1, -1, -1, -1], 18), ([0, 0, 2, 1, 0, -1, -2], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 1, 0, -2, -1], 18), ([0, 1, 1, 1, 0, -1, -2], -18), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 2, 1, 0, -1, -1], 18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 1, 0, 0, -1, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18)]

def combined239_part1 : Sparse := [([1, 0, 1, 1, 1, -2, -1], 18), ([1, 0, 1, 2, -1, -1, -1], -18), ([1, 0, 1, 2, 0, -1, -2], 18), ([1, 0, 2, 1, 0, -2, -1], -18), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 1, 1, 0, -1, -2], -18)]

def combined239 : Sparse := combined239_part0 ++ combined239_part1

theorem combined239_checked : Certificate.Integer.Sparse.merge combined238 source475 = combined239 := by
  decide +kernel

theorem combined239_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined239 (momentValues f) = 0 := by
  rw [← combined239_checked, Certificate.Integer.Sparse.eval_merge,
    combined238_zero f hcross, source475_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
