import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge40

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined328_part0 : Sparse := [([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 2, -1, 0, -1], -36), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 2, -1, 0, -1], 9), ([0, 1, 0, 1, -2, 1, -1], -9), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 1, 0, 0, -2], -27), ([0, 1, 0, 2, -2, 0, -1], -27), ([0, 1, 0, 2, -1, -1, -1], -9), ([0, 1, 0, 2, -1, 0, -2], 27), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -27), ([0, 2, 0, 1, -1, 0, -2], -36), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 2, -1, 0, -1], -36), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 27), ([1, 1, -1, 1, 0, 0, -1], -9)]

def combined328_part1 : Sparse := [([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 0, 1, -2, 0, 0], 27), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, -1, 1, -2], -9), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 0, 1, 0, 0, -2], -27), ([1, 1, 0, 2, -1, -1, -1], -9), ([1, 1, 0, 2, -1, 0, -2], 27), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 2, 0, 0, -1, 0, -1], 18), ([1, 2, 0, 1, -2, 0, -1], -36)]

def combined328 : Sparse := combined328_part0 ++ combined328_part1

theorem combined328_checked : Certificate.Integer.Sparse.merge source112 source140 = combined328 := by
  decide +kernel

theorem combined328_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined328 (momentValues f) = 0 := by
  rw [← combined328_checked, Certificate.Integer.Sparse.eval_merge,
    source112_zero f hcross, source140_zero f hcross, add_zero]

def combined329_part0 : Sparse := [([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 2, -1, 0, -1], -18), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 2, -1, 0, -1], 9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 0, 1, -1, 1, -2], 9), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 0, 1, 0, 0, -2], -18), ([0, 1, 0, 2, -2, 0, -1], -27), ([0, 1, 0, 2, -1, -1, -1], -9), ([0, 1, 0, 2, -1, 0, -2], 27), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 1, 1, -2, 0, -1], 9), ([0, 1, 1, 1, -1, -1, -1], -18), ([0, 1, 1, 1, -1, 0, -2], -9), ([0, 2, 0, 1, -1, -1, -1], 9), ([0, 2, 0, 1, -1, 0, -2], -27), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 2, -1, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 27)]

def combined329_part1 : Sparse := [([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 1, -1, 1, -1], 18), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 0, 1, -2, 0, 0], 18), ([1, 1, 0, 1, -2, 1, -1], 9), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 0, 1, 0, 0, -2], -18), ([1, 1, 0, 2, -1, -1, -1], -9), ([1, 1, 0, 2, -1, 0, -2], 27), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 2, -1, 1, -1, 0, -1], 9), ([1, 2, 0, 0, -1, 0, -1], 18), ([1, 2, 0, 1, -2, 0, -1], -27)]

def combined329 : Sparse := combined329_part0 ++ combined329_part1

theorem combined329_checked : Certificate.Integer.Sparse.merge combined328 source248 = combined329 := by
  decide +kernel

theorem combined329_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined329 (momentValues f) = 0 := by
  rw [← combined329_checked, Certificate.Integer.Sparse.eval_merge,
    combined328_zero f hcross, source248_zero f hcross, add_zero]

def combined330_part0 : Sparse := [([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 0, 2, -1, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 2, -1, 0, -1], 9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 0, 0, 0, 0, -1], 18), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 0, 1, -1, 1, -2], 18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 0, 1, 0, 0, -2], -18), ([0, 1, 0, 2, -2, 0, -1], -27), ([0, 1, 0, 2, -1, -1, -1], -9), ([0, 1, 0, 2, -1, 0, -2], 18), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 1, 1, -2, 0, -1], 9), ([0, 1, 1, 1, -1, -1, -1], -9), ([0, 1, 1, 1, -1, 0, -2], -18), ([0, 2, -1, 1, -1, 0, -1], -9), ([0, 2, 0, 1, -1, -1, -1], 9), ([0, 2, 0, 1, -1, 0, -2], -18), ([1, 0, 0, 1, -1, 1, -1], -9)]

def combined330_part1 : Sparse := [([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 0, 2, -1, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 1, -1, 1, -1], 9), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 0, 1, -2, 1, -1], 9), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 0, 1, 0, 0, -2], -18), ([1, 1, 0, 2, -1, -1, -1], -18), ([1, 1, 0, 2, -1, 0, -2], 18), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 1, 1, -1, 0, -2], -18), ([1, 2, -1, 1, -1, 0, -1], 9), ([1, 2, 0, 0, -1, 0, -1], 9), ([1, 2, 0, 1, -2, 0, -1], -27), ([1, 2, 0, 1, -1, -1, -1], -9)]

def combined330 : Sparse := combined330_part0 ++ combined330_part1

theorem combined330_checked : Certificate.Integer.Sparse.merge combined329 source351 = combined330 := by
  decide +kernel

theorem combined330_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined330 (momentValues f) = 0 := by
  rw [← combined330_checked, Certificate.Integer.Sparse.eval_merge,
    combined329_zero f hcross, source351_zero f hcross, add_zero]

def combined331_part0 : Sparse := [([0, 0, 0, 1, -1, 0, 0], 18), ([0, 0, 0, 1, -1, 1, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 2, -1, 0, -1], 18), ([0, 1, 0, 0, 0, 0, -1], 18), ([0, 1, 0, 1, -1, -1, 0], -18), ([0, 1, 0, 1, -1, 1, -2], 18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 0, 2, -2, 0, -1], -18), ([0, 1, 0, 2, -1, -1, -1], -18), ([0, 1, 0, 2, -1, 0, -2], 18), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 1, 1, -2, 0, -1], 18), ([0, 1, 1, 1, -1, 0, -2], -18), ([0, 2, 0, 1, -1, -1, -1], 18), ([0, 2, 0, 1, -1, 0, -2], -18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 1, -1, 1, -1, 0, 0], -18), ([1, 1, 0, 0, -1, 0, 0], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 1, -2, 1, -1], 18)]

def combined331_part1 : Sparse := [([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 0, 2, -1, -1, -1], -18), ([1, 1, 0, 2, -1, 0, -2], 18), ([1, 1, 1, 1, -1, 0, -2], -18), ([1, 2, -1, 1, -1, 0, -1], 18), ([1, 2, 0, 1, -2, 0, -1], -18)]

def combined331 : Sparse := combined331_part0 ++ combined331_part1

theorem combined331_checked : Certificate.Integer.Sparse.merge combined330 source459 = combined331 := by
  decide +kernel

theorem combined331_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined331 (momentValues f) = 0 := by
  rw [← combined331_checked, Certificate.Integer.Sparse.eval_merge,
    combined330_zero f hcross, source459_zero f hcross, add_zero]

def combined332_part0 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -36), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 1, -1, -1], -27), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, 0, -2, 0], -27), ([0, 1, 0, 1, 0, 0, -2], -27), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 0, 2, 0, -2, -1], -27), ([0, 1, 0, 2, 0, -1, -2], -27), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -27), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 2, 0, 0, 0, -1, -1], -18), ([0, 2, 0, 1, 0, -2, -1], -36), ([0, 2, 0, 1, 0, -1, -2], -36), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9)]

def combined332_part1 : Sparse := [([1, 0, 0, 2, 0, -1, -1], -36), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], -27), ([1, 1, -1, 2, 0, -1, -1], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 0, 1, 0, -2, 0], -27), ([1, 1, 0, 1, 0, 0, -2], -27), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 0, 2, -1, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], -18)]

def combined332 : Sparse := combined332_part0 ++ combined332_part1

theorem combined332_checked : Certificate.Integer.Sparse.merge source113 source142 = combined332 := by
  decide +kernel

theorem combined332_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined332 (momentValues f) = 0 := by
  rw [← combined332_checked, Certificate.Integer.Sparse.eval_merge,
    source113_zero f hcross, source142_zero f hcross, add_zero]

def combined333_part0 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 0, 2, 0, -1, -1], -18), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, -1, 1, 0, 0, -1], -27), ([0, 1, -1, 1, 1, -1, -1], -18), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 0, 1, 0, -2, 0], -18), ([0, 1, 0, 1, 0, 0, -2], -18), ([0, 1, 0, 2, 0, -2, -1], -27), ([0, 1, 0, 2, 0, -1, -2], -27), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 1, -1, -1, -1], -18), ([0, 2, 0, 0, 0, -1, -1], -18), ([0, 2, 0, 1, 0, -2, -1], -27), ([0, 2, 0, 1, 0, -1, -2], -27), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 2, 0, -1, -1], -18), ([1, 1, -1, 1, 1, -1, -1], -18), ([1, 1, -1, 2, 0, -1, -1], 9), ([1, 1, 0, 0, 0, -1, 0], 9)]

def combined333_part1 : Sparse := [([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 0, 1, 0, -2, 0], -18), ([1, 1, 0, 1, 0, 0, -2], -18), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 0, 1, 1, -1, -2], 9), ([1, 1, 0, 2, -1, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 1, 1, 0, -2, -1], 9), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 2, -1, 1, 0, -1, -1], 9), ([1, 2, 0, 0, 0, -1, -1], -18), ([1, 2, 0, 1, -1, -1, -1], 9)]

def combined333 : Sparse := combined333_part0 ++ combined333_part1

theorem combined333_checked : Certificate.Integer.Sparse.merge combined332 source250 = combined333 := by
  decide +kernel

theorem combined333_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined333 (momentValues f) = 0 := by
  rw [← combined333_checked, Certificate.Integer.Sparse.eval_merge,
    combined332_zero f hcross, source250_zero f hcross, add_zero]

def combined334_part0 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -18), ([0, 0, 0, 2, 0, -1, -1], -9), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, -1, 1, 1, -1, -1], -9), ([0, 1, -1, 2, 0, -1, -1], -9), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 0, 1, -1, -1, 0], -27), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 1, 0, 1, 0, 0, -2], -18), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 0, 2, 0, -2, -1], -27), ([0, 1, 0, 2, 0, -1, -2], -18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 1, -1, -1, -1], -9), ([0, 2, -1, 1, 0, -1, -1], 9), ([0, 2, 0, 0, 0, -1, -1], -9), ([0, 2, 0, 1, -1, -1, -1], -9), ([0, 2, 0, 1, 0, -2, -1], -27), ([0, 2, 0, 1, 0, -1, -2], -18), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 0, 0, 1, 1, -1, -1], 9)]

def combined334_part1 : Sparse := [([1, 0, 0, 2, 0, -1, -1], -9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 1, -1, 1, 1, -1, -1], -9), ([1, 1, -1, 2, 0, -1, -1], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 0, 0, 0, 0, -1], 18), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 0, 1, 0, 0, -2], -18), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 0, 1, 1, -1, -2], 18), ([1, 1, 0, 2, -1, -1, -1], 18), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 1, 1, 0, -2, -1], 9), ([1, 1, 1, 1, 0, -1, -2], 18), ([1, 2, -1, 1, 0, -1, -1], 18), ([1, 2, 0, 0, 0, -1, -1], -9), ([1, 2, 0, 1, -1, -1, -1], 9)]

def combined334 : Sparse := combined334_part0 ++ combined334_part1

theorem combined334_checked : Certificate.Integer.Sparse.merge combined333 source411 = combined334 := by
  decide +kernel

theorem combined334_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined334 (momentValues f) = 0 := by
  rw [← combined334_checked, Certificate.Integer.Sparse.eval_merge,
    combined333_zero f hcross, source411_zero f hcross, add_zero]

def combined335 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 1, -1, 1, 0, -1, 0], -18), ([0, 1, -1, 1, 0, 0, -1], -18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 0, 1, -1, -1, 0], -18), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 1, 0, 2, 0, -2, -1], -18), ([0, 1, 0, 2, 0, -1, -2], -18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 2, 0, 1, 0, -2, -1], -18), ([0, 2, 0, 1, 0, -1, -2], -18), ([1, 0, 0, 1, 0, -1, 0], 18), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 1, -1, 2, 0, -1, -1], 18), ([1, 1, 0, 0, 0, -1, 0], 18), ([1, 1, 0, 0, 0, 0, -1], 18), ([1, 1, 0, 1, 1, -2, -1], 18), ([1, 1, 0, 1, 1, -1, -2], 18), ([1, 1, 0, 2, -1, -1, -1], 18), ([1, 1, 1, 1, 0, -2, -1], 18), ([1, 1, 1, 1, 0, -1, -2], 18), ([1, 2, -1, 1, 0, -1, -1], 18), ([1, 2, 0, 1, -1, -1, -1], 18)]

theorem combined335_checked : Certificate.Integer.Sparse.merge combined334 source471 = combined335 := by
  decide +kernel

theorem combined335_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined335 (momentValues f) = 0 := by
  rw [← combined335_checked, Certificate.Integer.Sparse.eval_merge,
    combined334_zero f hcross, source471_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
