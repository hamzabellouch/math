import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge41

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined336_part0 : Sparse := [([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 1, -2, -1, 0, 1], 9), ([0, 1, 1, -2, -1, 1, 0], 9), ([0, 1, 1, -1, -2, 0, 1], -9), ([0, 1, 1, -1, -2, 1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], -27), ([0, 1, 1, -1, 0, -1, 0], -27), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, 0, -2, 0, 0], -27), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 2, -1, -2, 0, 0], -27), ([0, 1, 2, -1, -1, -1, 0], 9), ([0, 2, 0, -1, -1, 0, 0], -18), ([0, 2, 1, -2, -1, 0, 0], -36), ([0, 2, 1, -1, -2, 0, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 2, -1, -1, 0, 0], 36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 1, -2, -1, 0, 1], 9)]

def combined336_part1 : Sparse := [([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -2, 0, 0, 0], 27), ([1, 1, 1, -1, -2, 1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], -27), ([1, 1, 1, -1, -1, 1, -1], 27), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, 0, -2, 0, 0], -27), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 2, -2, -1, 0, 0], -27), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 2, 0, -1, -1, 0, 0], -18), ([1, 2, 1, -1, -2, 0, 0], 36)]

def combined336 : Sparse := combined336_part0 ++ combined336_part1

theorem combined336_checked : Certificate.Integer.Sparse.merge source114 source120 = combined336 := by
  decide +kernel

theorem combined336_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined336 (momentValues f) = 0 := by
  rw [← combined336_checked, Certificate.Integer.Sparse.eval_merge,
    source114_zero f hcross, source120_zero f hcross, add_zero]

def combined337_part0 : Sparse := [([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 1, 0, -1, -1, 0, 1], 27), ([0, 1, 0, -1, -1, 1, 0], -27), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 1, -2, -1, 0, 1], 9), ([0, 1, 1, -1, -2, 0, 1], -9), ([0, 1, 1, -1, -2, 1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], -18), ([0, 1, 1, -1, 0, -1, 0], -27), ([0, 1, 1, 0, -2, 0, 0], -18), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 2, -1, -2, 0, 0], -27), ([0, 1, 2, -1, -1, -1, 0], 9), ([0, 2, 0, -1, -1, 0, 0], -18), ([0, 2, 1, -2, -1, 0, 0], -27), ([0, 2, 1, -1, -2, 0, 0], 27), ([0, 2, 1, -1, -1, -1, 0], -9), ([0, 2, 1, -1, -1, 0, -1], 9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 2, -1, -1, 0, 0], 18)]

def combined337_part1 : Sparse := [([1, 1, 0, -1, -1, 0, 1], 27), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -2, 0, 0, 0], 18), ([1, 1, 1, -1, -2, 0, 1], -9), ([1, 1, 1, -1, -1, -1, 1], -18), ([1, 1, 1, -1, -1, 1, -1], 18), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, 0, -2, 0, 0], -18), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 2, -2, -1, 0, 0], -27), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 2, 0, -1, -1, 0, 0], -18), ([1, 2, 1, -1, -2, 0, 0], 27), ([1, 2, 1, -1, -1, -1, 0], -9)]

def combined337 : Sparse := combined337_part0 ++ combined337_part1

theorem combined337_checked : Certificate.Integer.Sparse.merge combined336 source180 = combined337 := by
  decide +kernel

theorem combined337_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined337 (momentValues f) = 0 := by
  rw [← combined337_checked, Certificate.Integer.Sparse.eval_merge,
    combined336_zero f hcross, source180_zero f hcross, add_zero]

def combined338_part0 : Sparse := [([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 1, 0, -1, -1, 0, 1], 27), ([0, 1, 0, -1, -1, 1, 0], -27), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, 0, -1, 0, 0], -18), ([0, 1, 1, -2, -1, 0, 1], 9), ([0, 1, 1, -1, -2, 0, 1], -18), ([0, 1, 1, -1, -2, 1, 0], 18), ([0, 1, 1, -1, -1, -1, 1], -9), ([0, 1, 1, -1, 0, -1, 0], -27), ([0, 1, 1, 0, -2, 0, 0], -18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 2, -1, -2, 0, 0], -18), ([0, 1, 2, -1, -1, -1, 0], 9), ([0, 1, 2, -1, -1, 0, -1], -9), ([0, 2, 0, -1, -1, 0, 0], -9), ([0, 2, 1, -2, -1, 0, 0], -27), ([0, 2, 1, -1, -2, 0, 0], 18), ([0, 2, 1, -1, -1, -1, 0], -9), ([0, 2, 1, -1, -1, 0, -1], 9), ([1, 0, 1, -1, -1, 0, 1], -9)]

def combined338_part1 : Sparse := [([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 2, -1, -1, 0, 0], 9), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, 0, -1, 0, 0], -18), ([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -1, -2, 0, 1], -18), ([1, 1, 1, -1, -1, -1, 1], -9), ([1, 1, 1, -1, -1, 1, -1], 9), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, 0, -2, 0, 0], -18), ([1, 1, 1, 0, -1, -1, 0], 18), ([1, 1, 2, -2, -1, 0, 0], -27), ([1, 1, 2, -1, -1, -1, 0], -9), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 2, 0, -1, -1, 0, 0], -9), ([1, 2, 1, -1, -2, 0, 0], 18), ([1, 2, 1, -1, -1, -1, 0], -18), ([1, 2, 1, -1, -1, 0, -1], -9)]

def combined338 : Sparse := combined338_part0 ++ combined338_part1

theorem combined338_checked : Certificate.Integer.Sparse.merge combined337 source265 = combined338 := by
  decide +kernel

theorem combined338_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined338 (momentValues f) = 0 := by
  rw [← combined338_checked, Certificate.Integer.Sparse.eval_merge,
    combined337_zero f hcross, source265_zero f hcross, add_zero]

def combined339_part0 : Sparse := [([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, 0, -1, 0, 0], 18), ([0, 1, 0, -1, -1, 0, 1], 18), ([0, 1, 0, -1, -1, 1, 0], -18), ([0, 1, 0, -1, 0, 0, 0], 18), ([0, 1, 0, 0, -1, 0, 0], -18), ([0, 1, 1, -2, -1, 0, 1], 18), ([0, 1, 1, -1, -2, 0, 1], -18), ([0, 1, 1, -1, -2, 1, 0], 18), ([0, 1, 1, -1, 0, -1, 0], -18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 2, -1, -2, 0, 0], -18), ([0, 1, 2, -1, -1, -1, 0], 18), ([0, 2, 1, -2, -1, 0, 0], -18), ([0, 2, 1, -1, -2, 0, 0], 18), ([0, 2, 1, -1, -1, -1, 0], -18), ([0, 2, 1, -1, -1, 0, -1], 18), ([1, 0, 1, -1, -1, 1, 0], -18), ([1, 0, 1, -1, 0, 0, 0], 18), ([1, 1, 0, -1, -1, 0, 1], 18), ([1, 1, 0, 0, -1, 0, 0], -18), ([1, 1, 1, -2, -1, 1, 0], 18), ([1, 1, 1, -1, -2, 0, 1], -18)]

def combined339_part1 : Sparse := [([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, 0, -1, -1, 0], 18), ([1, 1, 2, -2, -1, 0, 0], -18), ([1, 1, 2, -1, -1, 0, -1], 18), ([1, 2, 1, -1, -2, 0, 0], 18), ([1, 2, 1, -1, -1, -1, 0], -18)]

def combined339 : Sparse := combined339_part0 ++ combined339_part1

theorem combined339_checked : Certificate.Integer.Sparse.merge combined338 source325 = combined339 := by
  decide +kernel

theorem combined339_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined339 (momentValues f) = 0 := by
  rw [← combined339_checked, Certificate.Integer.Sparse.eval_merge,
    combined338_zero f hcross, source325_zero f hcross, add_zero]

def combined340_part0 : Sparse := [([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 2, -1, 0, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 1, -2, 1, -1, 0], -9), ([0, 1, 1, -1, -1, -1, 1], -27), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, 0, -2, 0], -27), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 2, -2, 0, -1, 0], -27), ([0, 1, 2, -1, -1, -1, 0], -9), ([0, 1, 2, -1, 0, -2, 0], 27), ([0, 1, 2, -1, 0, -1, -1], 9), ([0, 2, 1, -1, 0, -2, 0], -36), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 2, -1, 0, -1, 0], -36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 1, -2, 0, -1, 1], -9), ([1, 1, 1, -2, 0, 0, 0], 27)]

def combined340_part1 : Sparse := [([1, 1, 1, -1, -1, -1, 1], -27), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, 0, -2, 1], -9), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -2, 0], -9), ([1, 1, 1, -1, 1, -1, -1], 27), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 0, 0, -2, 0], -27), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 2, -1, -1, -1, 0], -9), ([1, 1, 2, -1, 0, -2, 0], 27), ([1, 2, 0, -1, 0, -1, 0], 18), ([1, 2, 1, -2, 0, -1, 0], -36)]

def combined340 : Sparse := combined340_part0 ++ combined340_part1

theorem combined340_checked : Certificate.Integer.Sparse.merge source115 source122 = combined340 := by
  decide +kernel

theorem combined340_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined340 (momentValues f) = 0 := by
  rw [← combined340_checked, Certificate.Integer.Sparse.eval_merge,
    source115_zero f hcross, source122_zero f hcross, add_zero]

def combined341_part0 : Sparse := [([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 2, -1, 0, -1, 0], -18), ([0, 1, 0, -1, 0, -1, 1], -27), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], -18), ([0, 1, 1, -1, -1, 0, 0], -27), ([0, 1, 1, -1, 0, -2, 1], -9), ([0, 1, 1, -1, 1, -2, 0], 9), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, 0, -2, 0], -18), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 2, -2, 0, -1, 0], -27), ([0, 1, 2, -1, -1, -1, 0], -9), ([0, 1, 2, -1, 0, -2, 0], 27), ([0, 1, 2, -1, 0, -1, -1], 9), ([0, 2, 1, -1, -1, -1, 0], 9), ([0, 2, 1, -1, 0, -2, 0], -27), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 2, -1, 0, -1, 0], -18)]

def combined341_part1 : Sparse := [([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 1, -2, 0, 0, 0], 18), ([1, 1, 1, -2, 1, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], -18), ([1, 1, 1, -1, 0, -2, 1], -9), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, -1, 1, -1, -1], 18), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 0, 0, -2, 0], -18), ([1, 1, 2, -1, -1, -1, 0], -9), ([1, 1, 2, -1, 0, -2, 0], 27), ([1, 2, 0, -1, 0, -1, 0], 18), ([1, 2, 1, -2, 0, -1, 0], -27), ([1, 2, 1, -1, 0, -1, -1], 9)]

def combined341 : Sparse := combined341_part0 ++ combined341_part1

theorem combined341_checked : Certificate.Integer.Sparse.merge combined340 source182 = combined341 := by
  decide +kernel

theorem combined341_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined341 (momentValues f) = 0 := by
  rw [← combined341_checked, Certificate.Integer.Sparse.eval_merge,
    combined340_zero f hcross, source182_zero f hcross, add_zero]

def combined342_part0 : Sparse := [([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 0, 2, -1, 0, -1, 0], -9), ([0, 1, 0, -1, 0, -1, 1], -27), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 0, 0, 0, -1, 0], 18), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], -9), ([0, 1, 1, -1, -1, 0, 0], -27), ([0, 1, 1, -1, 0, -2, 1], -18), ([0, 1, 1, -1, 1, -2, 0], 18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 0, 0, -2, 0], -18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 2, -2, 0, -1, 0], -27), ([0, 1, 2, -1, -1, -1, 0], -9), ([0, 1, 2, -1, 0, -2, 0], 18), ([0, 1, 2, -1, 0, -1, -1], 9), ([0, 2, 1, -1, -1, -1, 0], 9), ([0, 2, 1, -1, 0, -2, 0], -18), ([0, 2, 1, -1, 0, -1, -1], -9), ([1, 0, 1, -1, 0, -1, 1], 18)]

def combined342_part1 : Sparse := [([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], -18), ([1, 0, 2, -1, 0, -1, 0], -9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 1, -2, 1, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], -9), ([1, 1, 1, -1, 0, -2, 1], -18), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, -1, 1, -1, -1], 9), ([1, 1, 1, 0, -1, -1, 0], 18), ([1, 1, 1, 0, 0, -2, 0], -18), ([1, 1, 2, -1, -1, -1, 0], -18), ([1, 1, 2, -1, 0, -2, 0], 18), ([1, 1, 2, -1, 0, -1, -1], -9), ([1, 2, 0, -1, 0, -1, 0], 9), ([1, 2, 1, -2, 0, -1, 0], -27), ([1, 2, 1, -1, -1, -1, 0], -9), ([1, 2, 1, -1, 0, -1, -1], 9)]

def combined342 : Sparse := combined342_part0 ++ combined342_part1

theorem combined342_checked : Certificate.Integer.Sparse.merge combined341 source277 = combined342 := by
  decide +kernel

theorem combined342_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined342 (momentValues f) = 0 := by
  rw [← combined342_checked, Certificate.Integer.Sparse.eval_merge,
    combined341_zero f hcross, source277_zero f hcross, add_zero]

def combined343_part0 : Sparse := [([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 0, 0, 0], 18), ([0, 0, 1, -1, 1, -1, 0], -18), ([0, 0, 1, 0, 0, -1, 0], -18), ([0, 1, 0, -1, 0, -1, 1], -18), ([0, 1, 0, 0, 0, -1, 0], 18), ([0, 1, 1, -2, 0, -1, 1], 18), ([0, 1, 1, -1, -1, 0, 0], -18), ([0, 1, 1, -1, 0, -2, 1], -18), ([0, 1, 1, -1, 1, -2, 0], 18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 2, -2, 0, -1, 0], -18), ([0, 1, 2, -1, -1, -1, 0], -18), ([0, 1, 2, -1, 0, -2, 0], 18), ([0, 1, 2, -1, 0, -1, -1], 18), ([0, 2, 1, -1, -1, -1, 0], 18), ([0, 2, 1, -1, 0, -2, 0], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, 0, 0, -1, 0], -18), ([1, 1, 0, -1, 0, 0, 0], 18), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 1, -2, 1, -1, 0], 18), ([1, 1, 1, -1, 0, -2, 1], -18)]

def combined343_part1 : Sparse := [([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, 0, -1, -1, 0], 18), ([1, 1, 2, -1, -1, -1, 0], -18), ([1, 1, 2, -1, 0, -2, 0], 18), ([1, 2, 1, -2, 0, -1, 0], -18), ([1, 2, 1, -1, 0, -1, -1], 18)]

def combined343 : Sparse := combined343_part0 ++ combined343_part1

theorem combined343_checked : Certificate.Integer.Sparse.merge combined342 source385 = combined343 := by
  decide +kernel

theorem combined343_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined343 (momentValues f) = 0 := by
  rw [← combined343_checked, Certificate.Integer.Sparse.eval_merge,
    combined342_zero f hcross, source385_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
