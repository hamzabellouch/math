import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge43

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined352_part0 : Sparse := [([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 2, 0, -1, 0, -1], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, -2, 0, 0], -27), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, -1, 1, -2], -9), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -27), ([0, 1, 2, -1, -1, 0, -1], 9), ([0, 1, 2, 0, -2, 0, -1], 27), ([0, 1, 2, 0, -1, -1, -1], -9), ([0, 1, 2, 0, -1, 0, -2], -27), ([0, 2, 1, 0, -2, 0, -1], -36), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 2, 0, -1, 0, -1], -36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, 1, -1], 27)]

def combined352_part1 : Sparse := [([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, 0, -2, 0, 0], -27), ([1, 1, 1, 0, -2, 1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 0, 0, 0, -2], 27), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 1, 2, 0, -2, 0, -1], 27), ([1, 1, 2, 0, -1, -1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], 18), ([1, 2, 1, 0, -1, 0, -2], -36)]

def combined352 : Sparse := combined352_part0 ++ combined352_part1

theorem combined352_checked : Certificate.Integer.Sparse.merge source118 source128 = combined352 := by
  decide +kernel

theorem combined352_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined352 (momentValues f) = 0 := by
  rw [← combined352_checked, Certificate.Integer.Sparse.eval_merge,
    source118_zero f hcross, source128_zero f hcross, add_zero]

def combined353_part0 : Sparse := [([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, 0, -1], 27), ([0, 0, 2, 0, -1, 0, -1], -18), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 1, -1, -1, 0, 0], -27), ([0, 1, 1, 0, -2, 0, 0], -18), ([0, 1, 1, 0, -2, 1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 1, -2, 0, -1], -9), ([0, 1, 1, 1, -1, -1, -1], -18), ([0, 1, 1, 1, -1, 0, -2], 9), ([0, 1, 2, -1, -1, 0, -1], 9), ([0, 1, 2, 0, -2, 0, -1], 27), ([0, 1, 2, 0, -1, -1, -1], -9), ([0, 1, 2, 0, -1, 0, -2], -27), ([0, 2, 1, 0, -2, 0, -1], -27), ([0, 2, 1, 0, -1, -1, -1], 9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 2, 0, -1, 0, -1], -18)]

def combined353_part1 : Sparse := [([1, 1, 0, 0, -1, 1, -1], -27), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 1, -1, -1, 1, -1], 18), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, 0, -2, 0, 0], -18), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 0, -1, 1, -2], 9), ([1, 1, 1, 0, 0, 0, -2], 18), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 2, 0, -2, 0, -1], 27), ([1, 1, 2, 0, -1, -1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], 18), ([1, 2, 1, -1, -1, 0, -1], 9), ([1, 2, 1, 0, -1, 0, -2], -27)]

def combined353 : Sparse := combined353_part0 ++ combined353_part1

theorem combined353_checked : Certificate.Integer.Sparse.merge combined352 source188 = combined353 := by
  decide +kernel

theorem combined353_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined353 (momentValues f) = 0 := by
  rw [← combined353_checked, Certificate.Integer.Sparse.eval_merge,
    combined352_zero f hcross, source188_zero f hcross, add_zero]

def combined354_part0 : Sparse := [([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 0, 2, 0, -1, 0, -1], -9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 1, 1, -1, -1, 0, 0], -27), ([0, 1, 1, 0, -2, 1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 1, -2, 0, -1], -9), ([0, 1, 1, 1, -1, -1, -1], -9), ([0, 1, 1, 1, -1, 0, -2], 18), ([0, 1, 2, -1, -1, 0, -1], 18), ([0, 1, 2, 0, -2, 0, -1], 27), ([0, 1, 2, 0, -1, -1, -1], -18), ([0, 1, 2, 0, -1, 0, -2], -18), ([0, 2, 1, -1, -1, 0, -1], 9), ([0, 2, 1, 0, -2, 0, -1], -27), ([0, 2, 1, 0, -1, -1, -1], 18), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 0, -1, 1, -1], 9)]

def combined354_part1 : Sparse := [([1, 0, 1, 1, -1, 0, -1], 27), ([1, 0, 2, 0, -1, 0, -1], -9), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 0, 0, 0, -1], 18), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 1, -1, -1, 1, -1], 9), ([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 0, -1, 1, -2], 18), ([1, 1, 1, 0, 0, 0, -2], 18), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 1, 2, 0, -2, 0, -1], 27), ([1, 1, 2, 0, -1, -1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], 9), ([1, 2, 1, -1, -1, 0, -1], 18), ([1, 2, 1, 0, -1, -1, -1], 9), ([1, 2, 1, 0, -1, 0, -2], -18)]

def combined354 : Sparse := combined354_part0 ++ combined354_part1

theorem combined354_checked : Certificate.Integer.Sparse.merge combined353 source349 = combined354 := by
  decide +kernel

theorem combined354_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined354 (momentValues f) = 0 := by
  rw [← combined354_checked, Certificate.Integer.Sparse.eval_merge,
    combined353_zero f hcross, source349_zero f hcross, add_zero]

def combined355_part0 : Sparse := [([0, 0, 1, 0, -1, 0, 0], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 0, 0, 0, -1], 18), ([0, 0, 1, 1, -1, 0, -1], 18), ([0, 1, 0, 0, -1, 0, 0], 18), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 1, 1, -1, -1, 0, 0], -18), ([0, 1, 1, 0, -2, 1, -1], 18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 1, -2, 0, -1], -18), ([0, 1, 1, 1, -1, 0, -2], 18), ([0, 1, 2, -1, -1, 0, -1], 18), ([0, 1, 2, 0, -2, 0, -1], 18), ([0, 1, 2, 0, -1, -1, -1], -18), ([0, 1, 2, 0, -1, 0, -2], -18), ([0, 2, 1, 0, -2, 0, -1], -18), ([0, 2, 1, 0, -1, -1, -1], 18), ([1, 0, 1, 0, -1, 0, 0], -18), ([1, 0, 1, 1, -1, 0, -1], 18), ([1, 1, 0, 0, -1, 1, -1], -18), ([1, 1, 0, 0, 0, 0, -1], 18), ([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, 0, -1, -1, 0], 18)]

def combined355_part1 : Sparse := [([1, 1, 1, 0, -1, 1, -2], 18), ([1, 1, 1, 1, -2, 0, -1], -18), ([1, 1, 2, 0, -2, 0, -1], 18), ([1, 1, 2, 0, -1, -1, -1], -18), ([1, 2, 1, -1, -1, 0, -1], 18), ([1, 2, 1, 0, -1, 0, -2], -18)]

def combined355 : Sparse := combined355_part0 ++ combined355_part1

theorem combined355_checked : Certificate.Integer.Sparse.merge combined354 source457 = combined355 := by
  decide +kernel

theorem combined355_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined355 (momentValues f) = 0 := by
  rw [← combined355_checked, Certificate.Integer.Sparse.eval_merge,
    combined354_zero f hcross, source457_zero f hcross, add_zero]

def combined356_part0 : Sparse := [([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 1, -1, 0, -1, 0], -27), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 1, 0, 0, -2, 0], -27), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 1, 1, 1, -1, -1, -1], -27), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 1, 2, 0, -1, -1, -1], 9), ([0, 1, 2, 0, 0, -2, -1], -27), ([0, 2, 0, 0, 0, -1, -1], -18), ([0, 2, 1, 0, 0, -2, -1], 36), ([0, 2, 1, 0, 0, -1, -2], -36), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 2, 0, 0, -1, -1], 36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 1, -1, 0, -1, 0], 9)]

def combined356_part1 : Sparse := [([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, -1, 1, -1, -1], 27), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 0, 0, -2, 0], -27), ([1, 1, 1, 0, 0, 0, -2], 27), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 1, 2, -1, 0, -1, -1], 9), ([1, 1, 2, 0, 0, -1, -2], -27), ([1, 2, 0, 0, 0, -1, -1], -18), ([1, 2, 1, 0, 0, -2, -1], 36)]

def combined356 : Sparse := combined356_part0 ++ combined356_part1

theorem combined356_checked : Certificate.Integer.Sparse.merge source119 source130 = combined356 := by
  decide +kernel

theorem combined356_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined356 (momentValues f) = 0 := by
  rw [← combined356_checked, Certificate.Integer.Sparse.eval_merge,
    source119_zero f hcross, source130_zero f hcross, add_zero]

def combined357_part0 : Sparse := [([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 1, 0, -1, -1], -27), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 0, 1, -1, -1], -27), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 1, -1, 0, -1, 0], -27), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, -1, 0, -1], -27), ([0, 1, 1, 0, 0, -2, 0], -18), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 1, -1, -1, -1], -18), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 1, 2, 0, -1, -1, -1], 9), ([0, 1, 2, 0, 0, -2, -1], -27), ([0, 2, 0, 0, 0, -1, -1], -18), ([0, 2, 1, -1, 0, -1, -1], 9), ([0, 2, 1, 0, -1, -1, -1], -9), ([0, 2, 1, 0, 0, -2, -1], 27), ([0, 2, 1, 0, 0, -1, -2], -27), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 0, 2, 0, 0, -1, -1], 18)]

def combined357_part1 : Sparse := [([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 1, -1, 0, 0, -1], -27), ([1, 1, 1, -1, 1, -1, -1], 18), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 0, 0, -2, 0], -18), ([1, 1, 1, 0, 0, 0, -2], 18), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 1, 1, 1, 0, -2, -1], -9), ([1, 1, 2, -1, 0, -1, -1], 9), ([1, 1, 2, 0, 0, -1, -2], -27), ([1, 2, 0, 0, 0, -1, -1], -18), ([1, 2, 1, 0, -1, -1, -1], -9), ([1, 2, 1, 0, 0, -2, -1], 27)]

def combined357 : Sparse := combined357_part0 ++ combined357_part1

theorem combined357_checked : Certificate.Integer.Sparse.merge combined356 source190 = combined357 := by
  decide +kernel

theorem combined357_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined357 (momentValues f) = 0 := by
  rw [← combined357_checked, Certificate.Integer.Sparse.eval_merge,
    combined356_zero f hcross, source190_zero f hcross, add_zero]

def combined358_part0 : Sparse := [([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 0, 0, 0, 0, -1], 18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 1, -1, 0, -1, 0], -27), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 1, -1, -1, -1], -9), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 18), ([0, 1, 2, -1, 0, -1, -1], 9), ([0, 1, 2, 0, -1, -1, -1], 18), ([0, 1, 2, 0, 0, -2, -1], -27), ([0, 2, 0, 0, 0, -1, -1], -9), ([0, 2, 1, -1, 0, -1, -1], 18), ([0, 2, 1, 0, -1, -1, -1], -18), ([0, 2, 1, 0, 0, -2, -1], 27), ([0, 2, 1, 0, 0, -1, -2], -18), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18)]

def combined358_part1 : Sparse := [([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 2, 0, 0, -1, -1], 9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, -1, 1, -1, -1], 9), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 0, 0, 0, -2], 18), ([1, 1, 1, 0, 1, -1, -2], 18), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 1, 1, 1, 0, -2, -1], -9), ([1, 1, 2, -1, 0, -1, -1], 18), ([1, 1, 2, 0, -1, -1, -1], 9), ([1, 1, 2, 0, 0, -1, -2], -18), ([1, 2, 0, 0, 0, -1, -1], -9), ([1, 2, 1, -1, 0, -1, -1], 9), ([1, 2, 1, 0, -1, -1, -1], -9), ([1, 2, 1, 0, 0, -2, -1], 27)]

def combined358 : Sparse := combined358_part0 ++ combined358_part1

theorem combined358_checked : Certificate.Integer.Sparse.merge combined357 source409 = combined358 := by
  decide +kernel

theorem combined358_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined358 (momentValues f) = 0 := by
  rw [← combined358_checked, Certificate.Integer.Sparse.eval_merge,
    combined357_zero f hcross, source409_zero f hcross, add_zero]

def combined359_part0 : Sparse := [([0, 0, 1, 0, 0, -1, 0], 18), ([0, 0, 1, 1, 0, -1, -1], -18), ([0, 1, 0, 0, 0, -1, 0], -18), ([0, 1, 0, 0, 0, 0, -1], 18), ([0, 1, 0, 0, 1, -1, -1], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 1, -1, 0, -1, 0], -18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 0, -1, 0, -1], -18), ([0, 1, 1, 0, 1, -2, -1], 18), ([0, 1, 1, 1, 0, -2, -1], -18), ([0, 1, 1, 1, 0, -1, -2], 18), ([0, 1, 2, 0, -1, -1, -1], 18), ([0, 1, 2, 0, 0, -2, -1], -18), ([0, 2, 1, -1, 0, -1, -1], 18), ([0, 2, 1, 0, -1, -1, -1], -18), ([0, 2, 1, 0, 0, -2, -1], 18), ([0, 2, 1, 0, 0, -1, -2], -18), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 1, 0, 0, 0, -1, 0], -18), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 1, -1, 0, 0, -1], -18), ([1, 1, 1, 0, -1, -1, 0], 18)]

def combined359_part1 : Sparse := [([1, 1, 1, 0, 1, -1, -2], 18), ([1, 1, 1, 1, 0, -2, -1], -18), ([1, 1, 2, -1, 0, -1, -1], 18), ([1, 1, 2, 0, 0, -1, -2], -18), ([1, 2, 1, 0, -1, -1, -1], -18), ([1, 2, 1, 0, 0, -2, -1], 18)]

def combined359 : Sparse := combined359_part0 ++ combined359_part1

theorem combined359_checked : Certificate.Integer.Sparse.merge combined358 source469 = combined359 := by
  decide +kernel

theorem combined359_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined359 (momentValues f) = 0 := by
  rw [← combined359_checked, Certificate.Integer.Sparse.eval_merge,
    combined358_zero f hcross, source469_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
