import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge0

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined8_part0 : Sparse := [([0, -2, -1, 0, 1, 2, 0], -36), ([0, -2, -1, 0, 2, 1, 0], -36), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 1, 2, 0], -27), ([0, -1, -2, 0, 2, 1, 0], -27), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27), ([1, -2, 0, 0, 1, 1, 0], 18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 1, 1], -9)]

def combined8_part1 : Sparse := [([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 0, 2, 0, 0], 27), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, 0, -2, 0, 1, 1, 0], 36), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9)]

def combined8 : Sparse := combined8_part0 ++ combined8_part1

theorem combined8_checked : Certificate.Integer.Sparse.merge source32 source127 = combined8 := by
  decide +kernel

theorem combined8_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined8 (momentValues f) = 0 := by
  rw [← combined8_checked, Certificate.Integer.Sparse.eval_merge,
    source32_zero f hcross, source127_zero f hcross, add_zero]

def combined9_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 0, 1, 2, 0], -27), ([0, -2, -1, 0, 2, 1, 0], -27), ([0, -2, -1, 1, 1, 1, 0], -9), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 1, 2, 0], -27), ([0, -1, -2, 0, 2, 1, 0], -27), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27)]

def combined9_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -9), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -2, 0, 0, 1, 1, 0], 18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9)]

def combined9 : Sparse := combined9_part0 ++ combined9_part1

theorem combined9_checked : Certificate.Integer.Sparse.merge combined8 source187 = combined9 := by
  decide +kernel

theorem combined9_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined9 (momentValues f) = 0 := by
  rw [← combined9_checked, Certificate.Integer.Sparse.eval_merge,
    combined8_zero f hcross, source187_zero f hcross, add_zero]

def combined10_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 0, 1, 2, 0], -18), ([0, -2, -1, 0, 2, 1, 0], -27), ([0, -2, -1, 1, 1, 1, 0], -18), ([0, -1, -2, 0, 1, 1, 1], -18), ([0, -1, -2, 0, 1, 2, 0], -18), ([0, -1, -2, 0, 2, 1, 0], -27), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -18), ([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 0, 1, 2, -1], -18), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -18)]

def combined10_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -18), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -2, 0, 0, 1, 1, 0], 9), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 1, 2, 0], -18), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 2, -1], -18), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, 0, -2, 0, 1, 1, 0], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 1, 1, -1], 9)]

def combined10 : Sparse := combined10_part0 ++ combined10_part1

theorem combined10_checked : Certificate.Integer.Sparse.merge combined9 source336 = combined10 := by
  decide +kernel

theorem combined10_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined10 (momentValues f) = 0 := by
  rw [← combined10_checked, Certificate.Integer.Sparse.eval_merge,
    combined9_zero f hcross, source336_zero f hcross, add_zero]

def combined11_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -18), ([0, -2, -1, 0, 1, 2, 0], -18), ([0, -2, -1, 0, 2, 1, 0], -18), ([0, -2, -1, 1, 1, 1, 0], -18), ([0, -1, -2, 0, 1, 1, 1], -18), ([0, -1, -2, 0, 1, 2, 0], -18), ([0, -1, -2, 0, 2, 1, 0], -18), ([0, -1, -2, 1, 1, 1, 0], -18), ([0, -1, -1, -1, 1, 2, 0], -18), ([0, -1, -1, -1, 2, 1, 0], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 0, 1, 2, -1], -18), ([0, -1, -1, 0, 2, 1, -1], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 0, 1, 0, 0], -18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, -1, 0, 0, 1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], -18), ([0, 0, -1, 0, 1, 1, -1], -18)]

def combined11_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -18), ([1, -2, -1, 1, 1, 1, 0], -18), ([1, -1, -2, 0, 1, 1, 1], -18), ([1, -1, -2, 1, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 2, 0], -18), ([1, -1, -1, -1, 2, 1, 0], -18), ([1, -1, -1, 0, 1, 2, -1], -18), ([1, -1, -1, 0, 2, 1, -1], -18), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], -18), ([1, 0, -1, 0, 0, 1, 0], -18), ([1, 0, -1, 0, 1, 0, 0], -18)]

def combined11 : Sparse := combined11_part0 ++ combined11_part1

theorem combined11_checked : Certificate.Integer.Sparse.merge combined10 source396 = combined11 := by
  decide +kernel

theorem combined11_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined11 (momentValues f) = 0 := by
  rw [← combined11_checked, Certificate.Integer.Sparse.eval_merge,
    combined10_zero f hcross, source396_zero f hcross, add_zero]

def combined12_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -36), ([0, -2, -1, 2, 0, 0, 1], -36), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -27), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -27), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, 0, -2, 1, 0, 0, 1], -36), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -1, -2, 1, 0, 1, 1], 9)]

def combined12_part1 : Sparse := [([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -27), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, 0, -2, 1, 0, 0, 1], -36), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined12 : Sparse := combined12_part0 ++ combined12_part1

theorem combined12_checked : Certificate.Integer.Sparse.merge source33 source125 = combined12 := by
  decide +kernel

theorem combined12_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined12 (momentValues f) = 0 := by
  rw [← combined12_checked, Certificate.Integer.Sparse.eval_merge,
    source33_zero f hcross, source125_zero f hcross, add_zero]

def combined13_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -27), ([0, -2, -1, 2, 0, 0, 1], -27), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -27), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, 0, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, 0, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -27), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18)]

def combined13_part1 : Sparse := [([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], -18), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], -18), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined13 : Sparse := combined13_part0 ++ combined13_part1

theorem combined13_checked : Certificate.Integer.Sparse.merge combined12 source185 = combined13 := by
  decide +kernel

theorem combined13_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined13 (momentValues f) = 0 := by
  rw [← combined13_checked, Certificate.Integer.Sparse.eval_merge,
    combined12_zero f hcross, source185_zero f hcross, add_zero]

def combined14_part0 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -18), ([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, -1, 2, 0, 0, 1], -27), ([0, -2, 0, 1, 0, 0, 1], -9), ([0, -1, -2, 1, 0, 0, 2], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 2, 0, 0, 1], -27), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, 0, -2, 1, 0, 0, 1], -9), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, -1, 1, 0, -1, 1], -18), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 18), ([1, -2, 0, 1, 0, 0, 1], -9)]

def combined14_part1 : Sparse := [([1, -1, -2, 1, 0, 1, 1], 18), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 1, -1, 0, 2], 18), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], 18), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], -9), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def combined14 : Sparse := combined14_part0 ++ combined14_part1

theorem combined14_checked : Certificate.Integer.Sparse.merge combined13 source288 = combined14 := by
  decide +kernel

theorem combined14_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined14 (momentValues f) = 0 := by
  rw [← combined14_checked, Certificate.Integer.Sparse.eval_merge,
    combined13_zero f hcross, source288_zero f hcross, add_zero]

def combined15 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -18), ([0, -2, -1, 2, 0, 0, 1], -18), ([0, -1, -2, 1, 0, 0, 2], -18), ([0, -1, -2, 2, 0, 0, 1], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([1, -2, -1, 1, 0, 1, 1], 18), ([1, -2, -1, 1, 1, 0, 1], 18), ([1, -1, -2, 1, 0, 1, 1], 18), ([1, -1, -2, 1, 1, 0, 1], 18), ([1, -1, -1, 1, -1, 0, 2], 18), ([1, -1, -1, 1, 0, -1, 2], 18), ([1, -1, -1, 2, -1, 0, 1], 18), ([1, -1, -1, 2, 0, -1, 1], 18), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, 0, 0, 0], 18), ([1, 0, -1, 0, 0, 0, 1], 18), ([1, 0, -1, 1, 0, 0, 0], 18)]

theorem combined15_checked : Certificate.Integer.Sparse.merge combined14 source444 = combined15 := by
  decide +kernel

theorem combined15_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined15 (momentValues f) = 0 := by
  rw [← combined15_checked, Certificate.Integer.Sparse.eval_merge,
    combined14_zero f hcross, source444_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
