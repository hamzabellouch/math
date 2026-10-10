import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge3

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined32_part0 : Sparse := [([0, -2, 0, -1, 2, 1, 0], -36), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, 0, -2, 1, 1, 1], 9), ([0, -1, 0, -2, 1, 2, 0], -27), ([0, -1, 0, -2, 2, 1, 0], 27), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, -1, 2, 0, 0], -27), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 1, -2, 1, 1, 0], -9), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, 0, -2, 1, 1, 0], -36), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], 27), ([1, -2, 0, -1, 1, 2, 0], -36), ([1, -2, 0, 0, 1, 1, 0], 18), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, 0, -2, 2, 1, 0], 27)]

def combined32_part1 : Sparse := [([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 0, -1, 0, 2, 0], 27), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 2, -1], -9), ([1, -1, 0, -1, 2, 0, 0], -27), ([1, -1, 0, -1, 2, 1, -1], -9), ([1, -1, 1, -2, 1, 1, 0], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, 0, 0, -2, 1, 1, 0], -36), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27)]

def combined32 : Sparse := combined32_part0 ++ combined32_part1

theorem combined32_checked : Certificate.Integer.Sparse.merge source38 source139 = combined32 := by
  decide +kernel

theorem combined32_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined32 (momentValues f) = 0 := by
  rw [← combined32_checked, Certificate.Integer.Sparse.eval_merge,
    source38_zero f hcross, source139_zero f hcross, add_zero]

def combined33_part0 : Sparse := [([0, -2, 0, -1, 2, 1, 0], -27), ([0, -2, 1, -1, 1, 1, 0], 9), ([0, -1, -1, -1, 2, 1, 0], 9), ([0, -1, 0, -2, 1, 1, 1], 9), ([0, -1, 0, -2, 1, 2, 0], -27), ([0, -1, 0, -2, 2, 1, 0], 27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 2, -1], 9), ([0, -1, 0, -1, 2, 0, 0], -18), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 1, -2, 1, 1, 0], -9), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, 0, -2, 1, 1, 0], -18), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], 27), ([1, -2, 0, -1, 1, 1, 1], 9), ([1, -2, 0, -1, 1, 2, 0], -27), ([1, -2, 0, 0, 1, 1, 0], 18)]

def combined33_part1 : Sparse := [([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 1, 2, 0], 9), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, 0, -2, 2, 1, 0], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, -1, 0, 2, 0], 18), ([1, -1, 0, -1, 2, 0, 0], -18), ([1, -1, 0, -1, 2, 1, -1], -9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 1, -2, 1, 1, 0], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, 0, 0, -2, 1, 1, 0], -18), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27)]

def combined33 : Sparse := combined33_part0 ++ combined33_part1

theorem combined33_checked : Certificate.Integer.Sparse.merge combined32 source247 = combined33 := by
  decide +kernel

theorem combined33_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined33 (momentValues f) = 0 := by
  rw [← combined33_checked, Certificate.Integer.Sparse.eval_merge,
    combined32_zero f hcross, source247_zero f hcross, add_zero]

def combined34_part0 : Sparse := [([0, -2, 0, -1, 1, 1, 1], 9), ([0, -2, 0, -1, 2, 1, 0], -27), ([0, -2, 1, -1, 1, 1, 0], 18), ([0, -1, -1, -1, 2, 1, 0], 9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, 0, -2, 1, 1, 1], 18), ([0, -1, 0, -2, 1, 2, 0], -18), ([0, -1, 0, -2, 2, 1, 0], 27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 2, -1], 18), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 1, -2, 1, 1, 0], -18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, 0, -2, 1, 1, 0], -9), ([0, 0, 0, -1, 0, 1, 0], 18), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], 18), ([1, -2, 0, -1, 1, 1, 1], 18), ([1, -2, 0, -1, 1, 2, 0], -18)]

def combined34_part1 : Sparse := [([1, -2, 0, 0, 1, 1, 0], 9), ([1, -2, 1, -1, 1, 1, 0], 9), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 1, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, 0, -2, 1, 1, 1], 9), ([1, -1, 0, -2, 2, 1, 0], 27), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, -1, 0, 2, 0], 18), ([1, -1, 0, -1, 2, 1, -1], -9), ([1, -1, 0, 0, 0, 1, 0], 18), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 1, -2, 1, 1, 0], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, 0, -2, 1, 1, 0], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], 27)]

def combined34 : Sparse := combined34_part0 ++ combined34_part1

theorem combined34_checked : Certificate.Integer.Sparse.merge combined33 source338 = combined34 := by
  decide +kernel

theorem combined34_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined34 (momentValues f) = 0 := by
  rw [← combined34_checked, Certificate.Integer.Sparse.eval_merge,
    combined33_zero f hcross, source338_zero f hcross, add_zero]

def combined35_part0 : Sparse := [([0, -2, 0, -1, 2, 1, 0], -18), ([0, -2, 1, -1, 1, 1, 0], 18), ([0, -1, -1, -1, 2, 1, 0], 18), ([0, -1, 0, -2, 1, 1, 1], 18), ([0, -1, 0, -2, 1, 2, 0], -18), ([0, -1, 0, -2, 2, 1, 0], 18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 2, -1], 18), ([0, -1, 0, -1, 2, 1, -1], -18), ([0, -1, 0, 0, 1, 0, 0], 18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 1, -2, 1, 1, 0], -18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, -1, 1, 0, 0], 18), ([0, 0, -1, -1, 1, 1, 0], -18), ([0, 0, 0, -1, 0, 1, 0], 18), ([0, 0, 0, -1, 1, 0, 0], -18), ([0, 0, 0, -1, 1, 1, -1], 18), ([1, -2, 0, -1, 1, 1, 1], 18), ([1, -2, 0, -1, 1, 2, 0], -18), ([1, -1, -1, -1, 1, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, 0, -2, 2, 1, 0], 18), ([1, -1, 0, -1, 0, 1, 1], -18)]

def combined35_part1 : Sparse := [([1, -1, 0, -1, 2, 1, -1], -18), ([1, -1, 0, 0, 0, 1, 0], 18), ([1, -1, 1, -2, 1, 1, 0], -18), ([1, -1, 1, -1, 1, 0, 0], 18), ([1, 0, 0, -1, 1, 0, 0], -18), ([1, 0, 0, -1, 1, 1, -1], 18)]

def combined35 : Sparse := combined35_part0 ++ combined35_part1

theorem combined35_checked : Certificate.Integer.Sparse.merge combined34 source398 = combined35 := by
  decide +kernel

theorem combined35_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined35 (momentValues f) = 0 := by
  rw [← combined35_checked, Certificate.Integer.Sparse.eval_merge,
    combined34_zero f hcross, source398_zero f hcross, add_zero]

def combined36_part0 : Sparse := [([0, -2, 0, 0, -1, 2, 1], -36), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, 0, -2, 1, 2], -27), ([0, -1, 0, 0, -2, 2, 1], 27), ([0, -1, 0, 0, -1, 2, 0], -27), ([0, -1, 0, 1, -2, 1, 1], -9), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 1, 0, -2, 1, 1], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -36), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 0, 0, -1, 1, 0], -9), ([1, -2, 0, 0, -1, 1, 2], -36), ([1, -2, 0, 0, 0, 1, 1], 18), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, 0, -1, -1, 2, 1], -9)]

def combined36_part1 : Sparse := [([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 0, 0, -2, 2, 1], 27), ([1, -1, 0, 0, -1, 0, 2], 27), ([1, -1, 0, 0, -1, 2, 0], -27), ([1, -1, 0, 1, -2, 1, 1], -9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, 0, 0, -2, 1, 1], -36), ([1, 0, 0, 0, -1, 1, 0], -9)]

def combined36 : Sparse := combined36_part0 ++ combined36_part1

theorem combined36_checked : Certificate.Integer.Sparse.merge source39 source155 = combined36 := by
  decide +kernel

theorem combined36_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined36 (momentValues f) = 0 := by
  rw [← combined36_checked, Certificate.Integer.Sparse.eval_merge,
    source39_zero f hcross, source155_zero f hcross, add_zero]

def combined37_part0 : Sparse := [([0, -2, 0, 0, -1, 2, 1], -27), ([0, -2, 0, 1, -1, 1, 1], 9), ([0, -1, -1, 0, -1, 1, 2], 9), ([0, -1, -1, 0, -1, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, 0, -1, -1, 2, 1], 9), ([0, -1, 0, 0, -2, 1, 2], -27), ([0, -1, 0, 0, -2, 2, 1], 27), ([0, -1, 0, 0, -1, 2, 0], -18), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -2, 1, 1], -9), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 1, 0, -2, 1, 1], 9), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, 0, -1, -1, 1, 1], -27), ([0, 0, 0, 0, -2, 1, 1], -18), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 0, 0, -1, 1, 0], -9), ([1, -2, 0, 0, -1, 1, 2], -27), ([1, -2, 0, 0, 0, 1, 1], 18), ([1, -2, 1, 0, -1, 1, 1], 9)]

def combined37_part1 : Sparse := [([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, 0, -1, -1, 1, 2], 9), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, 0, -2, 2, 1], 27), ([1, -1, 0, 0, -1, 0, 2], 18), ([1, -1, 0, 0, -1, 2, 0], -18), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 1, -2, 1, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 1, -1, -1, 1, 1], 18), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, 0, 0, -2, 1, 1], -18), ([1, 0, 0, 0, -1, 1, 0], -9)]

def combined37 : Sparse := combined37_part0 ++ combined37_part1

theorem combined37_checked : Certificate.Integer.Sparse.merge combined36 source311 = combined37 := by
  decide +kernel

theorem combined37_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined37 (momentValues f) = 0 := by
  rw [← combined37_checked, Certificate.Integer.Sparse.eval_merge,
    combined36_zero f hcross, source311_zero f hcross, add_zero]

def combined38_part0 : Sparse := [([0, -2, 0, 0, -1, 2, 1], -27), ([0, -2, 0, 1, -1, 1, 1], 18), ([0, -2, 1, 0, -1, 1, 1], 9), ([0, -1, -1, 0, -1, 1, 2], 18), ([0, -1, -1, 0, -1, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, 0, -1, -1, 2, 1], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, 0, -2, 1, 2], -18), ([0, -1, 0, 0, -2, 2, 1], 27), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -2, 1, 1], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 1, 0, -2, 1, 1], 18), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, 0, -2, 1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 0, 0, -1, 1, 0], -9), ([1, -2, 0, 0, -1, 1, 2], -18), ([1, -2, 0, 0, 0, 1, 1], 9)]

def combined38_part1 : Sparse := [([1, -2, 0, 1, -1, 1, 1], 9), ([1, -2, 1, 0, -1, 1, 1], 18), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, 0, -1, -1, 1, 2], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, 0, -2, 2, 1], 27), ([1, -1, 0, 0, -1, 0, 2], 18), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, -2, 1, 1], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 1, -1, -1, 1, 1], 9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, 0, -2, 1, 1], -9), ([1, 0, 0, 0, -1, 1, 0], -9)]

def combined38 : Sparse := combined38_part0 ++ combined38_part1

theorem combined38_checked : Certificate.Integer.Sparse.merge combined37 source412 = combined38 := by
  decide +kernel

theorem combined38_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined38 (momentValues f) = 0 := by
  rw [← combined38_checked, Certificate.Integer.Sparse.eval_merge,
    combined37_zero f hcross, source412_zero f hcross, add_zero]

def combined39_part0 : Sparse := [([0, -2, 0, 0, -1, 2, 1], -18), ([0, -2, 0, 1, -1, 1, 1], 18), ([0, -1, -1, 0, -1, 1, 2], 18), ([0, -1, -1, 0, -1, 2, 1], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, 0, -1, -1, 2, 1], 18), ([0, -1, 0, 0, -2, 1, 2], -18), ([0, -1, 0, 0, -2, 2, 1], 18), ([0, -1, 0, 0, 0, 1, 0], 18), ([0, -1, 0, 1, -2, 1, 1], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 1, 0, -2, 1, 1], 18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, 0, -1, -1, 1, 1], -18), ([0, 0, 0, 0, -1, 0, 1], 18), ([0, 0, 0, 0, -1, 1, 0], -18), ([1, -2, 0, 0, -1, 1, 2], -18), ([1, -2, 1, 0, -1, 1, 1], 18), ([1, -1, -1, 0, -1, 2, 1], -18), ([1, -1, 0, -1, -1, 1, 2], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, 0, -2, 2, 1], 18)]

def combined39_part1 : Sparse := [([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 0, 1, -2, 1, 1], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, 0, 0, -1, 1, 0], -18)]

def combined39 : Sparse := combined39_part0 ++ combined39_part1

theorem combined39_checked : Certificate.Integer.Sparse.merge combined38 source472 = combined39 := by
  decide +kernel

theorem combined39_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined39 (momentValues f) = 0 := by
  rw [← combined39_checked, Certificate.Integer.Sparse.eval_merge,
    combined38_zero f hcross, source472_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
