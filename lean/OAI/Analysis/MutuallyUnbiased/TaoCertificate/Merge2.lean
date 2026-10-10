import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge1

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined16_part0 : Sparse := [([0, -2, -1, 1, 0, 2, 0], -36), ([0, -2, -1, 2, 0, 1, 0], 36), ([0, -2, 0, 1, 0, 1, 0], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 2, 0, 1, 0], -27), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([1, -2, -1, 2, 0, 1, 0], 36), ([1, -2, 0, 1, 0, 1, 0], -18), ([1, -1, -2, 1, 0, 2, 0], -27), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 0, 1, 1], 9)]

def combined16_part1 : Sparse := [([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, 0, -2, 1, 0, 1, 0], 36), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -27)]

def combined16 : Sparse := combined16_part0 ++ combined16_part1

theorem combined16_checked : Certificate.Integer.Sparse.merge source34 source123 = combined16 := by
  decide +kernel

theorem combined16_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined16 (momentValues f) = 0 := by
  rw [← combined16_checked, Certificate.Integer.Sparse.eval_merge,
    source34_zero f hcross, source123_zero f hcross, add_zero]

def combined17_part0 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 0, 2, 0], -27), ([0, -2, -1, 1, 1, 1, 0], 9), ([0, -2, -1, 2, 0, 1, 0], 27), ([0, -2, 0, 1, 0, 1, 0], -18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 2, 0, 1, 0], -27), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 0, 0], -18), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, -1, 1, 0, 0, 0], 9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, -1, 2, 0, 1, 0], 27), ([1, -2, 0, 1, 0, 1, 0], -18)]

def combined17_part1 : Sparse := [([1, -1, -2, 1, 0, 2, 0], -27), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, -1, 2, 0, 0, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, 0, -2, 1, 0, 1, 0], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -27)]

def combined17 : Sparse := combined17_part0 ++ combined17_part1

theorem combined17_checked : Certificate.Integer.Sparse.merge combined16 source183 = combined17 := by
  decide +kernel

theorem combined17_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined17 (momentValues f) = 0 := by
  rw [← combined17_checked, Certificate.Integer.Sparse.eval_merge,
    combined16_zero f hcross, source183_zero f hcross, add_zero]

def combined18_part0 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -18), ([0, -2, -1, 1, 0, 2, 0], -18), ([0, -2, -1, 1, 1, 1, 0], 18), ([0, -2, -1, 2, 0, 1, 0], 27), ([0, -2, 0, 1, 0, 1, 0], -9), ([0, -1, -2, 1, 0, 1, 1], 18), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 2, 0, 1, 0], -27), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, -1, 2, 0], 18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 1, 0], 18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, -1, 1, 1, 1, 0], 9)]

def combined18_part1 : Sparse := [([1, -2, -1, 2, 0, 1, 0], 27), ([1, -2, 0, 1, 0, 1, 0], -9), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 0, 2, 0], -18), ([1, -1, -2, 1, 1, 1, 0], 18), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 2, -1], 18), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, 0, -2, 1, 0, 1, 0], 9), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], -18)]

def combined18 : Sparse := combined18_part0 ++ combined18_part1

theorem combined18_checked : Certificate.Integer.Sparse.merge combined17 source276 = combined18 := by
  decide +kernel

theorem combined18_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined18 (momentValues f) = 0 := by
  rw [← combined18_checked, Certificate.Integer.Sparse.eval_merge,
    combined17_zero f hcross, source276_zero f hcross, add_zero]

def combined19_part0 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -18), ([0, -2, -1, 1, 0, 2, 0], -18), ([0, -2, -1, 1, 1, 1, 0], 18), ([0, -2, -1, 2, 0, 1, 0], 18), ([0, -1, -2, 1, 0, 1, 1], 18), ([0, -1, -2, 2, 0, 1, 0], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 1, -1, 2, 0], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, -1, 2, -1, 1, 0], -18), ([0, -1, -1, 2, 0, 1, -1], 18), ([0, -1, 0, 0, 0, 1, 0], 18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, 0, 0, 0], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, -1, 1, 0, 0, 0], 18), ([1, -2, -1, 1, 0, 1, 1], -18), ([1, -2, -1, 2, 0, 1, 0], 18), ([1, -1, -2, 1, 0, 2, 0], -18), ([1, -1, -2, 1, 1, 1, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18)]

def combined19_part1 : Sparse := [([1, -1, -1, 1, 0, 2, -1], 18), ([1, -1, -1, 2, -1, 1, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 1, 0, 0, 0], -18), ([1, 0, -1, 0, 0, 1, 0], 18), ([1, 0, -1, 1, 0, 1, -1], -18)]

def combined19 : Sparse := combined19_part0 ++ combined19_part1

theorem combined19_checked : Certificate.Integer.Sparse.merge combined18 source384 = combined19 := by
  decide +kernel

theorem combined19_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined19 (momentValues f) = 0 := by
  rw [← combined19_checked, Certificate.Integer.Sparse.eval_merge,
    combined18_zero f hcross, source384_zero f hcross, add_zero]

def combined20_part0 : Sparse := [([0, -2, -1, 2, 1, 0, 0], -36), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 2, 0, 0], -27), ([0, -1, -2, 2, 1, 0, 0], 27), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 2, 0, -1], -9), ([0, -1, -1, 2, 0, 0, 0], -27), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, 0, -2, 1, 1, 0, 0], -36), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 1, 0, -1], -27), ([1, -2, -1, 1, 2, 0, 0], -36), ([1, -2, 0, 1, 1, 0, 0], 18), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 2, 1, 0, 0], 27), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 1, 1, 0], -36)]

def combined20_part1 : Sparse := [([1, -1, -1, 0, 2, 0, 0], 27), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, -1, 2, 0, 0, 0], -27), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, 0, -2, 1, 1, 0, 0], -36), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], 27)]

def combined20 : Sparse := combined20_part0 ++ combined20_part1

theorem combined20_checked : Certificate.Integer.Sparse.merge source35 source121 = combined20 := by
  decide +kernel

theorem combined20_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined20 (momentValues f) = 0 := by
  rw [← combined20_checked, Certificate.Integer.Sparse.eval_merge,
    source35_zero f hcross, source121_zero f hcross, add_zero]

def combined21_part0 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, -1, 2, 1, 0, 0], -27), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 2, 0, 0], -27), ([0, -1, -2, 2, 1, 0, 0], 27), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 2, 0, 0, 0], -18), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, 0, -2, 1, 1, 0, 0], -18), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, -1, 1, 1, 0, -1], -27), ([1, -2, -1, 1, 1, 1, 0], 9), ([1, -2, -1, 1, 2, 0, 0], -27), ([1, -2, 0, 1, 1, 0, 0], 18)]

def combined21_part1 : Sparse := [([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 2, 1, 0, 0], 27), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, -1, 1, 2, 0, -1], 9), ([1, -1, -1, 2, 0, 0, 0], -18), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, 0, -2, 1, 1, 0, 0], -18), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], 27)]

def combined21 : Sparse := combined21_part0 ++ combined21_part1

theorem combined21_checked : Certificate.Integer.Sparse.merge combined20 source181 = combined21 := by
  decide +kernel

theorem combined21_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined21 (momentValues f) = 0 := by
  rw [← combined21_checked, Certificate.Integer.Sparse.eval_merge,
    combined20_zero f hcross, source181_zero f hcross, add_zero]

def combined22_part0 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 18), ([0, -2, -1, 1, 1, 1, 0], 9), ([0, -2, -1, 2, 1, 0, 0], -27), ([0, -1, -2, 1, 1, 0, 1], -18), ([0, -1, -2, 1, 1, 1, 0], 18), ([0, -1, -2, 1, 2, 0, 0], -18), ([0, -1, -2, 2, 1, 0, 0], 27), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 2, -1, 0], 18), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, 0, -2, 1, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 1, 1, 0, -1], -18), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -2, -1, 1, 1, 1, 0], 18)]

def combined22_part1 : Sparse := [([1, -2, -1, 1, 2, 0, 0], -18), ([1, -2, 0, 1, 1, 0, 0], 9), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -2, 2, 1, 0, 0], 27), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 1, 2, 0, -1], 18), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], 18), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, 0, -2, 1, 1, 0, 0], -9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, -1, 1, 1, 0, -1], 9)]

def combined22 : Sparse := combined22_part0 ++ combined22_part1

theorem combined22_checked : Certificate.Integer.Sparse.merge combined21 source264 = combined22 := by
  decide +kernel

theorem combined22_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined22 (momentValues f) = 0 := by
  rw [← combined22_checked, Certificate.Integer.Sparse.eval_merge,
    combined21_zero f hcross, source264_zero f hcross, add_zero]

def combined23_part0 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 18), ([0, -2, -1, 2, 1, 0, 0], -18), ([0, -1, -2, 1, 1, 0, 1], -18), ([0, -1, -2, 1, 1, 1, 0], 18), ([0, -1, -2, 1, 2, 0, 0], -18), ([0, -1, -2, 2, 1, 0, 0], 18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 2, -1, 0], 18), ([0, -1, -1, 2, 1, -1, 0], -18), ([0, -1, -1, 2, 1, 0, -1], 18), ([0, -1, 0, 1, 0, 0, 0], 18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, 0, -1, 0, 1, 0, 0], 18), ([0, 0, -1, 1, 0, 0, 0], -18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, -1, 1, 1, 0, -1], -18), ([1, -2, -1, 1, 1, 1, 0], 18), ([1, -2, -1, 1, 2, 0, 0], -18), ([1, -1, -2, 1, 1, 0, 1], -18), ([1, -1, -2, 2, 1, 0, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18)]

def combined23_part1 : Sparse := [([1, -1, -1, 1, 2, 0, -1], 18), ([1, -1, -1, 2, 1, -1, 0], -18), ([1, -1, 0, 0, 1, 0, 0], 18), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, 0, -1, 1, 0, 0, 0], -18), ([1, 0, -1, 1, 1, -1, 0], 18)]

def combined23 : Sparse := combined23_part0 ++ combined23_part1

theorem combined23_checked : Certificate.Integer.Sparse.merge combined22 source324 = combined23 := by
  decide +kernel

theorem combined23_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined23 (momentValues f) = 0 := by
  rw [← combined23_checked, Certificate.Integer.Sparse.eval_merge,
    combined22_zero f hcross, source324_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
