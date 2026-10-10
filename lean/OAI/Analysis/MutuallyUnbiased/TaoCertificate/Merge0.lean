import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Rows

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined0_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -36), ([0, -1, -2, 0, 0, 1, 2], 27), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 0, 2], -27), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -36), ([1, -2, 0, 0, 0, 1, 1], 18), ([1, -1, -2, 0, 0, 1, 2], 27), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], 27)]

def combined0_part1 : Sparse := [([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 0, 0, 0, 2], -27), ([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, 0, -2, 0, 0, 1, 1], -36), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9)]

def combined0 : Sparse := combined0_part0 ++ combined0_part1

theorem combined0_checked : Certificate.Integer.Sparse.merge source30 source131 = combined0 := by
  decide +kernel

theorem combined0_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined0 (momentValues f) = 0 := by
  rw [← combined0_checked, Certificate.Integer.Sparse.eval_merge,
    source30_zero f hcross, source131_zero f hcross, add_zero]

def combined1_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -27), ([0, -2, -1, 1, 0, 1, 1], 9), ([0, -1, -2, 0, 0, 1, 2], 27), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, 0, -2, 0, 0, 1, 1], -18), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -27), ([1, -2, -1, 0, 1, 1, 1], 9), ([1, -2, 0, 0, 0, 1, 1], 18)]

def combined1_part1 : Sparse := [([1, -1, -2, 0, 0, 1, 2], 27), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, 0, -2, 0, 0, 1, 1], -18), ([1, 0, -1, 0, -1, 1, 1], 27), ([1, 0, -1, 0, 0, 0, 1], -9)]

def combined1 : Sparse := combined1_part0 ++ combined1_part1

theorem combined1_checked : Certificate.Integer.Sparse.merge combined0 source191 = combined1 := by
  decide +kernel

theorem combined1_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined1 (momentValues f) = 0 := by
  rw [← combined1_checked, Certificate.Integer.Sparse.eval_merge,
    combined0_zero f hcross, source191_zero f hcross, add_zero]

def combined2_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -18), ([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 1, 0, 1, 1], 9), ([0, -1, -2, 0, 0, 1, 2], 18), ([0, -1, -2, 0, 0, 2, 1], -27), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], 18), ([0, -1, -1, 0, -1, 1, 2], -18), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, 0, 0, 1], 18), ([0, 0, -2, 0, 0, 1, 1], -9), ([0, 0, -1, -1, 0, 1, 1], -27), ([0, 0, -1, 0, -1, 1, 1], 27), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], -27)]

def combined2_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], 9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, 0, 0, 0, 1, 1], 9), ([1, -1, -2, 0, 0, 1, 2], 18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 0, 1, 1], -18), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, 0, -1, 1, 2], -18), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, 0, -2, 0, 0, 1, 1], -9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 0, 1], -18)]

def combined2 : Sparse := combined2_part0 ++ combined2_part1

theorem combined2_checked : Certificate.Integer.Sparse.merge combined1 source408 = combined2 := by
  decide +kernel

theorem combined2_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined2 (momentValues f) = 0 := by
  rw [← combined2_checked, Certificate.Integer.Sparse.eval_merge,
    combined1_zero f hcross, source408_zero f hcross, add_zero]

def combined3_part0 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -18), ([0, -2, -1, 1, 0, 1, 1], 18), ([0, -1, -2, 0, 0, 1, 2], 18), ([0, -1, -2, 0, 0, 2, 1], -18), ([0, -1, -2, 0, 1, 1, 1], 18), ([0, -1, -2, 1, 0, 1, 1], -18), ([0, -1, -1, -1, 0, 1, 2], 18), ([0, -1, -1, 0, -1, 1, 2], -18), ([0, -1, -1, 0, -1, 2, 1], 18), ([0, -1, -1, 0, 1, 0, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], 18), ([0, 0, -1, -1, 0, 1, 1], -18), ([0, 0, -1, 0, -1, 1, 1], 18), ([0, 0, -1, 0, 0, 0, 1], -18), ([0, 0, -1, 0, 0, 1, 0], 18), ([1, -2, -1, 0, 0, 2, 1], -18), ([1, -2, -1, 0, 1, 1, 1], 18), ([1, -1, -2, 0, 0, 1, 2], 18), ([1, -1, -2, 1, 0, 1, 1], -18), ([1, -1, -1, -1, 0, 2, 1], 18), ([1, -1, -1, 0, -1, 1, 2], -18)]

def combined3_part1 : Sparse := [([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, 0, 0, 1, 0], 18), ([1, 0, -1, 0, -1, 1, 1], 18), ([1, 0, -1, 0, 0, 0, 1], -18)]

def combined3 : Sparse := combined3_part0 ++ combined3_part1

theorem combined3_checked : Certificate.Integer.Sparse.merge combined2 source468 = combined3 := by
  decide +kernel

theorem combined3_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined3 (momentValues f) = 0 := by
  rw [← combined3_checked, Certificate.Integer.Sparse.eval_merge,
    combined2_zero f hcross, source468_zero f hcross, add_zero]

def combined4_part0 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 36), ([0, -2, -1, 0, 2, 0, 1], -36), ([0, -2, 0, 0, 1, 0, 1], -18), ([0, -1, -2, 0, 1, 0, 2], -27), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, -1, 2, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], -27), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], -27), ([1, -2, -1, 0, 1, 0, 2], 36), ([1, -2, 0, 0, 1, 0, 1], -18), ([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], -27), ([1, -1, -1, -1, 1, 0, 2], 9)]

def combined4_part1 : Sparse := [([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -27), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 0, 2, -1, 1], 9), ([1, -1, -1, 0, 2, 0, 0], 27), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, 0, -2, 0, 1, 0, 1], 36), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, 1, 0, 0], 9)]

def combined4 : Sparse := combined4_part0 ++ combined4_part1

theorem combined4_checked : Certificate.Integer.Sparse.merge source31 source129 = combined4 := by
  decide +kernel

theorem combined4_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined4 (momentValues f) = 0 := by
  rw [← combined4_checked, Certificate.Integer.Sparse.eval_merge,
    source31_zero f hcross, source129_zero f hcross, add_zero]

def combined5_part0 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 27), ([0, -2, -1, 0, 1, 1, 1], 9), ([0, -2, -1, 0, 2, 0, 1], -27), ([0, -2, -1, 1, 1, 0, 1], -9), ([0, -2, 0, 0, 1, 0, 1], -18), ([0, -1, -2, 0, 1, 0, 2], -27), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], -27), ([1, -2, -1, 0, 1, 0, 2], 27), ([1, -2, -1, 1, 1, 0, 1], -9), ([1, -2, 0, 0, 1, 0, 1], -18)]

def combined5_part1 : Sparse := [([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], -27), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, 0, 1], 18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, 1, 0, 0], 9)]

def combined5 : Sparse := combined5_part0 ++ combined5_part1

theorem combined5_checked : Certificate.Integer.Sparse.merge combined4 source189 = combined5 := by
  decide +kernel

theorem combined5_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined5 (momentValues f) = 0 := by
  rw [← combined5_checked, Certificate.Integer.Sparse.eval_merge,
    combined4_zero f hcross, source189_zero f hcross, add_zero]

def combined6_part0 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 18), ([0, -2, -1, 0, 1, 1, 1], 9), ([0, -2, -1, 0, 2, 0, 1], -27), ([0, -2, -1, 1, 1, 0, 1], -9), ([0, -2, 0, 0, 1, 0, 1], -9), ([0, -1, -2, 0, 1, 0, 2], -18), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, -1, 1, 0, 2], 18), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, -1, 2], -18), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -27), ([1, -2, -1, 0, 1, 0, 2], 18)]

def combined6_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -9), ([1, -2, -1, 1, 1, 0, 1], -18), ([1, -2, 0, 0, 1, 0, 1], -9), ([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], -27), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 1, -1, 2], -18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 1, 0, 0], 9)]

def combined6 : Sparse := combined6_part0 ++ combined6_part1

theorem combined6_checked : Certificate.Integer.Sparse.merge combined5 source348 = combined6 := by
  decide +kernel

theorem combined6_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined6 (momentValues f) = 0 := by
  rw [← combined6_checked, Certificate.Integer.Sparse.eval_merge,
    combined5_zero f hcross, source348_zero f hcross, add_zero]

def combined7_part0 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 18), ([0, -2, -1, 0, 1, 1, 1], 18), ([0, -2, -1, 0, 2, 0, 1], -18), ([0, -2, -1, 1, 1, 0, 1], -18), ([0, -1, -2, 0, 1, 0, 2], -18), ([0, -1, -2, 1, 1, 0, 1], 18), ([0, -1, -1, -1, 1, 0, 2], 18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, -1, 2], -18), ([0, -1, -1, 0, 2, -1, 1], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -18), ([1, -2, -1, 0, 1, 0, 2], 18), ([1, -2, -1, 1, 1, 0, 1], -18), ([1, -1, -2, 0, 1, 1, 1], 18), ([1, -1, -2, 0, 2, 0, 1], -18), ([1, -1, -1, -1, 2, 0, 1], 18), ([1, -1, -1, 0, 1, -1, 2], -18)]

def combined7_part1 : Sparse := [([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, 1, 0, 0], 18)]

def combined7 : Sparse := combined7_part0 ++ combined7_part1

theorem combined7_checked : Certificate.Integer.Sparse.merge combined6 source456 = combined7 := by
  decide +kernel

theorem combined7_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined7 (momentValues f) = 0 := by
  rw [← combined7_checked, Certificate.Integer.Sparse.eval_merge,
    combined6_zero f hcross, source456_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
