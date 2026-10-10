import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merge39

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined320_part0 : Sparse := [([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, -1, 0, 2, -1, -1], 9), ([0, 1, -1, 1, 1, -1, -1], -27), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], -27), ([0, 1, 0, 0, 1, 0, -2], -27), ([0, 1, 0, 0, 2, -1, -2], -27), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 2, 0, 0, 0, -1, -1], -18), ([0, 2, 0, 0, 1, -2, -1], -36), ([0, 2, 0, 0, 1, -1, -2], 36), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 0, 0, 2, -1, -1], 36), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 0, 1, 0, -1], 36)]

def combined320_part1 : Sparse := [([1, 1, -1, 1, 1, -1, -1], -27), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 0, -1, 2, -1, -1], 9), ([1, 1, 0, 0, 1, -2, 0], 27), ([1, 1, 0, 0, 1, 0, -2], -27), ([1, 1, 0, 0, 2, -2, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 1, -1, 1, -1, -1], 27), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], -18), ([1, 2, 0, 0, 1, -1, -2], 36)]

def combined320 : Sparse := combined320_part0 ++ combined320_part1

theorem combined320_checked : Certificate.Integer.Sparse.merge source110 source154 = combined320 := by
  decide +kernel

theorem combined320_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined320 (momentValues f) = 0 := by
  rw [← combined320_checked, Certificate.Integer.Sparse.eval_merge,
    source110_zero f hcross, source154_zero f hcross, add_zero]

def combined321_part0 : Sparse := [([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 0, 1, 0, -1], 27), ([0, 1, -1, 0, 2, -1, -1], 9), ([0, 1, -1, 1, 1, -1, -1], -18), ([0, 1, 0, -1, 1, 0, -1], -27), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 0, 0, 1, 0, -2], -18), ([0, 1, 0, 0, 2, -1, -2], -27), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 2, -1, 0, 1, -1, -1], -9), ([0, 2, 0, -1, 1, -1, -1], 9), ([0, 2, 0, 0, 0, -1, -1], -18), ([0, 2, 0, 0, 1, -2, -1], -27), ([0, 2, 0, 0, 1, -1, -2], 27), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 0, 0, 2, -1, -1], 18), ([1, 0, 1, 0, 1, -1, -1], -27)]

def combined321_part1 : Sparse := [([1, 1, -1, 0, 1, 0, -1], 27), ([1, 1, -1, 1, 1, -1, -1], -18), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 0, -1, 2, -1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 0, 0, 1, -2, 0], 18), ([1, 1, 0, 0, 1, 0, -2], -18), ([1, 1, 0, 0, 2, -2, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 0, 1, 1, -1, -2], -9), ([1, 1, 1, -1, 1, -1, -1], 18), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 2, -1, 0, 1, -1, -1], -9), ([1, 2, 0, 0, 0, -1, -1], -18), ([1, 2, 0, 0, 1, -1, -2], 27)]

def combined321 : Sparse := combined321_part0 ++ combined321_part1

theorem combined321_checked : Certificate.Integer.Sparse.merge combined320 source310 = combined321 := by
  decide +kernel

theorem combined321_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined321 (momentValues f) = 0 := by
  rw [← combined321_checked, Certificate.Integer.Sparse.eval_merge,
    combined320_zero f hcross, source310_zero f hcross, add_zero]

def combined322_part0 : Sparse := [([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 0, 1, 1, -1, -1], -27), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 1, -1, 0, 1, -1, 0], -27), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 0, 2, -1, -1], 9), ([0, 1, -1, 1, 1, -1, -1], -9), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 1, 0, -1, 2, -1, -1], -9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 0, 0, 0, -1], -18), ([0, 1, 0, 0, 1, 0, -2], -18), ([0, 1, 0, 0, 2, -1, -2], -18), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -18), ([0, 1, 1, 0, 0, -1, -1], -27), ([0, 1, 1, 0, 1, -1, -2], 18), ([0, 2, -1, 0, 1, -1, -1], -9), ([0, 2, 0, -1, 1, -1, -1], 9), ([0, 2, 0, 0, 0, -1, -1], -9), ([0, 2, 0, 0, 1, -2, -1], -27), ([0, 2, 0, 0, 1, -1, -2], 18), ([1, 0, 0, 0, 1, -1, 0], 9)]

def combined322_part1 : Sparse := [([1, 0, 0, 0, 2, -1, -1], 9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 1, 0, 1, -1, -1], -27), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 1, -1, -1], -9), ([1, 1, 0, -1, 1, -1, 0], -27), ([1, 1, 0, -1, 2, -1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], -18), ([1, 1, 0, 0, 1, 0, -2], -18), ([1, 1, 0, 0, 2, -2, -1], -27), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 0, 1, 1, -1, -2], -18), ([1, 1, 1, -1, 1, -1, -1], 9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 2, -1, 0, 1, -1, -1], -18), ([1, 2, 0, -1, 1, -1, -1], -9), ([1, 2, 0, 0, 0, -1, -1], -9), ([1, 2, 0, 0, 1, -1, -2], 18)]

def combined322 : Sparse := combined322_part0 ++ combined322_part1

theorem combined322_checked : Certificate.Integer.Sparse.merge combined321 source413 = combined322 := by
  decide +kernel

theorem combined322_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined322 (momentValues f) = 0 := by
  rw [← combined322_checked, Certificate.Integer.Sparse.eval_merge,
    combined321_zero f hcross, source413_zero f hcross, add_zero]

def combined323_part0 : Sparse := [([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 0, 1, 1, -1, -1], -18), ([0, 1, -1, 0, 1, -1, 0], -18), ([0, 1, -1, 0, 1, 0, -1], 18), ([0, 1, -1, 0, 2, -1, -1], 18), ([0, 1, 0, -1, 1, 0, -1], -18), ([0, 1, 0, 0, 0, -1, 0], 18), ([0, 1, 0, 0, 0, 0, -1], -18), ([0, 1, 0, 0, 2, -1, -2], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 0, 1, 1, -2, -1], 18), ([0, 1, 0, 1, 1, -1, -2], -18), ([0, 1, 1, 0, 0, -1, -1], -18), ([0, 1, 1, 0, 1, -1, -2], 18), ([0, 2, -1, 0, 1, -1, -1], -18), ([0, 2, 0, -1, 1, -1, -1], 18), ([0, 2, 0, 0, 1, -2, -1], -18), ([0, 2, 0, 0, 1, -1, -2], 18), ([1, 0, 0, 0, 1, -1, 0], 18), ([1, 0, 1, 0, 1, -1, -1], -18), ([1, 1, -1, 0, 1, 0, -1], 18), ([1, 1, 0, -1, 1, -1, 0], -18), ([1, 1, 0, -1, 2, -1, -1], 18), ([1, 1, 0, 0, 0, 0, -1], -18)]

def combined323_part1 : Sparse := [([1, 1, 0, 0, 2, -2, -1], -18), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 0, 1, 1, -1, -2], -18), ([1, 1, 1, 0, 1, -2, -1], 18), ([1, 2, -1, 0, 1, -1, -1], -18), ([1, 2, 0, 0, 1, -1, -2], 18)]

def combined323 : Sparse := combined323_part0 ++ combined323_part1

theorem combined323_checked : Certificate.Integer.Sparse.merge combined322 source473 = combined323 := by
  decide +kernel

theorem combined323_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined323 (momentValues f) = 0 := by
  rw [← combined323_checked, Certificate.Integer.Sparse.eval_merge,
    combined322_zero f hcross, source473_zero f hcross, add_zero]

def combined324_part0 : Sparse := [([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 0, 1, -2, -1, 1], 9), ([0, 1, 0, 1, -1, -2, 1], 9), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 0, 1, 0, -2, 0], -27), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 0, 2, -1, -2, 0], -27), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -9), ([0, 1, 1, 1, -1, -1, -1], -27), ([0, 2, 0, 0, -1, -1, 0], -18), ([0, 2, 0, 1, -2, -1, 0], -36), ([0, 2, 0, 1, -1, -2, 0], 36), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 2, -1, -1, 0], 36), ([1, 1, -1, 1, -1, -1, 1], 27), ([1, 1, -1, 1, -1, 0, 0], -27)]

def combined324_part1 : Sparse := [([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 2, -1, -1, 0], 9), ([1, 1, 0, 1, -2, -1, 1], 9), ([1, 1, 0, 1, -2, 0, 0], 27), ([1, 1, 0, 1, -1, -2, 1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, 0, -2, 0], -27), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 2, -2, -1, 0], -27), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 1, -2, -1, 0], 9), ([1, 1, 1, 1, -1, -1, -1], -27), ([1, 2, 0, 0, -1, -1, 0], -18), ([1, 2, 0, 1, -1, -2, 0], 36)]

def combined324 : Sparse := combined324_part0 ++ combined324_part1

theorem combined324_checked : Certificate.Integer.Sparse.merge source111 source138 = combined324 := by
  decide +kernel

theorem combined324_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined324 (momentValues f) = 0 := by
  rw [← combined324_checked, Certificate.Integer.Sparse.eval_merge,
    source111_zero f hcross, source138_zero f hcross, add_zero]

def combined325_part0 : Sparse := [([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 1, -1, 1, 0, -1, 0], -27), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 0, 1, -1, -2, 1], 9), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 0, 1, 0, -2, 0], -18), ([0, 1, 0, 1, 0, -1, -1], 27), ([0, 1, 0, 2, -1, -2, 0], -27), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -9), ([0, 1, 1, 1, -1, -1, -1], -18), ([0, 2, -1, 1, -1, -1, 0], 9), ([0, 2, 0, 0, -1, -1, 0], -18), ([0, 2, 0, 1, -2, -1, 0], -27), ([0, 2, 0, 1, -1, -2, 0], 27), ([0, 2, 0, 1, -1, -1, -1], -9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 2, -1, -1, 0], 18)]

def combined325_part1 : Sparse := [([1, 1, -1, 1, -1, -1, 1], 18), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 2, -1, -1, 0], 9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 1, -2, -1, 1], 9), ([1, 1, 0, 1, -2, 0, 0], 18), ([1, 1, 0, 1, 0, -2, 0], -18), ([1, 1, 0, 1, 0, -1, -1], 27), ([1, 1, 0, 2, -2, -1, 0], -27), ([1, 1, 1, 0, -1, -1, 0], 27), ([1, 1, 1, 1, -1, -2, 0], -9), ([1, 1, 1, 1, -1, -1, -1], -18), ([1, 2, 0, 0, -1, -1, 0], -18), ([1, 2, 0, 1, -1, -2, 0], 27), ([1, 2, 0, 1, -1, -1, -1], -9)]

def combined325 : Sparse := combined325_part0 ++ combined325_part1

theorem combined325_checked : Certificate.Integer.Sparse.merge combined324 source246 = combined325 := by
  decide +kernel

theorem combined325_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined325 (momentValues f) = 0 := by
  rw [← combined325_checked, Certificate.Integer.Sparse.eval_merge,
    combined324_zero f hcross, source246_zero f hcross, add_zero]

def combined326_part0 : Sparse := [([0, 0, 0, 1, -1, -1, 1], -9), ([0, 0, 0, 1, 0, -1, 0], 18), ([0, 0, 1, 1, -1, -1, 0], -27), ([0, 1, -1, 1, 0, -1, 0], -18), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 1, 0, 0, -1, -1, 1], -27), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 0, 0, -1, 0], -18), ([0, 1, 0, 1, -1, -2, 1], 18), ([0, 1, 0, 1, -1, 0, -1], -27), ([0, 1, 0, 1, 0, -2, 0], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 0, 2, -1, -2, 0], -18), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], 27), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -18), ([0, 1, 1, 1, -1, -1, -1], -9), ([0, 2, -1, 1, -1, -1, 0], 9), ([0, 2, 0, 0, -1, -1, 0], -9), ([0, 2, 0, 1, -2, -1, 0], -27), ([0, 2, 0, 1, -1, -2, 0], 18), ([0, 2, 0, 1, -1, -1, -1], -9), ([1, 0, 0, 1, -1, -1, 1], -27)]

def combined326_part1 : Sparse := [([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 2, -1, -1, 0], 9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], 9), ([1, 1, -1, 1, -1, 0, 0], -27), ([1, 1, -1, 2, -1, -1, 0], 9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 0, 0, 0, -1, 0], -18), ([1, 1, 0, 1, -2, -1, 1], 9), ([1, 1, 0, 1, 0, -2, 0], -18), ([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 0, 2, -2, -1, 0], -27), ([1, 1, 0, 2, -1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], 18), ([1, 1, 1, 1, -1, -2, 0], -18), ([1, 1, 1, 1, -1, -1, -1], -9), ([1, 2, -1, 1, -1, -1, 0], -9), ([1, 2, 0, 0, -1, -1, 0], -9), ([1, 2, 0, 1, -1, -2, 0], 18), ([1, 2, 0, 1, -1, -1, -1], -18)]

def combined326 : Sparse := combined326_part0 ++ combined326_part1

theorem combined326_checked : Certificate.Integer.Sparse.merge combined325 source339 = combined326 := by
  decide +kernel

theorem combined326_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined326 (momentValues f) = 0 := by
  rw [← combined326_checked, Certificate.Integer.Sparse.eval_merge,
    combined325_zero f hcross, source339_zero f hcross, add_zero]

def combined327_part0 : Sparse := [([0, 0, 0, 1, 0, -1, 0], 18), ([0, 0, 1, 1, -1, -1, 0], -18), ([0, 1, -1, 1, 0, -1, 0], -18), ([0, 1, 0, 0, -1, -1, 1], -18), ([0, 1, 0, 0, -1, 0, 0], 18), ([0, 1, 0, 0, 0, -1, 0], -18), ([0, 1, 0, 1, -1, -2, 1], 18), ([0, 1, 0, 1, -1, 0, -1], -18), ([0, 1, 0, 1, 0, -1, -1], 18), ([0, 1, 0, 2, -1, -2, 0], -18), ([0, 1, 0, 2, -1, -1, -1], 18), ([0, 1, 1, 0, -1, -1, 0], 18), ([0, 1, 1, 1, -2, -1, 0], 18), ([0, 1, 1, 1, -1, -2, 0], -18), ([0, 2, -1, 1, -1, -1, 0], 18), ([0, 2, 0, 1, -2, -1, 0], -18), ([0, 2, 0, 1, -1, -2, 0], 18), ([0, 2, 0, 1, -1, -1, -1], -18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, -1, 0, 0], 18), ([1, 1, -1, 1, -1, 0, 0], -18), ([1, 1, -1, 2, -1, -1, 0], 18), ([1, 1, 0, 0, 0, -1, 0], -18), ([1, 1, 0, 1, -2, -1, 1], 18)]

def combined327_part1 : Sparse := [([1, 1, 0, 1, 0, -1, -1], 18), ([1, 1, 0, 2, -2, -1, 0], -18), ([1, 1, 1, 0, -1, -1, 0], 18), ([1, 1, 1, 1, -1, -2, 0], -18), ([1, 2, 0, 1, -1, -2, 0], 18), ([1, 2, 0, 1, -1, -1, -1], -18)]

def combined327 : Sparse := combined327_part0 ++ combined327_part1

theorem combined327_checked : Certificate.Integer.Sparse.merge combined326 source399 = combined327 := by
  decide +kernel

theorem combined327_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined327 (momentValues f) = 0 := by
  rw [← combined327_checked, Certificate.Integer.Sparse.eval_merge,
    combined326_zero f hcross, source399_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
