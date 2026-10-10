import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source184 : Sparse := [([0, 1, 0, -1, 0, 0, 0], -9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 1, -2, 0, 1, -1], -9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, -1, 1, 0, -2], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 2, 1, -2, 0, 0, -1], 9), ([0, 2, 1, -1, -1, 0, -1], -9), ([0, 2, 1, -1, 0, -1, -1], -9), ([0, 2, 1, -1, 0, 0, -2], 9), ([1, 0, 2, -1, 0, 0, -1], -18), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -2, 1, 0, -1], -9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 0, 1, -2], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 2, 1, -1, -1, 0, -1], -9), ([1, 2, 1, -1, 0, -1, -1], -9)]

theorem source184_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![1, -1, 0, 0, 0, 0] (0, -3)) = source184 := by
  decide +kernel

theorem source184_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source184 (momentValues f) = 0 := by
  rw [← source184_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source185 : Sparse := [([0, -2, -1, 1, 0, 0, 2], 9), ([0, -2, -1, 2, 0, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 1, -1, 0, 2], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, -1, 2], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, 0, -2, 1, 0, 0, 1], 18), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], 18)]

theorem source185_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source185 := by
  decide +kernel

theorem source185_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source185 (momentValues f) = 0 := by
  rw [← source185_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source186 : Sparse := [([0, 0, 2, 0, -1, -1, 0], 18), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, 0, -2, -1, 1], 9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -1, -2, 1], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 1, 1, -2, -1, 0], -9), ([0, 1, 1, 1, -1, -2, 0], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, 1, 0, -2, -1, 0], 9), ([0, 2, 1, 0, -1, -2, 0], 9), ([1, 0, 2, 0, -1, -1, 0], 18), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, 0, -2, -1, 1], 9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 1, -1, -2, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, 1, -1, -1, -1, 0], 9), ([1, 2, 1, 0, -1, -1, -1], 9)]

theorem source186_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![1, -1, 0, 0, 0, 0] (3, 3)) = source186 := by
  decide +kernel

theorem source186_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source186 (momentValues f) = 0 := by
  rw [← source186_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source187 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 0, 1, 2, 0], 9), ([0, -2, -1, 0, 2, 1, 0], 9), ([0, -2, -1, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], 9), ([1, -2, -1, 0, 1, 1, 1], -9), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, 0, -2, 0, 1, 1, 0], -18)]

theorem source187_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source187 := by
  decide +kernel

theorem source187_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source187 (momentValues f) = 0 := by
  rw [← source187_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source188 : Sparse := [([0, 0, 2, 0, -1, 0, -1], 18), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -2, 1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, -1, 1, -2], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -2, 0, -1], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, -1, 0, -2], 9), ([0, 2, 1, 0, -2, 0, -1], 9), ([0, 2, 1, 0, -1, -1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], 18), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -2, 1, -1], 9), ([1, 1, 1, 0, -1, 1, -2], 9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], 9), ([1, 2, 1, -1, -1, 0, -1], 9), ([1, 2, 1, 0, -1, 0, -2], 9)]

theorem source188_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![1, -1, 0, 0, 0, 0] (3, 3)) = source188 := by
  decide +kernel

theorem source188_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source188 (momentValues f) = 0 := by
  rw [← source188_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source189 : Sparse := [([0, -2, -1, 0, 1, 0, 2], -9), ([0, -2, -1, 0, 1, 1, 1], 9), ([0, -2, -1, 0, 2, 0, 1], 9), ([0, -2, -1, 1, 1, 0, 1], -9), ([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([1, -2, -1, 0, 1, 0, 2], -9), ([1, -2, -1, 1, 1, 0, 1], -9), ([1, -1, -1, -1, 1, 0, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 2, -1, 1], -9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], -18)]

theorem source189_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source189 := by
  decide +kernel

theorem source189_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source189 (momentValues f) = 0 := by
  rw [← source189_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source190 : Sparse := [([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 1, 0, 1, -1, -2], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, 1, -1, 0, -1, -1], 9), ([0, 2, 1, 0, -1, -1, -1], -9), ([0, 2, 1, 0, 0, -2, -1], -9), ([0, 2, 1, 0, 0, -1, -2], 9), ([1, 0, 2, 0, 0, -1, -1], -18), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 1, 0, 1, -2, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -2, -1], -9), ([1, 1, 1, 1, 0, -1, -2], -9), ([1, 2, 1, 0, -1, -1, -1], -9), ([1, 2, 1, 0, 0, -2, -1], -9)]

theorem source190_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![1, -1, 0, 0, 0, 0] (0, -3)) = source190 := by
  decide +kernel

theorem source190_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source190 (momentValues f) = 0 := by
  rw [← source190_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source191 : Sparse := [([0, -2, -1, 0, 0, 1, 2], 9), ([0, -2, -1, 1, 0, 1, 1], 9), ([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, 0, -2, 0, 0, 1, 1], 18), ([1, -2, -1, 0, 0, 2, 1], 9), ([1, -2, -1, 0, 1, 1, 1], 9), ([1, -1, -1, -1, 0, 1, 2], 9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, 0, -2, 0, 0, 1, 1], 18)]

theorem source191_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source191 := by
  decide +kernel

theorem source191_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source191 (momentValues f) = 0 := by
  rw [← source191_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
