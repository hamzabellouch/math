import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source360 : Sparse := [([0, 0, -1, -1, 0, 2, 0], 18), ([0, 1, -2, -1, 0, 1, 1], -9), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -1, -2, 0, 1, 1], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 2, -2, -1, 0, 1, 0], 9), ([0, 2, -1, -2, 0, 1, 0], 9), ([1, 0, -1, -1, 0, 2, 0], 18), ([1, 1, -2, -1, 1, 1, 0], 9), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -1, -2, 0, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 2, -1, -1, -1, 1, 0], 9), ([1, 2, -1, -1, 0, 1, -1], 9)]

theorem source360_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![1, 0, 0, 0, -1, 0] (3, 3)) = source360 := by
  decide +kernel

theorem source360_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source360 (momentValues f) = 0 := by
  rw [← source360_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source361 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -9), ([0, -2, 1, 1, 1, -1, 0], -9), ([0, -2, 1, 2, 0, -1, 0], 9), ([0, -2, 2, 1, 0, -1, 0], 9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 2, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -1, -1], -9), ([1, -2, 1, 1, 0, -1, 1], -9), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, -1, 2, 1, -1, -1, 0], -9), ([1, 0, 1, 1, 0, -2, 0], -18)]

theorem source361_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source361 := by
  decide +kernel

theorem source361_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source361 (momentValues f) = 0 := by
  rw [← source361_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source362 : Sparse := [([0, 0, -1, 0, -1, 2, 0], 18), ([0, 1, -2, 0, -1, 1, 1], -9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -2, 1, -1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 1, -2, 1, 0], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 2, -2, 0, -1, 1, 0], 9), ([0, 2, -1, -1, -1, 1, 0], 9), ([1, 0, -1, 0, -1, 2, 0], 18), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -2, 1, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -2, 1, 1], 9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -2, 1, 0], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 2, -1, 0, -2, 1, 0], 9), ([1, 2, -1, 0, -1, 1, -1], 9)]

theorem source362_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![1, 0, 0, 0, -1, 0] (3, 3)) = source362 := by
  decide +kernel

theorem source362_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source362 (momentValues f) = 0 := by
  rw [← source362_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source363 : Sparse := [([0, -2, 1, 0, 1, -1, 1], -9), ([0, -2, 1, 0, 2, -1, 0], -9), ([0, -2, 1, 1, 1, -1, 0], 9), ([0, -2, 2, 0, 1, -1, 0], 9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 2, 0, 1, -1, -1], -9), ([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 1, 0, 2, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 2, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 2, -1, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, -1, 1, -1, 0], -9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, 0, 1, 0, 1, -2, 0], -18)]

theorem source363_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source363 := by
  decide +kernel

theorem source363_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source363 (momentValues f) = 0 := by
  rw [← source363_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source364 : Sparse := [([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 0, 1, -2], -9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 2, -2, 0, 0, 1, -1], -9), ([0, 2, -1, -1, 0, 1, -1], -9), ([0, 2, -1, 0, -1, 1, -1], 9), ([0, 2, -1, 0, 0, 1, -2], 9), ([1, 0, -1, 0, 0, 2, -1], -18), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -2, 0, 1, 1, -1], -9), ([1, 1, -2, 1, 0, 1, -1], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 1, -2], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 2, -2, 0, 0, 1, -1], -9), ([1, 2, -1, -1, 0, 1, -1], -9)]

theorem source364_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![1, 0, 0, 0, -1, 0] (0, -3)) = source364 := by
  decide +kernel

theorem source364_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source364 (momentValues f) = 0 := by
  rw [← source364_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source365 : Sparse := [([0, -2, 1, 0, 0, -1, 2], 9), ([0, -2, 1, 0, 1, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 1, -1, 0, -1, 2], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, -1, -1, 2], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 2, -1, 0, -1, 1], 9), ([0, -1, 2, 0, -1, -1, 1], 9), ([0, 0, 1, 0, 0, -2, 1], 18), ([1, -2, 1, 1, 0, -1, 1], 9), ([1, -2, 2, 0, 0, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, -1, -1, 2], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 2, -1, 0, -1, 1], 9), ([1, -1, 2, 0, -1, -1, 1], 9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, 0, 1, 0, 0, -2, 1], 18)]

theorem source365_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source365 := by
  decide +kernel

theorem source365_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source365 (momentValues f) = 0 := by
  rw [← source365_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source366 : Sparse := [([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 1, -1, -2, 1, 0], -9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 2, -1, -1, -1, 1, 0], -9), ([0, 2, 0, -2, -1, 1, 0], -9), ([0, 2, 0, -1, -2, 1, 0], 9), ([0, 2, 0, -1, -1, 1, -1], 9), ([1, 0, 0, -1, -1, 2, 0], -18), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, 0, -2, -1, 1, 1], -9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -1, -2, 1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 1, 1, -2, -1, 1, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, -1, -1, -1, 1, 0], -9), ([1, 2, 0, -2, -1, 1, 0], -9)]

theorem source366_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![1, 0, 0, 0, -1, 0] (0, -3)) = source366 := by
  decide +kernel

theorem source366_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source366 (momentValues f) = 0 := by
  rw [← source366_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source367 : Sparse := [([0, -2, 0, 1, 1, -1, 1], 9), ([0, -2, 0, 1, 2, -1, 0], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 1, 2, -1, 0], -9), ([0, -1, -1, 2, 1, -1, 0], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 0, 1, 2, -1, -1], 9), ([0, -1, 0, 2, 1, -1, -1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 1, -2, 0], 18), ([1, -2, 0, 2, 1, -1, 0], 9), ([1, -2, 1, 1, 1, -1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 1, -1, 0], 9), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 1, 2, -1, -1], 9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 0, 2, 1, -1, -1], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, 0, 1, 1, -2, 0], 18)]

theorem source367_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source367 := by
  decide +kernel

theorem source367_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source367 (momentValues f) = 0 := by
  rw [← source367_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
