import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source288 : Sparse := [([0, -2, -1, 1, 0, 0, 2], 9), ([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, 0, 1, 0, 0, 1], 9), ([0, -1, -2, 1, 0, 0, 2], 9), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, 0, 0, 0], 18), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, 0, -2, 1, 0, 0, 1], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 9), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], 18), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, 0, -2, 1, 0, 0, 1], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9)]

theorem source288_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source288 := by
  decide +kernel

theorem source288_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source288 (momentValues f) = 0 := by
  rw [← source288_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source289 : Sparse := [([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 1, -1, 0, 1, -2], -9), ([0, 1, 1, -1, 1, 0, -2], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 2, -1, -1, 0, -1], -9), ([0, 1, 2, -1, 0, 0, -2], 9), ([0, 2, 1, -1, 0, -1, -1], -9), ([0, 2, 1, -1, 0, 0, -2], 9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 2, -1, 0, 0, -1], -9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 1, -2, 0, 0, 0], -18), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 1, -2], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], -9), ([1, 1, 2, -1, 0, -1, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -9), ([1, 2, 1, -1, -1, 0, -1], -9)]

theorem source289_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source289 := by
  decide +kernel

theorem source289_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source289 (momentValues f) = 0 := by
  rw [← source289_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source290 : Sparse := [([0, -2, 0, 1, -1, 0, 2], 9), ([0, -2, 0, 1, -1, 1, 1], -9), ([0, -2, 0, 1, 0, 0, 1], 9), ([0, -2, 1, 1, -1, 0, 1], 9), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 1, -2, 1, 1], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 0, 2, -1, 0, 0], 18), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, 1, -1, -1, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 9), ([1, -2, 1, 1, -1, 0, 1], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, 1, -2, 0, 2], 9), ([1, -1, 0, 1, -2, 1, 1], 9), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 2, -1, 0, 0], 18), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 1, -2, 0, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -2, 0, 1], -9), ([1, 0, 0, 1, -1, -1, 1], 9)]

theorem source290_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source290 := by
  decide +kernel

theorem source290_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source290 (momentValues f) = 0 := by
  rw [← source290_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source291 : Sparse := [([0, 0, 0, -1, 2, 0, -1], 9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, 0, -1, 1, 1, -2], -9), ([0, 1, 0, -1, 2, 0, -2], -9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, -1, 1, 0, -2], 9), ([0, 2, 0, -1, 1, -1, -1], -9), ([0, 2, 0, -1, 1, 0, -2], 9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, -1, 2, 0, -1], 9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, 0, -2, 1, 0, 0], -18), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 0, -1, 1, 1, -2], -9), ([1, 1, 0, -1, 2, -1, -1], -9), ([1, 1, 0, -1, 2, 0, -2], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 2, -1, -1, 1, 0, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -9)]

theorem source291_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source291 := by
  decide +kernel

theorem source291_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source291 (momentValues f) = 0 := by
  rw [← source291_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source292 : Sparse := [([0, -2, 0, 1, 0, -1, 2], -9), ([0, -2, 0, 1, 0, 0, 1], 9), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, 0, -2, 2], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 0, 1, -1, -1, 1], -9), ([1, -2, 0, 1, 0, -1, 2], -9), ([1, -2, 0, 1, 0, 0, 1], 9), ([1, -2, 0, 1, 1, -1, 1], -9), ([1, -2, 1, 1, 0, -1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], -9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -9), ([1, -1, 0, 2, 0, -1, 0], -18), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, 0, 1, 0, -2, 1], -9)]

theorem source292_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source292 := by
  decide +kernel

theorem source292_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source292 (momentValues f) = 0 := by
  rw [← source292_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source293 : Sparse := [([0, 0, 0, -1, 0, 2, -1], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 2, -1], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -2, 0, 1, 0], 18), ([0, 1, 0, -1, -1, 2, -1], 9), ([0, 1, 0, -1, 0, 2, -2], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, -1, 1, 1, -2], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 2, -1, -1, 0, 1, -1], 9), ([0, 2, 0, -1, -1, 1, -1], 9), ([1, 0, 0, -1, 0, 2, -1], 9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -2, 0, 1, 0], 18), ([1, 1, 0, -1, -1, 2, -1], 9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 0, 1, -2], 9), ([1, 2, -1, -1, 0, 1, -1], 9), ([1, 2, 0, -1, -1, 1, -1], 9), ([1, 2, 0, -1, 0, 0, -1], -9), ([1, 2, 0, -1, 0, 1, -2], 9)]

theorem source293_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source293 := by
  decide +kernel

theorem source293_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source293 (momentValues f) = 0 := by
  rw [← source293_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source294 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, 0, -2, 1, -1, 0, 2], -9), ([0, 0, -2, 1, 0, 0, 1], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 1, -2, 0, 2], 9), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 1, -2, 0, 1], -9), ([1, -1, -1, 1, -1, 0, 2], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, 0, -2, 1, -1, 0, 2], -9), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 0, 1], 9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 2, -1, 0, 0], -18), ([1, 0, 0, 1, -2, 0, 1], -9), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9)]

theorem source294_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source294 := by
  decide +kernel

theorem source294_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source294 (momentValues f) = 0 := by
  rw [← source294_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source295 : Sparse := [([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, -1, 2, 0, -1], -9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 2, -1, 1, 0, -1], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, -1, 2, 0, -1], 9), ([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 1, -2, 1, 0, 0], 18), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, -1, 1, 1, -2], 9), ([0, 0, 1, -1, 2, -1, -1], 9), ([0, 0, 1, -1, 2, 0, -2], 9), ([0, 0, 2, -1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 2, -1, 1, 0, -1], 9), ([1, 0, 0, -1, 2, 0, -1], 9), ([1, 0, 1, -2, 1, 0, 0], 18), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, -1, 2, -1, -1], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 2, -1, 0, 0, -1], -9), ([1, 0, 2, -1, 1, -1, -1], 9), ([1, 0, 2, -1, 1, 0, -2], 9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], 9)]

theorem source295_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source295 := by
  decide +kernel

theorem source295_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source295 (momentValues f) = 0 := by
  rw [← source295_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
