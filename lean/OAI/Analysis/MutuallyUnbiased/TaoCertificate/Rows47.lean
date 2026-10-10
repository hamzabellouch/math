import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source376 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 9), ([0, -2, 1, 0, 1, 1, -1], 9), ([0, -2, 1, 1, 0, 1, -1], -9), ([0, -2, 2, 0, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 2, -1], 18), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 0, 1, 1, -2], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 1, 0, 1, -2], 9), ([0, -1, 2, 0, 0, 1, -2], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, 0, 0, 1, -2], 9), ([1, -2, 1, 0, 0, 1, 0], 9), ([1, -2, 1, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 0, 2, -1], 18), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 1, -2], 9), ([1, -1, 2, -1, 0, 1, -1], 9), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 0, 1, -2], 9)]

theorem source376_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![0, 1, 0, 0, -1, 0] (3, 3)) = source376 := by
  decide +kernel

theorem source376_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source376 (momentValues f) = 0 := by
  rw [← source376_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source377 : Sparse := [([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 1, -2, 0, 0, -1, 2], 9), ([0, 1, -2, 0, 1, -1, 1], -9), ([0, 1, -2, 1, 0, -1, 1], -9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, 0, -1, -1, 2], -9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 2, -2, 0, 0, -1, 1], 9), ([0, 2, -1, -1, 0, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], -9), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -2, 1, 0, -1, 1], -9), ([1, 1, -1, -1, 0, -1, 2], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, 0, 0, 0, -2, 1], -18), ([1, 2, -1, 0, -1, -1, 1], -9), ([1, 2, -1, 0, 0, -1, 0], -9)]

theorem source377_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![0, -1, 0, 0, 1, 0] (0, -3)) = source377 := by
  decide +kernel

theorem source377_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source377 (momentValues f) = 0 := by
  rw [← source377_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source378 : Sparse := [([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 2, -1, -1, 1, 0], -9), ([0, 0, 1, -2, -1, 1, 1], -9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 2, -2, -1, 1, 0], 9), ([0, 0, 2, -1, -2, 1, 0], 9), ([0, 0, 2, -1, -1, 1, -1], -9), ([0, 1, 1, -1, -2, 1, 0], -9), ([0, 1, 1, -1, -1, 0, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 2, -1, -1, 1, 0], -9), ([1, 0, 0, -1, -1, 2, 0], -18), ([1, 0, 1, -2, 0, 1, 0], -9), ([1, 0, 1, -1, -2, 1, 1], -9), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, 0, -2, 1, 0], -9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 2, -1, -1, 1, -1], -9), ([1, 1, 1, -2, -1, 1, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9)]

theorem source378_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 1, 0, 0, -1, 0] (0, -3)) = source378 := by
  decide +kernel

theorem source378_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source378 (momentValues f) = 0 := by
  rw [← source378_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source379 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 1, 2, -1, 0], -9), ([0, -1, -1, 2, 1, -1, 0], 9), ([0, 0, -2, 1, 2, -1, 0], 9), ([0, 0, -2, 2, 1, -1, 0], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 0, 2, -1, 0], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, -1, 1, 2, -1, -1], 9), ([0, 0, -1, 2, 0, -1, 0], 9), ([0, 0, -1, 2, 1, -1, -1], -9), ([0, 0, 0, 1, 1, -2, 0], 18), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 1, -1, 0], 9), ([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 2, -1, 0], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 2, -1, -1], 9), ([1, 0, -1, 2, 0, -1, 0], 9), ([1, 0, 0, 1, 1, -2, 0], 18), ([1, 1, -2, 1, 1, -1, 0], 9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9)]

theorem source379_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, -1, 0, 0, 1, 0] (3, 3)) = source379 := by
  decide +kernel

theorem source379_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source379 (momentValues f) = 0 := by
  rw [← source379_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source380 : Sparse := [([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 2, -1, 0, 1, -1], 9), ([0, 0, 0, -1, 0, 2, -1], 18), ([0, 0, 1, -2, 1, 1, -1], 9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, -1, 1, 1, -2], -9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 0, 0, 1, -2], 9), ([0, 0, 2, -1, 0, 1, -2], 9), ([0, 1, 1, -2, 0, 1, -1], 9), ([0, 1, 1, -1, 0, 1, -2], 9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, 0, -1, 0, 2, -1], 18), ([1, 0, 1, -2, 0, 1, 0], -9), ([1, 0, 1, -2, 1, 1, -1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 1, 0, 0, 1, -2], 9), ([1, 0, 2, -2, 0, 1, -1], 9), ([1, 0, 2, -1, -1, 1, -1], 9), ([1, 1, 1, -2, 0, 1, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 0, 1, -2], 9)]

theorem source380_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 1, 0, 0, -1, 0] (3, 3)) = source380 := by
  decide +kernel

theorem source380_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source380 (momentValues f) = 0 := by
  rw [← source380_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source381 : Sparse := [([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, 0, -2, 1, 0, -1, 2], 9), ([0, 0, -2, 1, 1, -1, 1], -9), ([0, 0, -2, 2, 0, -1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 1, -1, -1, 2], -9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 2, 0, -1, 0], 9), ([0, 1, -2, 1, 0, -1, 1], 9), ([0, 1, -1, 0, 0, -1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], -9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 0, -1, 1], -9), ([1, 0, -2, 1, 1, -1, 1], -9), ([1, 0, -2, 2, 0, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], -9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, -1, 2, -1, -1, 1], -9), ([1, 0, -1, 2, 0, -1, 0], 9), ([1, 0, 0, 1, 0, -2, 1], -18), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -1, 0], -9)]

theorem source381_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, -1, 0, 0, 1, 0] (0, -3)) = source381 := by
  decide +kernel

theorem source381_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source381 (momentValues f) = 0 := by
  rw [← source381_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source382 : Sparse := [([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 2, 0, -1, 1, -1], -9), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 0, 0, 1, -2], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 2, -1, -1, 1, -1], 9), ([0, 0, 2, 0, -2, 1, -1], 9), ([0, 0, 2, 0, -1, 1, -2], -9), ([0, 1, 1, 0, -2, 1, -1], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, 0, -1, 1, -1], -9), ([1, 0, 0, 0, -1, 2, -1], -18), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, 0, -2, 1, 0], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 0, 0, 1, -2], 9), ([1, 0, 1, 1, -2, 1, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, -1, 1, -2], -9), ([1, 0, 2, 0, -1, 1, -2], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -1, 1, -2], -9)]

theorem source382_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 1, 0, 0, -1, 0] (0, -3)) = source382 := by
  decide +kernel

theorem source382_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source382 (momentValues f) = 0 := by
  rw [← source382_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source383 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 0, 2, -1, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, 0, -2, 0, 2, -1, 1], 9), ([0, 0, -2, 1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, -1, 2], 9), ([0, 0, -1, -1, 2, -1, 1], 9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 2, -1, 0], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -2, 1], 18), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([1, -1, -1, 0, 1, -1, 2], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, 0, -2, 0, 1, -1, 2], 9), ([1, 0, -1, -1, 1, -1, 2], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, -1, 2, -1, 1], 9), ([1, 0, -1, 0, 0, -1, 2], -9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 2, -1, 0], 9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], 18), ([1, 1, -2, 0, 1, -1, 1], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 1, -1, 0], 9)]

theorem source383_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, -1, 0, 0, 1, 0] (3, 3)) = source383 := by
  decide +kernel

theorem source383_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source383 (momentValues f) = 0 := by
  rw [← source383_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
