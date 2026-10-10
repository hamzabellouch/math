import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source312 : Sparse := [([0, -2, 1, -1, 1, 0, 1], -9), ([0, -2, 1, -1, 1, 1, 0], 9), ([0, -2, 1, 0, 1, 0, 0], 9), ([0, -2, 2, -1, 1, 0, 0], 9), ([0, -1, 0, -1, 2, 0, 0], 18), ([0, -1, 1, -2, 1, 0, 1], 9), ([0, -1, 1, -2, 1, 1, 0], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 2, -2, 1, 0, 0], 9), ([0, 0, 1, -2, 1, 0, 0], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([1, -2, 1, -1, 1, 1, 0], 9), ([1, -2, 1, 0, 1, 0, 0], 9), ([1, -1, 0, -1, 2, 0, 0], 18), ([1, -1, 1, -2, 1, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, -1, 1, 0, -1], 9), ([1, 0, 1, -2, 1, 0, 0], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, -1, 1, 0, -1], 9)]

theorem source312_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![0, 1, 0, -1, 0, 0] (3, 3)) = source312 := by
  decide +kernel

theorem source312_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source312 (momentValues f) = 0 := by
  rw [← source312_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source313 : Sparse := [([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -2, 2, -1, 0, 0], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 2, -2, 1, -1, 0, 0], 9), ([0, 2, -1, 1, -1, 0, -1], -9), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 2, -1, 0, 0], -9), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 1, -2, 0, 0], -18), ([1, 2, -1, 0, -1, 0, 0], -9), ([1, 2, -1, 1, -1, -1, 0], -9)]

theorem source313_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![0, -1, 0, 1, 0, 0] (0, -3)) = source313 := by
  decide +kernel

theorem source313_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source313 (momentValues f) = 0 := by
  rw [← source313_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source314 : Sparse := [([0, -2, 1, 0, 1, -1, 1], -9), ([0, -2, 1, 0, 1, 0, 0], 9), ([0, -2, 1, 1, 1, -1, 0], 9), ([0, -2, 2, 0, 1, -1, 0], 9), ([0, -1, 0, 0, 2, -1, 0], 18), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 1, 1, -2, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([1, -2, 1, 0, 1, 0, 0], 9), ([1, -2, 1, 1, 1, -1, 0], 9), ([1, -1, 0, 0, 2, -1, 0], 18), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 1, -2, 1], 9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, 0, 1, -2, 0], 9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -2, 0], -9), ([1, 0, 1, 0, 1, -1, -1], 9)]

theorem source314_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![0, 1, 0, -1, 0, 0] (3, 3)) = source314 := by
  decide +kernel

theorem source314_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source314 (momentValues f) = 0 := by
  rw [← source314_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source315 : Sparse := [([0, 0, -1, 0, -1, 2, 0], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 1, -2, 0, -1, 1, 1], -9), ([0, 1, -2, 0, -1, 2, 0], -9), ([0, 1, -2, 1, -1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 2, -2, 0, -1, 1, 0], 9), ([0, 2, -1, 0, -1, 1, -1], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, -1, 2, 0], 9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, -1, 2, 0], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 2, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, 0, -2, 1, 0], -18), ([1, 2, -1, -1, -1, 1, 0], -9), ([1, 2, -1, 0, -1, 0, 0], -9)]

theorem source315_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![0, -1, 0, 1, 0, 0] (0, -3)) = source315 := by
  decide +kernel

theorem source315_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source315 (momentValues f) = 0 := by
  rw [← source315_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source316 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 9), ([0, -2, 2, 0, 1, 0, -1], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 1, 1, 0, -2], -9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, -1, 2, 0, 1, 0, -2], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 0, 1, -1, -1], -9), ([1, -2, 1, 0, 1, 0, 0], 9), ([1, -2, 1, 0, 1, 1, -1], -9), ([1, -2, 1, 1, 1, 0, -1], -9), ([1, -2, 2, 0, 1, 0, -1], -9), ([1, -1, 0, 0, 2, 0, -1], -18), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 0, 1, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, -1, 1, 0, -1], -9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 1, 0, 1, 0, -2], -9)]

theorem source316_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![0, 1, 0, -1, 0, 0] (0, -3)) = source316 := by
  decide +kernel

theorem source316_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source316 (momentValues f) = 0 := by
  rw [← source316_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source317 : Sparse := [([0, 0, -1, 0, -1, 0, 2], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 1, -2, 0, -1, 0, 2], 9), ([0, 1, -2, 0, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 0, 2], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, 0, -1, -1, 2], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, 0, 0, -2, 0, 1], 18), ([0, 2, -1, -1, -1, 0, 1], 9), ([0, 2, -1, 0, -1, -1, 1], 9), ([1, 0, -1, 0, -1, 0, 2], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 1, -2, 1, -1, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -1, -1, 2], 9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, 0, 0, -2, 0, 1], 18), ([1, 2, -2, 0, -1, 0, 1], 9), ([1, 2, -1, -1, -1, 0, 1], 9), ([1, 2, -1, 0, -1, -1, 1], 9), ([1, 2, -1, 0, -1, 0, 0], -9)]

theorem source317_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![0, -1, 0, 1, 0, 0] (3, 3)) = source317 := by
  decide +kernel

theorem source317_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source317 (momentValues f) = 0 := by
  rw [← source317_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source318 : Sparse := [([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 2, -1, 1, -1, 0], -9), ([0, 0, 1, -2, 1, 0, 0], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 0, 2, -2, 1, -1, 0], -9), ([0, 0, 2, -1, 1, -2, 0], 9), ([0, 0, 2, -1, 1, -1, -1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, -1, 1, -2, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 2, -1, 1, -1, 0], -9), ([1, 0, 0, -1, 2, -1, 0], -18), ([1, 0, 1, -2, 1, -1, 1], -9), ([1, 0, 1, -2, 1, 0, 0], 9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, -1, 1, -2, 1], -9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 1, 0, 1, -2, 0], -9), ([1, 0, 2, -2, 1, -1, 0], -9), ([1, 1, 1, -2, 1, -1, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9)]

theorem source318_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 1, 0, -1, 0, 0] (0, -3)) = source318 := by
  decide +kernel

theorem source318_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source318 (momentValues f) = 0 := by
  rw [← source318_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source319 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 2, -1, 1, 0], 9), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -2, 1, -1, 2, 0], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, -1, 2, 0], 9), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, -1, 2, -1], 9), ([0, 0, -1, 2, -1, 1, -1], 9), ([0, 0, 0, 1, -2, 1, 0], 18), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 2, -1, 1, 0], 9), ([1, 0, -2, 2, -1, 1, 0], 9), ([1, 0, -1, 0, -1, 2, 0], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 2, -1], 9), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 2, -1, 0, 0], -9), ([1, 0, -1, 2, -1, 1, -1], 9), ([1, 0, 0, 1, -2, 1, 0], 18), ([1, 1, -2, 1, -1, 1, 0], 9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9)]

theorem source319_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, -1, 0, 1, 0, 0] (3, 3)) = source319 := by
  decide +kernel

theorem source319_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source319 (momentValues f) = 0 := by
  rw [← source319_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
