import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source216 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 9), ([0, -2, 1, -1, 0, 2, 0], 9), ([0, -2, 1, -1, 1, 1, 0], -9), ([0, -2, 1, 0, 0, 1, 0], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 1, -2, 0, 1, 1], 9), ([0, -1, 1, -2, 1, 1, 0], 9), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 2, -1, 0, 0, 0], 18), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([1, -2, 1, -1, 0, 1, 1], 9), ([1, -2, 1, 0, 0, 1, 0], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 1, -2, 0, 1, 1], 9), ([1, -1, 1, -2, 0, 2, 0], 9), ([1, -1, 1, -2, 1, 1, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 2, -1, 0, 0, 0], 18), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 1, -2, 0, 1, 0], -9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, 0, 1, -1], 9)]

theorem source216_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![0, -1, 0, 0, 1, 0] (3, 3)) = source216 := by
  decide +kernel

theorem source216_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source216 (momentValues f) = 0 := by
  rw [← source216_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source217 : Sparse := [([0, 0, -1, 2, 0, -1, 0], 9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 1, 0, -2, 1], 9), ([0, 1, -1, 1, 1, -2, 0], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 2, 0, -2, 0], -9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 2, -1, 1, -1, -1, 0], -9), ([0, 2, -1, 1, 0, -2, 0], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, -1, 2, 0, -1, 0], 9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], -18), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, -1, -1, 0], -9), ([1, 1, -1, 2, 0, -2, 0], -9), ([1, 1, -1, 2, 0, -1, -1], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 2, -1, 0, 0, -1, 0], -9), ([1, 2, -1, 1, 0, -1, -1], -9)]

theorem source217_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![0, 1, 0, 0, -1, 0] (0, -3)) = source217 := by
  decide +kernel

theorem source217_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source217 (momentValues f) = 0 := by
  rw [← source217_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source218 : Sparse := [([0, -2, 1, 0, -1, 2, 0], -9), ([0, -2, 1, 0, 0, 1, 0], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, 0, -2, 1, 1], -9), ([0, -1, 1, 0, -2, 2, 0], 9), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, -1, -1, 1, 0], -9), ([1, -2, 1, 0, -1, 1, 1], -9), ([1, -2, 1, 0, -1, 2, 0], -9), ([1, -2, 1, 0, 0, 1, 0], 9), ([1, -2, 1, 1, -1, 1, 0], -9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, 0, -1, 2, -1], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, 0, -1, 0, 0], -18), ([1, 0, 1, 0, -2, 1, 0], -9), ([1, 0, 1, 0, -1, 1, -1], -9)]

theorem source218_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![0, -1, 0, 0, 1, 0] (0, -3)) = source218 := by
  decide +kernel

theorem source218_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source218 (momentValues f) = 0 := by
  rw [← source218_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source219 : Sparse := [([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 0, 2, -1, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 1, -2, 0, 1, 0, 0], 18), ([0, 1, -1, -1, 2, -1, 0], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 0, 2, -2, 0], 9), ([0, 1, -1, 0, 2, -1, -1], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 1, -2, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 2, -1, -1, 1, -1, 0], 9), ([0, 2, -1, 0, 1, -1, -1], 9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 0, 2, -1, 0], 9), ([1, 1, -2, 0, 1, 0, 0], 18), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 2, -1, 0], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 1, -2, 1], 9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 2, -1, -1, 1, -1, 0], 9), ([1, 2, -1, 0, 0, -1, 0], -9), ([1, 2, -1, 0, 1, -2, 0], 9), ([1, 2, -1, 0, 1, -1, -1], 9)]

theorem source219_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![0, 1, 0, 0, -1, 0] (3, 3)) = source219 := by
  decide +kernel

theorem source219_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source219 (momentValues f) = 0 := by
  rw [← source219_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source220 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 9), ([0, -2, 1, 0, 0, 2, -1], 9), ([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 1, 0, 1, -1], 9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 2, -2], 9), ([0, -1, 1, 0, 1, 1, -2], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 1, -2], -9), ([0, -1, 2, 0, 0, 0, -1], 18), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 0, 0, 1, -2], 9), ([1, -2, 1, 0, 0, 1, 0], 9), ([1, -2, 1, 1, 0, 1, -1], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 0, 2, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 0, -1, 2, -1], 9), ([1, -1, 1, 0, 1, 1, -2], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], 18), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 1, 0, 0, 1, -2], 9)]

theorem source220_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![0, -1, 0, 0, 1, 0] (3, 3)) = source220 := by
  decide +kernel

theorem source220_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source220 (momentValues f) = 0 := by
  rw [← source220_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source221 : Sparse := [([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 1, -1, -1, 0, -1, 2], -9), ([0, 1, -1, 0, 0, -2, 2], 9), ([0, 1, -1, 0, 1, -2, 1], -9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 1, 0, -2, 1], -9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 2, -1, 0, -1, -1, 1], -9), ([0, 2, -1, 0, 0, -2, 1], 9), ([1, 0, -1, 0, 0, -1, 2], -9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], -18), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, -1, -1, 2], -9), ([1, 1, -1, 0, 1, -2, 1], -9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -2, 1], -9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 2, -1, -1, 0, -1, 1], -9), ([1, 2, -1, 0, 0, -1, 0], -9)]

theorem source221_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![0, 1, 0, 0, -1, 0] (0, -3)) = source221 := by
  decide +kernel

theorem source221_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source221 (momentValues f) = 0 := by
  rw [← source221_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source222 : Sparse := [([0, -1, 1, -1, -1, 2, 0], -9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 1, -2, -1, 2, 0], 9), ([0, 0, 1, -1, -2, 1, 1], -9), ([0, 0, 1, -1, -2, 2, 0], 9), ([0, 0, 1, -1, -1, 2, -1], -9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 1, -2, -1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -2, 0, 1, 0], -9), ([1, 0, 1, -1, -1, 2, -1], -9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, 0, -2, 1, 0], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 2, -1, -1, 0, 0], -18), ([1, 1, 1, -1, -2, 1, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9)]

theorem source222_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, -1, 0, 0, 1, 0] (0, -3)) = source222 := by
  decide +kernel

theorem source222_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source222 (momentValues f) = 0 := by
  rw [← source222_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source223 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, 0, -2, 1, 1, 0, 0], 18), ([0, 0, -1, 0, 2, -1, 0], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 2, -2, 0], 9), ([0, 0, -1, 1, 2, -1, -1], -9), ([0, 0, -1, 2, 0, -1, 0], 9), ([0, 0, -1, 2, 1, -2, 0], 9), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 2, -1, 0], 9), ([1, 0, -2, 1, 1, 0, 0], 18), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 2, -1, 0], 9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 2, 0, -1, 0], 9), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 1, -2, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9)]

theorem source223_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, 1, 0, 0, -1, 0] (3, 3)) = source223 := by
  decide +kernel

theorem source223_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source223 (momentValues f) = 0 := by
  rw [← source223_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
