import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source232 : Sparse := [([0, -2, 1, 0, 0, -1, 2], 9), ([0, -2, 1, 1, 0, -1, 1], -9), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 1, -1, 0, -1, 2], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, -1, -1, 2], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, 0, -2, 2], -9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 1, 0, 0, -2, 1], 9), ([1, -2, 1, 0, 0, 0, 1], -9), ([1, -2, 1, 0, 1, -1, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], -9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -2, 2], -9), ([1, -1, 1, 0, 1, -2, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 2, 0, 0, -1, 0], -18), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, 0, -2, 1], 9)]

theorem source232_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source232 := by
  decide +kernel

theorem source232_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source232 (momentValues f) = 0 := by
  rw [← source232_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source233 : Sparse := [([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 1, -2, 0, 0, 1, 0], 18), ([0, 1, -1, -1, 0, 2, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, -1, 2, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 2, -1, -1, 0, 1, -1], -9), ([0, 2, -1, 0, -1, 1, -1], 9), ([0, 2, -1, 0, 0, 0, -1], 9), ([0, 2, -1, 0, 0, 1, -2], 9), ([1, 0, -1, 0, 0, 2, -1], -9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 1, -2, 0, 0, 1, 0], 18), ([1, 1, -1, -1, 0, 2, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, -1, 2, -1], 9), ([1, 1, -1, 0, 0, 2, -2], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 0, 1, -2], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 2, -1, 0, -1, 1, -1], 9), ([1, 2, -1, 0, 0, 0, -1], 9)]

theorem source233_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source233 := by
  decide +kernel

theorem source233_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source233 (momentValues f) = 0 := by
  rw [← source233_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source234 : Sparse := [([0, -1, 1, -1, -1, 0, 2], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 1, -2, -1, 0, 2], -9), ([0, 0, 1, -2, 0, 0, 1], 9), ([0, 0, 1, -1, -2, 0, 2], 9), ([0, 0, 1, -1, -2, 1, 1], -9), ([0, 0, 1, -1, -1, -1, 2], -9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 1, -2, -1, 0, 2], -9), ([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -2, 0, 0, 1], 9), ([1, 0, 1, -1, -1, -1, 2], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, 0, -2, 0, 1], -9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 2, -1, -1, 0, 0], -18), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 1, -2, -1, 0, 1], -9), ([1, 1, 1, -1, -2, 0, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9)]

theorem source234_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source234 := by
  decide +kernel

theorem source234_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source234 (momentValues f) = 0 := by
  rw [← source234_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source235 : Sparse := [([0, -1, -1, 1, 2, 0, -1], 9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, 0, -2, 1, 1, 0, 0], 18), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 0, 2, 0, -1], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 1, 2, -1, -1], -9), ([0, 0, -1, 1, 2, 0, -2], 9), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, 0, -1], 9), ([1, -1, -1, 2, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, 0, -2, 1, 1, 0, 0], 18), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 0, 2, 0, -1], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 1, 1, 1, -2], 9), ([1, 0, -1, 2, 0, 0, -1], -9), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, -1, 2, 1, 0, -2], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9)]

theorem source235_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source235 := by
  decide +kernel

theorem source235_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source235 (momentValues f) = 0 := by
  rw [← source235_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source236 : Sparse := [([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 1, -2, 0, -1, 2], 9), ([0, 0, 1, -2, 0, 0, 1], 9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -1, 0, -2, 2], 9), ([0, 0, 1, -1, 1, -2, 1], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, 0, -2, 1], 9), ([0, 0, 2, -1, 0, -1, 0], 18), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -2, 1], -9), ([1, -1, 1, -1, 0, -1, 2], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 1, -2, 0, 0, 1], 9), ([1, 0, 1, -1, -1, -1, 2], 9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, 1, -2, 1], 9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, 0, -2, 1], 9), ([1, 0, 2, -1, 0, -1, 0], 18), ([1, 1, 1, -2, 0, -1, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9)]

theorem source236_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source236 := by
  decide +kernel

theorem source236_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source236 (momentValues f) = 0 := by
  rw [← source236_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source237 : Sparse := [([0, -1, -1, 1, 0, 2, -1], -9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, 0, -1, 1, 0, 2, -2], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, -1, 1, 1, 1, -2], -9), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, -1, 2, 0, 1, -2], 9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 1, 0, 1, -2], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 0, 1, -1], -9), ([1, 0, -2, 1, 0, 1, 0], -18), ([1, 0, -1, 0, 0, 2, -1], -9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 1, -1, 2, -1], -9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 1, 1, 1, -2], -9), ([1, 0, -1, 2, 0, 0, -1], -9), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -9)]

theorem source237_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source237 := by
  decide +kernel

theorem source237_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source237 (momentValues f) = 0 := by
  rw [← source237_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source238 : Sparse := [([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 1, -1, -1, -1, 2], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, 0, -1, -2, 2], 9), ([0, 0, 1, 0, 0, -2, 1], 9), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -1, -2, 1], 9), ([0, 0, 2, 0, -1, -1, 0], 18), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -2, -1, 1], 9), ([0, 1, 1, 0, -1, -2, 1], -9), ([1, -1, 1, 0, -1, -1, 2], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, 0, -2, -1, 2], 9), ([1, 0, 1, 0, -2, 0, 1], -9), ([1, 0, 1, 0, 0, -2, 1], 9), ([1, 0, 1, 1, -2, -1, 1], 9), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 2, 0, -1, -1, 0], 18), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -2, -1, 1], 9)]

theorem source238_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source238 := by
  decide +kernel

theorem source238_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source238 (momentValues f) = 0 := by
  rw [← source238_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source239 : Sparse := [([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, 0, -1, 0, 1, 2, -2], 9), ([0, 0, -1, 0, 2, 0, -1], 9), ([0, 0, -1, 0, 2, 1, -2], -9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, 1, -2], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 1, 1, -2], -9), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, 0, -2, 0, 1, 1, 0], -18), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, -1, 0, 0, 2, -1], -9), ([1, 0, -1, 0, 2, 0, -1], 9), ([1, 0, -1, 0, 2, 1, -2], -9), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 1, -2], -9)]

theorem source239_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source239 := by
  decide +kernel

theorem source239_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source239 (momentValues f) = 0 := by
  rw [← source239_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
