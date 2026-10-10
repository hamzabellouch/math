import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source136 : Sparse := [([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -2, 1, 1, 0, -1], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 0, 1, -2], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], -9), ([0, 1, -1, 2, 0, -1, -1], 9), ([0, 1, -1, 2, 0, 0, -2], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 2, -1, 0, 0, 0, -1], 18), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -2, 1, 0, 1, -1], 9), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -2, 2, 0, 0, -1], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 0, 1, -2], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, -1, 0, -1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 2, -1, 0, 0, 0, -1], 18)]

theorem source136_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source136 := by
  decide +kernel

theorem source136_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source136 (momentValues f) = 0 := by
  rw [← source136_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source137 : Sparse := [([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 1, -2, 0, 0, 2], 9), ([0, -1, 1, -2, 0, 1, 1], 9), ([0, -1, 1, -2, 1, 0, 1], -9), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 2, -2, 0, 0, 1], -9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], -9), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 1, -2, 1, 0, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 2, -2, 0, 0, 1], -9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 0, 0, 0], -9)]

theorem source137_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![1, 0, -1, 0, 0, 0] (0, -3)) = source137 := by
  decide +kernel

theorem source137_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source137 (momentValues f) = 0 := by
  rw [← source137_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source138 : Sparse := [([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, 0, 1, -2, -1, 1], 9), ([0, 1, 0, 1, -1, -2, 1], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -2, 0], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 2, -1, -2, 0], 9), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, 0, 0, -1, -1, 0], 18), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 2, -1, -1, 0], 9), ([1, 1, 0, 1, -2, -1, 1], 9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -2, 1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 2, -2, -1, 0], 9), ([1, 1, 1, 1, -2, -1, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, 0, 0, -1, -1, 0], 18)]

theorem source138_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source138 := by
  decide +kernel

theorem source138_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source138 (momentValues f) = 0 := by
  rw [← source138_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source139 : Sparse := [([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, 0, -2, 1, 1, 1], 9), ([0, -1, 0, -2, 1, 2, 0], 9), ([0, -1, 0, -2, 2, 1, 0], -9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 1, -2, 1, 1, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], -9), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, 0, -2, 2, 1, 0], -9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 2, -1], -9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 0, -1, 2, 1, -1], -9), ([1, -1, 1, -2, 1, 1, 0], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9)]

theorem source139_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![1, 0, -1, 0, 0, 0] (0, -3)) = source139 := by
  decide +kernel

theorem source139_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source139 (momentValues f) = 0 := by
  rw [← source139_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source140 : Sparse := [([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, -1, 2, -1, 0, -1], 9), ([0, 1, 0, 1, -2, 1, -1], -9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 1, 0, 2, -2, 0, -1], 9), ([0, 1, 0, 2, -1, -1, -1], -9), ([0, 1, 0, 2, -1, 0, -2], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, -1, 1, -2], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 1, 0, 2, -1, -1, -1], -9), ([1, 1, 0, 2, -1, 0, -2], -9), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 2, 0, 0, -1, 0, -1], -18)]

theorem source140_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source140 := by
  decide +kernel

theorem source140_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source140 (momentValues f) = 0 := by
  rw [← source140_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source141 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 18), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, -1, 2, 0, 1], 9), ([0, -1, 0, -2, 2, 0, 1], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, -1, 2], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, -1, 2, -1, 1], -9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 1, -2, 1, 0, 1], 9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], 9), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -1, -1, -1, 1, 0, 2], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, 0, -2, 1, 0, 2], 9), ([1, -1, 0, -2, 1, 1, 1], 9), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 1, -1, 2], 9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, 0, -1, 0, 0, 1], 9)]

theorem source141_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![1, 0, -1, 0, 0, 0] (3, 3)) = source141 := by
  decide +kernel

theorem source141_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source141 (momentValues f) = 0 := by
  rw [← source141_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source142 : Sparse := [([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, 0, -2, 0], 9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 0, 2, 0, -2, -1], 9), ([0, 1, 0, 2, 0, -1, -2], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 2, 0, 0, 0, -1, -1], 18), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, 0, -1, -1], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 0, 2, -1, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], 18)]

theorem source142_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source142 := by
  decide +kernel

theorem source142_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source142 (momentValues f) = 0 := by
  rw [← source142_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source143 : Sparse := [([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, 0, -2, 0, 1, 2], 9), ([0, -1, 0, -2, 0, 2, 1], 9), ([0, -1, 0, -2, 1, 1, 1], -9), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 1, -2, 0, 1, 1], -9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 0, 1, 0], -9), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, 0, -2, 1, 1, 1], -9), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 1, -2, 0, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 0, 1, 0], -9)]

theorem source143_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![1, 0, -1, 0, 0, 0] (0, -3)) = source143 := by
  decide +kernel

theorem source143_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source143 (momentValues f) = 0 := by
  rw [← source143_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
