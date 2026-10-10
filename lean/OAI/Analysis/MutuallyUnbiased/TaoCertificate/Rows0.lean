import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source0 : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -2, -1, 0, 0, 1, 2], 18), ([0, -2, -1, 0, 1, 0, 2], -18), ([0, -2, -1, 1, 0, 0, 2], 18), ([0, -2, 0, -1, 0, 1, 2], 18), ([0, -2, 0, -1, 1, 0, 2], 18), ([0, -2, 0, 0, 1, -1, 2], 18), ([0, -2, 0, 0, 1, 0, 1], 18), ([0, -2, 0, 1, -1, 0, 2], 18), ([0, -2, 0, 1, 0, -1, 2], -18), ([0, -2, 0, 1, 0, 0, 1], 18), ([0, -2, 1, 0, -1, 0, 2], 18), ([0, -2, 1, 0, 0, -1, 2], 18), ([0, -1, -1, 0, 0, 0, 2], 18), ([0, -1, 0, 0, 0, -1, 2], 18), ([1, -2, -1, 0, 1, 0, 2], -18), ([1, -2, 0, 0, -1, 1, 2], 18), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -2, 0, 1, 0, -1, 2], -18), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -2, 1, -1, 0, 0, 2], 18), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, -1, 0, 0, 0, 2], 18), ([1, -1, 0, -1, 0, 0, 2], -18), ([1, -1, 0, 0, -1, 0, 2], -18), ([1, -1, 0, 0, 0, -1, 2], 18)]

theorem source0_checked : normalize (row ![-2, 0, 0, 0, 0, 2] ![-2, 0, 0, 0, 0, 2] (6, 0)) = source0 := by
  decide +kernel

theorem source0_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source0 (momentValues f) = 0 := by
  rw [← source0_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source1 : Sparse := [([0, -3, 0, 0, 0, 3, 0], 36), ([0, -2, -1, 0, 1, 2, 0], 18), ([0, -2, -1, 1, 0, 2, 0], 18), ([0, -2, 0, -1, 0, 2, 1], 18), ([0, -2, 0, 0, -1, 2, 1], 18), ([0, -2, 0, 0, 1, 2, -1], 18), ([0, -2, 0, 1, -1, 2, 0], 18), ([0, -2, 0, 1, 0, 1, 0], 18), ([0, -2, 0, 1, 0, 2, -1], -18), ([0, -2, 1, -1, 0, 2, 0], 18), ([0, -2, 1, 0, -1, 2, 0], -18), ([0, -2, 1, 0, 0, 1, 0], 18), ([0, -2, 1, 0, 0, 2, -1], 18), ([0, -1, 0, 0, -1, 2, 0], 18), ([0, -1, 0, 0, 0, 2, -1], 18), ([1, -2, -1, 0, 0, 2, 1], 18), ([1, -2, 0, -1, 1, 2, 0], 18), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -2, 0, 1, 0, 2, -1], -18), ([1, -2, 1, 0, -1, 2, 0], -18), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -1, -1, 0, 0, 2, 0], -18), ([1, -1, 0, -1, 0, 2, 0], -18), ([1, -1, 0, 0, -1, 2, 0], 18), ([1, -1, 0, 0, 0, 2, -1], 18)]

theorem source1_checked : normalize (row ![-2, 0, 0, 0, 2, 0] ![-2, 0, 0, 0, 2, 0] (6, 0)) = source1 := by
  decide +kernel

theorem source1_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source1 (momentValues f) = 0 := by
  rw [← source1_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source2 : Sparse := [([0, -3, 0, 0, 3, 0, 0], 36), ([0, -2, -1, 0, 2, 0, 1], 18), ([0, -2, -1, 0, 2, 1, 0], 18), ([0, -2, 0, -1, 2, 0, 1], -18), ([0, -2, 0, -1, 2, 1, 0], 18), ([0, -2, 0, 0, 1, 0, 1], 18), ([0, -2, 0, 0, 2, -1, 1], 18), ([0, -2, 0, 1, 2, -1, 0], 18), ([0, -2, 0, 1, 2, 0, -1], 18), ([0, -2, 1, -1, 2, 0, 0], 18), ([0, -2, 1, 0, 1, 0, 0], 18), ([0, -2, 1, 0, 2, -1, 0], -18), ([0, -2, 1, 0, 2, 0, -1], 18), ([0, -1, 0, -1, 2, 0, 0], 18), ([0, -1, 0, 0, 2, -1, 0], 18), ([1, -2, -1, 1, 2, 0, 0], 18), ([1, -2, 0, -1, 2, 0, 1], -18), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -2, 0, 0, 2, 1, -1], 18), ([1, -2, 0, 1, 1, 0, 0], -18), ([1, -2, 1, 0, 1, 0, 0], 18), ([1, -2, 1, 0, 2, -1, 0], -18), ([1, -1, -1, 0, 2, 0, 0], -18), ([1, -1, 0, -1, 2, 0, 0], 18), ([1, -1, 0, 0, 2, -1, 0], 18), ([1, -1, 0, 0, 2, 0, -1], -18)]

theorem source2_checked : normalize (row ![-2, 0, 0, 2, 0, 0] ![-2, 0, 0, 2, 0, 0] (6, 0)) = source2 := by
  decide +kernel

theorem source2_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source2 (momentValues f) = 0 := by
  rw [← source2_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source3 : Sparse := [([0, -3, 0, 3, 0, 0, 0], 36), ([0, -2, -1, 2, 0, 0, 1], 18), ([0, -2, -1, 2, 0, 1, 0], -18), ([0, -2, -1, 2, 1, 0, 0], 18), ([0, -2, 0, 1, 0, 0, 1], 18), ([0, -2, 0, 1, 0, 1, 0], 18), ([0, -2, 0, 2, -1, 0, 1], -18), ([0, -2, 0, 2, -1, 1, 0], 18), ([0, -2, 0, 2, 0, -1, 1], 18), ([0, -2, 0, 2, 0, 1, -1], 18), ([0, -2, 0, 2, 1, 0, -1], 18), ([0, -2, 1, 2, -1, 0, 0], 18), ([0, -2, 1, 2, 0, -1, 0], 18), ([0, -1, -1, 2, 0, 0, 0], 18), ([0, -1, 0, 2, -1, 0, 0], 18), ([1, -2, -1, 2, 0, 1, 0], -18), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -2, 0, 1, 1, 0, 0], -18), ([1, -2, 0, 2, -1, 0, 1], -18), ([1, -2, 0, 2, 1, -1, 0], 18), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -2, 1, 2, 0, 0, -1], 18), ([1, -1, -1, 2, 0, 0, 0], 18), ([1, -1, 0, 2, -1, 0, 0], 18), ([1, -1, 0, 2, 0, -1, 0], -18), ([1, -1, 0, 2, 0, 0, -1], -18)]

theorem source3_checked : normalize (row ![-2, 0, 2, 0, 0, 0] ![-2, 0, 2, 0, 0, 0] (6, 0)) = source3 := by
  decide +kernel

theorem source3_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source3 (momentValues f) = 0 := by
  rw [← source3_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source4 : Sparse := [([0, -3, 3, 0, 0, 0, 0], 36), ([0, -2, 1, 0, 0, 1, 0], 18), ([0, -2, 1, 0, 1, 0, 0], 18), ([0, -2, 2, -1, 0, 0, 1], 18), ([0, -2, 2, -1, 0, 1, 0], -18), ([0, -2, 2, -1, 1, 0, 0], 18), ([0, -2, 2, 0, -1, 0, 1], 18), ([0, -2, 2, 0, -1, 1, 0], 18), ([0, -2, 2, 0, 0, 1, -1], 18), ([0, -2, 2, 0, 1, -1, 0], 18), ([0, -2, 2, 0, 1, 0, -1], -18), ([0, -2, 2, 1, 0, -1, 0], 18), ([0, -2, 2, 1, 0, 0, -1], 18), ([0, -1, 2, -1, 0, 0, 0], 18), ([0, -1, 2, 0, 0, 0, -1], 18), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -2, 1, 0, 1, 0, 0], 18), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -2, 2, -1, 0, 1, 0], -18), ([1, -2, 2, 0, 0, -1, 1], 18), ([1, -2, 2, 0, 1, 0, -1], -18), ([1, -2, 2, 1, -1, 0, 0], 18), ([1, -1, 2, -1, 0, 0, 0], 18), ([1, -1, 2, 0, -1, 0, 0], -18), ([1, -1, 2, 0, 0, -1, 0], -18), ([1, -1, 2, 0, 0, 0, -1], 18)]

theorem source4_checked : normalize (row ![-2, 2, 0, 0, 0, 0] ![-2, 2, 0, 0, 0, 0] (6, 0)) = source4 := by
  decide +kernel

theorem source4_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source4 (momentValues f) = 0 := by
  rw [← source4_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source5 : Sparse := [([0, -1, -2, 0, 0, 1, 2], -18), ([0, -1, -2, 0, 1, 0, 2], 18), ([0, -1, -2, 1, 0, 0, 2], 18), ([0, -1, -1, 0, 0, 0, 2], 18), ([0, 0, -3, 0, 0, 0, 3], 36), ([0, 0, -2, -1, 0, 1, 2], 18), ([0, 0, -2, -1, 1, 0, 2], 18), ([0, 0, -2, 0, -1, 1, 2], 18), ([0, 0, -2, 0, 0, 1, 1], 18), ([0, 0, -2, 1, -1, 0, 2], -18), ([0, 0, -2, 1, 0, -1, 2], 18), ([0, 0, -2, 1, 0, 0, 1], 18), ([0, 0, -1, 0, -1, 0, 2], 18), ([0, 1, -2, 0, -1, 0, 2], 18), ([0, 1, -2, 0, 0, -1, 2], 18), ([1, -1, -2, 0, 0, 1, 2], -18), ([1, -1, -1, 0, 0, 0, 2], 18), ([1, 0, -2, 0, 0, 1, 1], 18), ([1, 0, -2, 0, 1, -1, 2], 18), ([1, 0, -2, 0, 1, 0, 1], -18), ([1, 0, -2, 1, -1, 0, 2], -18), ([1, 0, -2, 1, 0, 0, 1], 18), ([1, 0, -1, -1, 0, 0, 2], -18), ([1, 0, -1, 0, -1, 0, 2], 18), ([1, 0, -1, 0, 0, -1, 2], -18), ([1, 1, -2, -1, 0, 0, 2], 18), ([1, 1, -2, 0, 0, 0, 1], -18)]

theorem source5_checked : normalize (row ![0, -2, 0, 0, 0, 2] ![0, -2, 0, 0, 0, 2] (6, 0)) = source5 := by
  decide +kernel

theorem source5_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source5 (momentValues f) = 0 := by
  rw [← source5_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source6 : Sparse := [([0, -1, -2, 0, 0, 2, 1], 18), ([0, -1, -2, 0, 1, 2, 0], 18), ([0, 0, -3, 0, 0, 3, 0], 36), ([0, 0, -2, -1, 0, 2, 1], -18), ([0, 0, -2, -1, 1, 2, 0], 18), ([0, 0, -2, 0, -1, 2, 1], 18), ([0, 0, -2, 0, 0, 1, 1], 18), ([0, 0, -2, 1, -1, 2, 0], 18), ([0, 0, -2, 1, 0, 2, -1], 18), ([0, 0, -1, -1, 0, 2, 0], 18), ([0, 0, -1, 0, -1, 2, 0], 18), ([0, 1, -2, -1, 0, 2, 0], 18), ([0, 1, -2, 0, -1, 2, 0], -18), ([0, 1, -2, 0, 0, 1, 0], 18), ([0, 1, -2, 0, 0, 2, -1], 18), ([1, -1, -2, 1, 0, 2, 0], 18), ([1, -1, -1, 0, 0, 2, 0], -18), ([1, 0, -2, -1, 0, 2, 1], -18), ([1, 0, -2, 0, 0, 1, 1], 18), ([1, 0, -2, 0, 1, 1, 0], -18), ([1, 0, -2, 0, 1, 2, -1], 18), ([1, 0, -2, 1, 0, 1, 0], -18), ([1, 0, -1, -1, 0, 2, 0], 18), ([1, 0, -1, 0, -1, 2, 0], 18), ([1, 0, -1, 0, 0, 2, -1], -18), ([1, 1, -2, 0, -1, 2, 0], -18), ([1, 1, -2, 0, 0, 1, 0], 18)]

theorem source6_checked : normalize (row ![0, -2, 0, 0, 2, 0] ![0, -2, 0, 0, 2, 0] (6, 0)) = source6 := by
  decide +kernel

theorem source6_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source6 (momentValues f) = 0 := by
  rw [← source6_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source7 : Sparse := [([0, -1, -2, 0, 2, 1, 0], 18), ([0, -1, -2, 1, 2, 0, 0], 18), ([0, 0, -3, 0, 3, 0, 0], 36), ([0, 0, -2, -1, 2, 0, 1], 18), ([0, 0, -2, 0, 2, -1, 1], 18), ([0, 0, -2, 0, 2, 1, -1], 18), ([0, 0, -2, 1, 1, 0, 0], 18), ([0, 0, -2, 1, 2, -1, 0], 18), ([0, 0, -2, 1, 2, 0, -1], -18), ([0, 0, -1, 0, 2, -1, 0], 18), ([0, 0, -1, 0, 2, 0, -1], 18), ([0, 1, -2, -1, 2, 0, 0], 18), ([0, 1, -2, 0, 1, 0, 0], 18), ([0, 1, -2, 0, 2, -1, 0], -18), ([0, 1, -2, 0, 2, 0, -1], 18), ([1, -1, -2, 0, 2, 0, 1], 18), ([1, -1, -1, 0, 2, 0, 0], -18), ([1, 0, -2, -1, 2, 1, 0], 18), ([1, 0, -2, 0, 1, 0, 1], -18), ([1, 0, -2, 0, 1, 1, 0], -18), ([1, 0, -2, 1, 1, 0, 0], 18), ([1, 0, -2, 1, 2, 0, -1], -18), ([1, 0, -1, -1, 2, 0, 0], -18), ([1, 0, -1, 0, 2, -1, 0], 18), ([1, 0, -1, 0, 2, 0, -1], 18), ([1, 1, -2, 0, 1, 0, 0], 18), ([1, 1, -2, 0, 2, -1, 0], -18)]

theorem source7_checked : normalize (row ![0, -2, 0, 2, 0, 0] ![0, -2, 0, 2, 0, 0] (6, 0)) = source7 := by
  decide +kernel

theorem source7_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source7 (momentValues f) = 0 := by
  rw [← source7_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
