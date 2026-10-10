import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source56 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -36), ([0, -2, 1, 0, 2, 0, -1], -36), ([0, -2, 2, 0, 1, 0, -1], 36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 2, 0, 0, 0, -1], -36), ([0, -1, 2, 0, 1, 0, -2], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([1, -2, 1, 0, 1, 0, 0], -36), ([1, -2, 2, 0, 1, 0, -1], 36), ([1, -1, 0, 0, 2, 0, -1], 36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 0, 2, 0, -2], -36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, -1, 2, 0, 0, 0, -1], -36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 0, 1, 0, 1, 0, -2], 36)]

theorem source56_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![-1, 1, 0, 1, 0, -1] (-12, 0)) = source56 := by
  decide +kernel

theorem source56_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source56 (momentValues f) = 0 := by
  rw [← source56_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source57 : Sparse := [([0, -2, 1, 2, -1, 0, 0], -36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 2, -1, 0, 0], -36), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, -2, 0, 0], 36), ([0, -1, 2, 1, -2, 0, 0], -36), ([0, 0, 1, 1, -2, 0, 0], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([1, -2, 1, 1, 0, 0, 0], 36), ([1, -2, 2, 1, -1, 0, 0], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 2, -1, 0, 0], -36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 2, -2, 0, 0], 36), ([1, -1, 2, 0, -1, 0, 0], 36), ([1, 0, 1, 1, -2, 0, 0], -36), ([1, 0, 1, 1, -1, 0, -1], 36)]

theorem source57_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![-1, 1, 1, -1, 0, 0] (-12, 0)) = source57 := by
  decide +kernel

theorem source57_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source57 (momentValues f) = 0 := by
  rw [← source57_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source58 : Sparse := [([0, -2, 1, 2, 0, -1, 0], -36), ([0, -2, 2, 1, 0, -1, 0], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 2, 0, -2, 0], -36), ([0, -1, 2, 1, 0, -2, 0], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 1, 1, 0, -1, -1], -36), ([1, -2, 1, 1, 0, 0, 0], 36), ([1, -1, 0, 2, 0, -1, 0], 36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, -1, 2, 0, 0, -1, 0], 36), ([1, 0, 1, 1, 0, -2, 0], 36)]

theorem source58_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![-1, 1, 1, 0, -1, 0] (-12, 0)) = source58 := by
  decide +kernel

theorem source58_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source58 (momentValues f) = 0 := by
  rw [← source58_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source59 : Sparse := [([0, -2, 2, 1, 0, 0, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, -1, 1, 2, 0, 0, -2], -36), ([0, -1, 2, 0, 0, 0, -1], -36), ([0, -1, 2, 1, 0, 0, -2], 36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 1, 1, 0, 0, -2], -36), ([1, -2, 1, 1, 0, 0, 0], 36), ([1, -2, 1, 2, 0, 0, -1], -36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 0, 2, 0, 0, -1], 36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, -1, 2, 0, 0, 0, -1], -36), ([1, -1, 2, 1, 0, 0, -2], 36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 1, 1, 0, 0, -2], -36)]

theorem source59_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![-1, 1, 1, 0, 0, -1] (-12, 0)) = source59 := by
  decide +kernel

theorem source59_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source59 (momentValues f) = 0 := by
  rw [← source59_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source60 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -36), ([0, 0, -2, -1, 0, 1, 2], -36), ([0, 0, -2, -1, 0, 2, 1], 36), ([0, 0, -2, 0, 0, 1, 1], -36), ([0, 0, -1, -2, 0, 2, 1], -36), ([0, 0, -1, -1, 0, 2, 0], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, 0, -1, -1, 1, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, 0, -2, -1, 0, 2, 1], 36), ([1, 0, -2, 0, 0, 1, 1], -36), ([1, 0, -1, -2, 0, 1, 2], -36), ([1, 0, -1, -1, 0, 0, 2], 36), ([1, 0, -1, -1, 0, 2, 0], -36), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, 0, -2, 0, 1, 1], 36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, -1, -1, 0, 1, 0], 36)]

theorem source60_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, -1, -1, 0, 1, 1] (-12, 0)) = source60 := by
  decide +kernel

theorem source60_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source60 (momentValues f) = 0 := by
  rw [← source60_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source61 : Sparse := [([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, 0, -2, -1, 1, 0, 2], -36), ([0, 0, -2, -1, 2, 0, 1], -36), ([0, 0, -1, -2, 1, 0, 2], -36), ([0, 0, -1, -2, 2, 0, 1], -36), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, 0, -1, 1, -1, 1], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, 0, -2, 0, 1, 0, 1], 36), ([1, 0, -1, -1, 0, 0, 2], 36), ([1, 0, -1, -1, 2, 0, 0], 36), ([1, 0, 0, -2, 1, 0, 1], 36), ([1, 1, -1, -1, 1, -1, 1], 36)]

theorem source61_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, -1, -1, 1, 0, 1] (-12, 0)) = source61 := by
  decide +kernel

theorem source61_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source61 (momentValues f) = 0 := by
  rw [← source61_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source62 : Sparse := [([0, -1, 0, -1, 1, 1, 0], -36), ([0, 0, -2, -1, 1, 2, 0], -36), ([0, 0, -1, -2, 1, 2, 0], 36), ([0, 0, -1, -2, 2, 1, 0], -36), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 2, 0], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, 0, -2, 1, 1, 0], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, 0, -2, -1, 2, 1, 0], -36), ([1, 0, -2, 0, 1, 1, 0], 36), ([1, 0, -1, -2, 1, 2, 0], 36), ([1, 0, -1, -1, 0, 2, 0], -36), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, -1, 2, 0, 0], 36), ([1, 0, 0, -2, 1, 1, 0], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, 1, -1], -36)]

theorem source62_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, -1, -1, 1, 1, 0] (-12, 0)) = source62 := by
  decide +kernel

theorem source62_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source62 (momentValues f) = 0 := by
  rw [← source62_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source63 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, 0, -2, 0, -1, 1, 2], -36), ([0, 0, -2, 0, -1, 2, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, 0, -2, 1, 2], -36), ([0, 0, -1, 0, -2, 2, 1], -36), ([0, 0, -1, 0, -1, 0, 2], -36), ([0, 0, -1, 0, -1, 2, 0], -36), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, 0, -1, -1, 1, 1], -36), ([0, 0, 0, 0, -2, 1, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, 0, -2, 0, 0, 1, 1], -36), ([1, 0, -1, 0, -1, 0, 2], -36), ([1, 0, -1, 0, -1, 2, 0], -36), ([1, 0, 0, 0, -2, 1, 1], -36), ([1, 1, -1, -1, -1, 1, 1], -36)]

theorem source63_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, -1, 0, -1, 1, 1] (-12, 0)) = source63 := by
  decide +kernel

theorem source63_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source63 (momentValues f) = 0 := by
  rw [← source63_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
