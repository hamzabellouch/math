import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source32 : Sparse := [([0, -2, -1, 0, 1, 2, 0], -36), ([0, -2, -1, 0, 2, 1, 0], -36), ([0, -1, -2, 0, 1, 2, 0], -36), ([0, -1, -2, 0, 2, 1, 0], -36), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([1, -2, 0, 0, 1, 1, 0], 36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, -1, 0, 0, 2, 0], 36), ([1, -1, -1, 0, 2, 0, 0], 36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, 0, -2, 0, 1, 1, 0], 36)]

theorem source32_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![-1, -1, 0, 1, 1, 0] (-12, 0)) = source32 := by
  decide +kernel

theorem source32_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source32 (momentValues f) = 0 := by
  rw [← source32_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source33 : Sparse := [([0, -2, -1, 1, 0, 0, 2], -36), ([0, -2, -1, 2, 0, 0, 1], -36), ([0, -2, 0, 1, 0, 0, 1], -36), ([0, -1, -2, 1, 0, 0, 2], -36), ([0, -1, -2, 2, 0, 0, 1], -36), ([0, -1, -1, 0, 0, 0, 2], -36), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 2, 0, 0, 0], -36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, 0, -2, 1, 0, 0, 1], -36), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, 0, -1, 1], -36), ([1, -2, 0, 1, 0, 0, 1], -36), ([1, -1, -1, 0, 0, 0, 2], -36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, -1, -1, 2, 0, 0, 0], -36), ([1, 0, -2, 1, 0, 0, 1], -36)]

theorem source33_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![-1, -1, 1, 0, 0, 1] (-12, 0)) = source33 := by
  decide +kernel

theorem source33_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source33 (momentValues f) = 0 := by
  rw [← source33_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source34 : Sparse := [([0, -2, -1, 1, 0, 2, 0], -36), ([0, -2, -1, 2, 0, 1, 0], 36), ([0, -2, 0, 1, 0, 1, 0], -36), ([0, -1, -2, 2, 0, 1, 0], -36), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 2, 0, 0, 0], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([1, -2, -1, 2, 0, 1, 0], 36), ([1, -2, 0, 1, 0, 1, 0], -36), ([1, -1, -2, 1, 0, 2, 0], -36), ([1, -1, -1, 0, 0, 2, 0], 36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, -1, -1, 2, 0, 0, 0], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, 0, -2, 1, 0, 1, 0], 36), ([1, 0, -1, 1, 0, 1, -1], -36)]

theorem source34_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![-1, -1, 1, 0, 1, 0] (-12, 0)) = source34 := by
  decide +kernel

theorem source34_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source34 (momentValues f) = 0 := by
  rw [← source34_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source35 : Sparse := [([0, -2, -1, 2, 1, 0, 0], -36), ([0, -1, -2, 1, 2, 0, 0], -36), ([0, -1, -2, 2, 1, 0, 0], 36), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, -1, 2, 0, 0, 0], -36), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, 0, -2, 1, 1, 0, 0], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 1, 1, 0, -1], -36), ([1, -2, -1, 1, 2, 0, 0], -36), ([1, -2, 0, 1, 1, 0, 0], 36), ([1, -1, -2, 2, 1, 0, 0], 36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 0, 2, 0, 0], 36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, -1, -1, 2, 0, 0, 0], -36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, 0, -2, 1, 1, 0, 0], -36), ([1, 0, -1, 1, 1, -1, 0], 36)]

theorem source35_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![-1, -1, 1, 1, 0, 0] (-12, 0)) = source35 := by
  decide +kernel

theorem source35_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source35 (momentValues f) = 0 := by
  rw [← source35_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source36 : Sparse := [([0, -2, 0, -1, 0, 1, 2], -36), ([0, -2, 0, -1, 0, 2, 1], -36), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, 0, -2, 0, 1, 2], -36), ([0, -1, 0, -2, 0, 2, 1], -36), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, 0, -1, -1, 1, 1], -36), ([1, -2, 0, 0, 0, 1, 1], 36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, 0, -1, 0, 0, 2], 36), ([1, -1, 0, -1, 0, 2, 0], 36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, 0, 0, -2, 0, 1, 1], 36)]

theorem source36_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![-1, 0, -1, 0, 1, 1] (-12, 0)) = source36 := by
  decide +kernel

theorem source36_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source36 (momentValues f) = 0 := by
  rw [← source36_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source37 : Sparse := [([0, -2, 0, -1, 1, 0, 2], -36), ([0, -2, 0, -1, 2, 0, 1], 36), ([0, -2, 0, 0, 1, 0, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, 0, -2, 2, 0, 1], -36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, -1, 2, 0, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, 0, 0, -1, 1, -1, 1], -36), ([1, -2, 0, -1, 2, 0, 1], 36), ([1, -2, 0, 0, 1, 0, 1], -36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, 0, -2, 1, 0, 2], -36), ([1, -1, 0, -1, 0, 0, 2], 36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 0, -1, 2, 0, 0], -36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, 0, -2, 1, 0, 1], 36)]

theorem source37_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![-1, 0, -1, 1, 0, 1] (-12, 0)) = source37 := by
  decide +kernel

theorem source37_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source37 (momentValues f) = 0 := by
  rw [← source37_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source38 : Sparse := [([0, -2, 0, -1, 2, 1, 0], -36), ([0, -1, 0, -2, 1, 2, 0], -36), ([0, -1, 0, -2, 2, 1, 0], 36), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, -1, 2, 0, 0], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, 0, -2, 1, 1, 0], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([1, -2, 0, -1, 1, 2, 0], -36), ([1, -2, 0, 0, 1, 1, 0], 36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, 0, -2, 2, 1, 0], 36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 0, -1, 0, 2, 0], 36), ([1, -1, 0, -1, 2, 0, 0], -36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, 0, 0, -2, 1, 1, 0], -36), ([1, 0, 0, -1, 1, 1, -1], 36)]

theorem source38_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![-1, 0, -1, 1, 1, 0] (-12, 0)) = source38 := by
  decide +kernel

theorem source38_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source38 (momentValues f) = 0 := by
  rw [← source38_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source39 : Sparse := [([0, -2, 0, 0, -1, 2, 1], -36), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, 0, 0, -2, 1, 2], -36), ([0, -1, 0, 0, -2, 2, 1], 36), ([0, -1, 0, 0, -1, 2, 0], -36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, 0, -1, -1, 1, 1], -36), ([0, 0, 0, 0, -2, 1, 1], -36), ([1, -2, 0, 0, -1, 1, 2], -36), ([1, -2, 0, 0, 0, 1, 1], 36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 0, 0, -2, 2, 1], 36), ([1, -1, 0, 0, -1, 0, 2], 36), ([1, -1, 0, 0, -1, 2, 0], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, 0, 0, -2, 1, 1], -36)]

theorem source39_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![-1, 0, 0, -1, 1, 1] (-12, 0)) = source39 := by
  decide +kernel

theorem source39_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source39 (momentValues f) = 0 := by
  rw [← source39_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
