import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source40 : Sparse := [([0, -2, 0, 0, 1, -1, 2], -36), ([0, -2, 0, 0, 1, 0, 1], -36), ([0, -2, 0, 0, 2, -1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, 0, 0, -1, 2], -36), ([0, -1, 0, 0, 1, -2, 2], -36), ([0, -1, 0, 0, 2, -2, 1], -36), ([0, -1, 0, 0, 2, -1, 0], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 0, 0, 1, -2, 1], -36), ([1, -2, 0, 0, 1, 0, 1], -36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, -1, 0, 0, 0, -1, 2], -36), ([1, -1, 0, 0, 2, -1, 0], -36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, 0, 0, 0, 1, -2, 1], -36)]

theorem source40_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![-1, 0, 0, 1, -1, 1] (-12, 0)) = source40 := by
  decide +kernel

theorem source40_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source40 (momentValues f) = 0 := by
  rw [← source40_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source41 : Sparse := [([0, -2, 0, 0, 1, 2, -1], -36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, 0, 0, 2, -1], -36), ([0, -1, 0, 0, 1, 2, -2], 36), ([0, -1, 0, 0, 2, 1, -2], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 0, 0, 1, 1, -2], -36), ([1, -2, 0, 0, 1, 1, 0], 36), ([1, -2, 0, 0, 2, 1, -1], -36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, -1, 0, 0, 0, 2, -1], -36), ([1, -1, 0, 0, 1, 2, -2], 36), ([1, -1, 0, 0, 2, 0, -1], 36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 0, 0, 0, 1, 1, -2], -36)]

theorem source41_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![-1, 0, 0, 1, 1, -1] (-12, 0)) = source41 := by
  decide +kernel

theorem source41_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source41 (momentValues f) = 0 := by
  rw [← source41_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source42 : Sparse := [([0, -2, 0, 1, -1, 0, 2], -36), ([0, -2, 0, 1, 0, 0, 1], -36), ([0, -2, 0, 2, -1, 0, 1], 36), ([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 0, 2, -2, 0, 1], -36), ([0, -1, 0, 2, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, 0, -1, 1, -1, 0, 1], -36), ([1, -2, 0, 1, 0, 0, 1], -36), ([1, -2, 0, 2, -1, 0, 1], 36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, 0, 0, -1, 0, 2], 36), ([1, -1, 0, 1, -2, 0, 2], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 2, -1, 0, 0], -36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, 0, 0, 1, -2, 0, 1], 36), ([1, 0, 0, 1, -1, -1, 1], -36)]

theorem source42_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![-1, 0, 1, -1, 0, 1] (-12, 0)) = source42 := by
  decide +kernel

theorem source42_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source42 (momentValues f) = 0 := by
  rw [← source42_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source43 : Sparse := [([0, -2, 0, 1, -1, 2, 0], -36), ([0, -2, 0, 1, 0, 1, 0], -36), ([0, -2, 0, 2, -1, 1, 0], -36), ([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 0, 0, -1, 2, 0], -36), ([0, -1, 0, 1, -2, 2, 0], -36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 0, 2, -2, 1, 0], -36), ([0, -1, 0, 2, -1, 0, 0], -36), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, 0, 1, -2, 1, 0], -36), ([0, 0, 0, 1, -1, 1, -1], -36), ([1, -2, 0, 1, 0, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, 0, 0, -1, 2, 0], -36), ([1, -1, 0, 2, -1, 0, 0], -36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, 0, 0, 1, -2, 1, 0], -36)]

theorem source43_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![-1, 0, 1, -1, 1, 0] (-12, 0)) = source43 := by
  decide +kernel

theorem source43_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source43 (momentValues f) = 0 := by
  rw [← source43_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source44 : Sparse := [([0, -2, 0, 1, 0, -1, 2], 36), ([0, -2, 0, 1, 0, 0, 1], -36), ([0, -2, 0, 2, 0, -1, 1], -36), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, 0, 0, 0, -1, 2], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -2, 2], -36), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, 0, -1, 1, 0, -1, 1], -36), ([1, -2, 0, 1, 0, -1, 2], 36), ([1, -2, 0, 1, 0, 0, 1], -36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, -1, 0, 0, 0, -1, 2], -36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 0, 2, 0, -2, 1], -36), ([1, -1, 0, 2, 0, -1, 0], 36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 0, 0, 1, 0, -2, 1], 36)]

theorem source44_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![-1, 0, 1, 0, -1, 1] (-12, 0)) = source44 := by
  decide +kernel

theorem source44_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source44 (momentValues f) = 0 := by
  rw [← source44_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source45 : Sparse := [([0, -2, 0, 1, 0, 1, 0], -36), ([0, -2, 0, 1, 0, 2, -1], 36), ([0, -2, 0, 2, 0, 1, -1], -36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 0, 0, 2, -1], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, 0, 2, -2], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, 0, 0, 1, -1, 1, -1], -36), ([1, -2, 0, 1, 0, 1, 0], -36), ([1, -2, 0, 1, 0, 2, -1], 36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, -1, 0, 0, 0, 2, -1], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 0, 2, 0, 0, -1], 36), ([1, -1, 0, 2, 0, 1, -2], -36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, 0, 1, 0, 1, -2], 36)]

theorem source45_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![-1, 0, 1, 0, 1, -1] (-12, 0)) = source45 := by
  decide +kernel

theorem source45_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source45 (momentValues f) = 0 := by
  rw [← source45_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source46 : Sparse := [([0, -2, 0, 1, 2, -1, 0], -36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 0, 0, 2, -1, 0], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 0, 1, 2, -2, 0], 36), ([0, -1, 0, 2, 1, -2, 0], -36), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, 0, 1, 1, -2, 0], -36), ([0, 0, 0, 1, 1, -1, -1], -36), ([1, -2, 0, 1, 1, 0, 0], 36), ([1, -2, 0, 2, 1, -1, 0], -36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 0, 0, 2, -1, 0], -36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 0, 1, 2, -2, 0], 36), ([1, -1, 0, 2, 0, -1, 0], 36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, 0, 1, 1, -2, 0], -36)]

theorem source46_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![-1, 0, 1, 1, -1, 0] (-12, 0)) = source46 := by
  decide +kernel

theorem source46_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source46 (momentValues f) = 0 := by
  rw [← source46_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source47 : Sparse := [([0, -2, 0, 1, 2, 0, -1], -36), ([0, -2, 0, 2, 1, 0, -1], -36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 0, 1, 2, 0, -2], -36), ([0, -1, 0, 2, 1, 0, -2], -36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, 0, 1, 1, -1, -1], -36), ([1, -2, 0, 1, 1, 0, 0], 36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, -1, 0, 0, 2, 0, -1], 36), ([1, -1, 0, 2, 0, 0, -1], 36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, 0, 0, 1, 1, 0, -2], 36)]

theorem source47_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![-1, 0, 1, 1, 0, -1] (-12, 0)) = source47 := by
  decide +kernel

theorem source47_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source47 (momentValues f) = 0 := by
  rw [← source47_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
