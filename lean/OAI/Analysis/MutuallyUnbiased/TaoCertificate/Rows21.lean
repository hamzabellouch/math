import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source168 : Sparse := [([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -1, -2, 0, 0, 2], 9), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -1, -1, 0, 2], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, 0, -2, 0, 0, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 2, -1, -1, 0, 0, 0], 18), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 1, -2, -1, 0, 0, 2], 9), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 0, 0, 1], -9), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, -1, 2], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, 0, -2, 0, 0, 1], 9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 2, -1, -1, 0, 0, 0], 18)]

theorem source168_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source168 := by
  decide +kernel

theorem source168_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source168 (momentValues f) = 0 := by
  rw [← source168_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source169 : Sparse := [([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 1, -2], -9), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], 9), ([0, -1, 2, 0, 0, 0, -1], 9), ([0, -1, 2, 1, 0, 0, -2], -9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 1, 0, -1, -1], 9), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, 0, 0, -1], 9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9)]

theorem source169_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source169 := by
  decide +kernel

theorem source169_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source169 (momentValues f) = 0 := by
  rw [← source169_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source170 : Sparse := [([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 1, -2, 0, -1, 0, 2], 9), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -1, -1, -1, 0, 2], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -2, 0, 2], -9), ([0, 1, -1, 0, -1, -1, 2], 9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, 0, 0, -2, 0, 1], 9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], -9), ([1, 1, -1, -1, -1, 0, 2], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, 0, -2, 0, 2], -9), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 1, -2, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, 0, -2, 0, 1], 9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 2, -1, 0, -1, 0, 0], -18)]

theorem source170_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source170 := by
  decide +kernel

theorem source170_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source170 (momentValues f) = 0 := by
  rw [← source170_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source171 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 18), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 0, 1, 1, -2], 9), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, -1, 2, 0, 0, 0, -1], 9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, -1, 2, 0, 1, 0, -2], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([1, -2, 1, 0, 1, 0, 0], 18), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], -9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 0, 2, 0, -2], 9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 1, 1, 0, -2], 9), ([1, -1, 2, 0, 0, 0, -1], 9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9)]

theorem source171_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source171 := by
  decide +kernel

theorem source171_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source171 (momentValues f) = 0 := by
  rw [← source171_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source172 : Sparse := [([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 1, -2, 0, 0, -1, 2], 9), ([0, 1, -2, 1, 0, -1, 1], -9), ([0, 1, -1, -1, 0, -1, 2], -9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, 0, -1, -1, 2], -9), ([0, 1, -1, 0, 0, -2, 2], 9), ([0, 1, -1, 0, 1, -2, 1], -9), ([0, 1, 0, 0, -1, -1, 1], 9), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], -9), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -1, -1, 0, -1, 2], -9), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, -1, -1, 2], -9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -2, 1], -9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 0, 0, -2, 1], -9), ([1, 2, -1, 0, 0, -1, 0], -18)]

theorem source172_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source172 := by
  decide +kernel

theorem source172_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source172 (momentValues f) = 0 := by
  rw [← source172_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source173 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 18), ([0, -1, 0, 0, 0, 2, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 0, 0, 2, -2], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, -1, 2, 0, 0, 0, -1], 9), ([0, -1, 2, 0, 0, 1, -2], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -1, 0, 0, 0, 2, -1], 9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 1, -1, 0, 2, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 0, 1, 1, -2], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 0, 1, -2], 9), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], 9), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 1, 0, 0, 0, -1], 9)]

theorem source173_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source173 := by
  decide +kernel

theorem source173_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source173 (momentValues f) = 0 := by
  rw [← source173_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source174 : Sparse := [([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, 0, -2, -1, 0, 2], 9), ([0, 1, 0, -2, -1, 1, 1], -9), ([0, 1, 0, -2, 0, 0, 1], 9), ([0, 1, 0, -1, -2, 0, 2], 9), ([0, 1, 0, -1, -2, 1, 1], 9), ([0, 1, 0, 0, -2, 0, 1], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 1, -2, -1, 0, 1], 9), ([0, 1, 1, -1, -2, 0, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 2, 0, -1, -1, 0, 0], 18), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 1, -1, -1, -1, 0, 2], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, 0, -2, 0, 0, 1], 9), ([1, 1, 0, -1, -2, 1, 1], 9), ([1, 1, 0, -1, -1, -1, 2], 9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, 0, -2, 0, 1], 9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 1, -2, -1, 0, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 2, 0, -1, -1, 0, 0], 18)]

theorem source174_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source174 := by
  decide +kernel

theorem source174_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source174 (momentValues f) = 0 := by
  rw [← source174_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source175 : Sparse := [([0, -1, -1, 1, 2, 0, -1], -9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 0, 1, 1, 1, -2], -9), ([0, -1, 0, 1, 2, 0, -2], 9), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 0, 2, 1, 0, -2], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 1, 1, 0, -2], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], 9), ([1, -2, 0, 1, 1, 0, 0], -18), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 0, 2, 0, -1], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 0, 1, 1, 1, -2], -9), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 1, 1, 0, -2], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9)]

theorem source175_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source175 := by
  decide +kernel

theorem source175_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source175 (momentValues f) = 0 := by
  rw [← source175_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
