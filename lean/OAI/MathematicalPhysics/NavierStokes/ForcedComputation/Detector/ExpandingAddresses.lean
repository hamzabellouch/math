import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LatticeArithmetic

namespace OAI

/-! Finite planar addresses for the expanding velocity detector. The
index is computed from a state and two bounded stacks; it never requires
executing the selected run. The next layer can enumerate every address. -/

namespace ForcedComputation.ExpandingDetector

structure Address (N B : ℕ) where
  state : Fin N
  left : Fin B
  right : Fin B
  deriving DecidableEq, Fintype

def Address.index {N B : ℕ} (a : Address N B) : ℕ :=
  1 + Lattice.pack B 1 a.left a.right a.state

theorem Address.index_positive {N B : ℕ} (a : Address N B) : 0 < a.index := by
  unfold index
  omega

theorem Address.index_le {N B : ℕ} (a : Address N B) : a.index ≤ N * B ^ 2 := by
  have hin : a.right.val + B * a.state.val < B * N :=
    Lattice.prepend_lt a.right.isLt a.state.isLt
  have hout := Lattice.prepend_lt a.left.isLt hin
  have he : a.index = 1 + (a.left.val + B * (a.right.val + B * a.state.val)) := by
    simp only [index, Lattice.pack, Lattice.stackBase, pow_one]
  rw [he]
  have he' : B * (B * N) = N * B ^ 2 := by ring
  rw [he'] at hout
  omega

theorem Address.index_injective (N B : ℕ) : Function.Injective (@Address.index N B) := by
  intro a b hab
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) a.left.isLt
  have hp : Lattice.pack B 1 a.left a.right a.state =
      Lattice.pack B 1 b.left b.right b.state := by
    unfold Address.index at hab
    omega
  have hl := congrArg (Lattice.leftStack B 1) hp
  have hr := congrArg (Lattice.rightStack B 1) hp
  have hq := congrArg (Lattice.stateDigit B 1) hp
  have haL : a.left.val < Lattice.stackBase B 1 := by simpa only [Lattice.stackBase, pow_one] using a.left.isLt
  have hbL : b.left.val < Lattice.stackBase B 1 := by simpa only [Lattice.stackBase, pow_one] using b.left.isLt
  have haR : a.right.val < Lattice.stackBase B 1 := by simpa only [Lattice.stackBase, pow_one] using a.right.isLt
  have hbR : b.right.val < Lattice.stackBase B 1 := by simpa only [Lattice.stackBase, pow_one] using b.right.isLt
  rw [Lattice.pack_left haL, Lattice.pack_left hbL] at hl
  rw [Lattice.pack_right hB haL haR, Lattice.pack_right hB hbL hbR] at hr
  rw [Lattice.pack_state hB haL haR, Lattice.pack_state hB hbL hbR] at hq
  cases a
  cases b
  simp only [Address.mk.injEq]
  exact ⟨Fin.ext hq, Fin.ext hl, Fin.ext hr⟩

def Address.finIndex {N B : ℕ} (a : Address N B) : Fin (N * B ^ 2) :=
  ⟨a.index - 1, by have := a.index_positive; have := a.index_le; omega⟩

theorem Address.finIndex_injective (N B : ℕ) :
    Function.Injective (@Address.finIndex N B) := by
  intro a b hab
  apply Address.index_injective N B
  have he := congrArg Fin.val hab
  have ha := a.index_positive
  have hb := b.index_positive
  change a.index - 1 = b.index - 1 at he
  omega

end ForcedComputation.ExpandingDetector

end OAI
