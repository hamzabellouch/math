import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # The dimension bound for an eventually vanishing action filtration

Take successive spans of the images of a family of operators. If this
descending filtration ever vanishes, it vanishes by the dimension of the
space: an equality at one stage propagates to all later stages, so every
nonzero stage must strictly lower dimension.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def linearActionStep (D : I → Module.End K V) (W : Submodule K V) : Submodule K V :=
  ⨆ i, W.map (D i)

theorem linearActionStep_mono (D : I → Module.End K V) : Monotone (linearActionStep D) := by
  intro U W h
  exact iSup_mono fun _ => Submodule.map_mono h

def linearActionFiltration (D : I → Module.End K V) : ℕ → Submodule K V
  | 0 => ⊤
  | n + 1 => linearActionStep D (linearActionFiltration D n)

theorem linearActionFiltration_antitone (D : I → Module.End K V) :
    Antitone (linearActionFiltration D) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih => exact linearActionStep_mono D ih

theorem linearActionFiltration_constant (D : I → Module.End K V) {n : ℕ}
    (h : linearActionFiltration D (n + 1) = linearActionFiltration D n) (k : ℕ) :
    linearActionFiltration D (n + k) = linearActionFiltration D n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change linearActionStep D (linearActionFiltration D (n + k)) = _
    rw [ih]
    exact h

theorem linearActionFiltration_strict_of_nonzero
    (D : I → Module.End K V) (hnil : ∃ c, linearActionFiltration D c = ⊥)
    {n : ℕ} (hn : linearActionFiltration D n ≠ ⊥) :
    linearActionFiltration D (n + 1) < linearActionFiltration D n := by
  apply lt_of_le_of_ne (linearActionFiltration_antitone D (Nat.le_succ n))
  intro he
  obtain ⟨c, hc⟩ := hnil
  have hnc : linearActionFiltration D (n + c) = ⊥ :=
    eq_bot_iff.mpr ((linearActionFiltration_antitone D (Nat.le_add_left c n)).trans_eq hc)
  exact hn ((linearActionFiltration_constant D he c).symm.trans hnc)

theorem linearActionFiltration_finrank_eq_bot [Module.Finite K V]
    (D : I → Module.End K V) (hnil : ∃ c, linearActionFiltration D c = ⊥) :
    linearActionFiltration D (Module.finrank K V) = ⊥ := by
  by_contra hnonzero
  let d := Module.finrank K V
  have hn (n : ℕ) (hnd : n ≤ d) : linearActionFiltration D n ≠ ⊥ := by
    intro hn
    exact hnonzero (eq_bot_iff.mpr
      ((linearActionFiltration_antitone D hnd).trans_eq hn))
  have hr (n : ℕ) (hnd : n ≤ d) :
      Module.finrank K (linearActionFiltration D n) + n ≤ d := by
    induction n with
    | zero => simpa only [Nat.add_zero] using
        (Submodule.finrank_le (linearActionFiltration D 0))
    | succ n ih =>
      have hi := ih (Nat.le_of_succ_le hnd)
      have hs := Submodule.finrank_lt_finrank_of_lt
        (linearActionFiltration_strict_of_nonzero D hnil (hn n (by omega)))
      omega
  have hzero : Module.finrank K (linearActionFiltration D d) = 0 := by
    have hbound := hr d le_rfl
    omega
  exact hnonzero (Submodule.finrank_eq_zero.mp hzero)

end PolycyclicRecognition

end

end OAI
