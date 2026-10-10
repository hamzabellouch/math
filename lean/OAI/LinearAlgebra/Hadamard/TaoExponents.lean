import OAI.LinearAlgebra.Hadamard.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OAI

/-! Cubic exponent symmetries of Tao’s order-six complex Hadamard matrix. -/

namespace HadamardSix.TaoSymmetry

abbrev I := Fin 6
abbrev Exponents := I → I → ZMod 3

def exponent : Exponents :=
  fun i j => (HadamardSix.taoExponent i j : ZMod 3)

def RowSymmetry (t : Exponents) (p : Equiv.Perm I) : Prop :=
  ∃ (q : Equiv.Perm I) (s : (ZMod 3)ˣ) (u v : I → ZMod 3),
    ∀ i j, t (p i) (q j) = (s : ZMod 3) * t i j + u i + v j

theorem rowSymmetry_one (t : Exponents) : RowSymmetry t 1 := by
  refine ⟨1, 1, fun _ => 0, fun _ => 0, ?_⟩
  intro i j
  simp

theorem rowSymmetry_mul {t : Exponents} {p p' : Equiv.Perm I}
    (hp : RowSymmetry t p) (hp' : RowSymmetry t p') :
    RowSymmetry t (p * p') := by
  obtain ⟨q, s, u, v, h⟩ := hp
  obtain ⟨q', s', u', v', h'⟩ := hp'
  refine ⟨q * q', s * s',
    (fun i => (s : ZMod 3) * u' i + u (p' i)),
    (fun j => (s : ZMod 3) * v' j + v (q' j)), ?_⟩
  intro i j
  change t (p (p' i)) (q (q' j)) =
    ((s * s' : (ZMod 3)ˣ) : ZMod 3) * t i j +
      ((s : ZMod 3) * u' i + u (p' i)) +
      ((s : ZMod 3) * v' j + v (q' j))
  rw [h, h']
  simp only [Units.val_mul]
  ring

def symmetryMonoid (t : Exponents) : Submonoid (Equiv.Perm I) where
  carrier := RowSymmetry t
  one_mem' := rowSymmetry_one t
  mul_mem' := fun hp hp' => rowSymmetry_mul hp hp'

def columnMap : Fin 5 → I → I :=
  ![![1, 0, 5, 4, 3, 2],
    ![4, 5, 3, 2, 0, 1],
    ![5, 2, 1, 4, 3, 0],
    ![1, 0, 3, 2, 5, 4],
    ![2, 5, 0, 4, 3, 1]]

theorem columnMap_bijective (a : Fin 5) :
    Function.Bijective (columnMap a) := by
  fin_cases a <;> decide

noncomputable def columnPerm (a : Fin 5) : Equiv.Perm I :=
  Equiv.ofBijective (columnMap a) (columnMap_bijective a)

def rowPhase : Fin 5 → I → ZMod 3 :=
  ![![0, 0, 1, 2, 2, 1],
    ![0, 2, 2, 1, 0, 1],
    ![0, 1, 2, 2, 1, 0],
    ![0, 0, 1, 2, 2, 1],
    ![0, 1, 0, 1, 2, 2]]

def columnPhase : Fin 5 → I → ZMod 3 :=
  ![![0, 0, 1, 2, 2, 1],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]]

theorem adjacent_certificate (a : Fin 5) :
    ∀ i j,
      exponent (Equiv.swap a.castSucc a.succ i) (columnMap a j) =
      (-1 : ZMod 3) * exponent i j + rowPhase a i + columnPhase a j := by
  fin_cases a <;> decide

theorem adjacent_symmetry (a : Fin 5) :
    RowSymmetry exponent (Equiv.swap a.castSucc a.succ) := by
  refine ⟨columnPerm a, -1, rowPhase a, columnPhase a, ?_⟩
  intro i j
  change exponent (Equiv.swap a.castSucc a.succ i) (columnMap a j) =
    (-1 : ZMod 3) * exponent i j + rowPhase a i + columnPhase a j
  exact adjacent_certificate a i j

theorem every_row_permutation (p : Equiv.Perm I) :
    RowSymmetry exponent p := by
  have hclosure :
      Submonoid.closure
        (Set.range fun a : Fin 5 => Equiv.swap a.castSucc a.succ) ≤
      symmetryMonoid exponent := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨a, rfl⟩
    exact adjacent_symmetry a
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hclosure
  exact hclosure (by simp)

end HadamardSix.TaoSymmetry

end OAI
