import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerTable
import OAI.Combinatorics.ContingencyTables.Model
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # Unique bin and offset encoding of free integer entries -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators

def gridCoordinateFin (K : ℕ) : Set.Icc (0 : ℤ) ((K : ℤ) - 1) ≃ Fin K where
  toFun z := ⟨z.val.toNat, by
    have hcast : (z.val.toNat : ℤ) = z.val := Int.toNat_of_nonneg z.property.1
    have hhi := z.property.2
    omega⟩
  invFun v := ⟨(v.val : ℤ), by constructor <;> omega⟩
  left_inv z := by
    apply Subtype.ext
    exact Int.toNat_of_nonneg z.property.1
  right_inv v := by
    apply Fin.ext
    exact Int.toNat_natCast _

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q : ℕ}

abbrev Offset (w : I × J → ℕ) := ∀ p, Fin (w p)
abbrev FreeBox (w : I × J → ℕ) (K : ℕ) := ∀ p, Fin (K * w p)

def trialBoxEquiv (e : I × J ≃ Fin q) (w : I × J → ℕ) (K : ℕ) :
    Grid (I := Fin q) K × Offset w ≃ FreeBox w K where
  toFun t p := finProdFinEquiv (gridCoordinateFin K (t.1 (e p)), t.2 p)
  invFun z :=
    (fun j => (gridCoordinateFin K).symm
      (((finProdFinEquiv : Fin K × Fin (w (e.symm j)) ≃ Fin (K * w (e.symm j))).symm
        (z (e.symm j))).1),
     fun p => ((finProdFinEquiv : Fin K × Fin (w p) ≃ Fin (K * w p)).symm (z p)).2)
  left_inv t := by
    rcases t with ⟨a, o⟩
    apply Prod.ext
    · funext j
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · funext p
      simp only [Equiv.symm_apply_apply]
  right_inv z := by
    funext p
    simp only [Equiv.apply_symm_apply]
    have hb : ((finProdFinEquiv : Fin K × Fin (w (e.symm (e p))) ≃
        Fin (K * w (e.symm (e p)))).symm (z (e.symm (e p)))).1 =
        ((finProdFinEquiv : Fin K × Fin (w p) ≃ Fin (K * w p)).symm (z p)).1 := by
      apply Fin.ext
      change (z (e.symm (e p))).val / w (e.symm (e p)) = (z p).val / w p
      rw [Equiv.symm_apply_apply]
    rw [hb]
    exact finProdFinEquiv.apply_symm_apply (z p)

omit [Fintype I] [Fintype J] in
theorem trialBoxEquiv_val (e : I × J ≃ Fin q) (w : I × J → ℕ) (K : ℕ)
    (a : Grid (I := Fin q) K) (o : Offset w) (p : I × J) :
    (trialBoxEquiv e w K (a, o) p).val = (o p).val + w p * (corner a (e p)).toNat := rfl

def integerWidth (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (p : I × J) : ℕ :=
  min (R (some p.1)) (P (some p.2)) / d ^ 8

omit [Fintype I] [Fintype J] in
theorem integerWidth_pos (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j) (p : I × J) :
    0 < integerWidth R P d p :=
  DenseAffine.dense_width_positive d _ hd (le_min (hR _) (hP _))

omit [Fintype I] [Fintype J] in
theorem free_entry_lt_box (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (p : I × J) (z : ℕ) (hz : z ≤ min (R (some p.1)) (P (some p.2))) :
    z < (4 * d ^ 8) * integerWidth R P d p := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hb := (DenseAffine.dense_width_bounds d (min (R (some p.1)) (P (some p.2))) hd
    (le_min (hR _) (hP _))).1
  have hs : min (R (some p.1)) (P (some p.2)) ≤
      (2 * d ^ 8) * integerWidth R P d p := by
    have h := (div_le_iff₀ (show (0 : ℝ) < 2 * (d : ℝ) ^ 8 by positivity)).mp hb
    have h' : min (R (some p.1)) (P (some p.2)) ≤
        integerWidth R P d p * (2 * d ^ 8) := by exact_mod_cast h
    simpa only [Nat.mul_comm] using h'
  have hw := integerWidth_pos R P d hd hR hP p
  have hd8 : 0 < d ^ 8 := pow_pos (show 0 < d by omega) _
  nlinarith [Nat.mul_pos hd8 hw]

def tableFreeBox (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (X : Table R P) : FreeBox (integerWidth R P d) (4 * d ^ 8) := fun p =>
  ⟨X.val (some p.1) (some p.2), free_entry_lt_box R P d hd hR hP p _ (by
    apply le_min
    · exact entry_le_row X.property _ _
    · rw [← X.property.2 (some p.2)]
      exact Finset.single_le_sum (f := fun i : Option I => X.val i (some p.2))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some p.1)))⟩

end ContingencyTables.GridBoundary

end OAI
