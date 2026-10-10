import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Multiplicities in a rational circle grid

An integer-periodic predicate samples a rational step `a / h` on precisely
`h / gcd h a` different points, each with multiplicity `gcd h a`.
The proof reindexes actual finite types using division with remainder and the
permutation given by multiplication by a coprime numerator.
-/

namespace QuantitativeVanDerWaerden

/-- Multiplication by a coprime natural number permutes the finite residues. -/
noncomputable def mulModGridEquiv (s b : ℕ) (hs : 0 < s)
    (hcop : Nat.gcd s b = 1) : Equiv.Perm (Fin s) := by
  let f : Fin s → Fin s := fun x => ⟨x.val * b % s, Nat.mod_lt _ hs⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have hm : Nat.ModEq s (x.val * b) (y.val * b) := congrArg Fin.val hxy
    exact (Nat.ModEq.cancel_right_of_coprime hcop hm).eq_of_lt_of_lt x.isLt y.isLt
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, rfl⟩)

@[simp] theorem mulModGridEquiv_val (s b : ℕ) (hs : 0 < s)
    (hcop : Nat.gcd s b = 1) (x : Fin s) :
    (mulModGridEquiv s b hs hcop x).val = x.val * b % s := rfl

/-- An integer-periodic predicate is unchanged when a rational numerator is
reduced modulo its positive denominator. -/
theorem periodic_predicate_div_mod (P : ℝ → Prop)
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x)
    (y : ℝ) (n s : ℕ) (hs : 0 < s) :
    P (y + (n : ℝ) / s) ↔ P (y + ((n % s : ℕ) : ℝ) / s) := by
  have hsR : (s : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) = ((n % s : ℕ) : ℝ) + (s : ℝ) * (n / s : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n s).symm
  have heq : y + (n : ℝ) / s =
      (y + ((n % s : ℕ) : ℝ) / s) + ((n / s : ℕ) : ℝ) := by
    rw [hn]
    field_simp
    ring
  rw [heq]
  simpa only [Int.cast_natCast] using
    hperiod (y + ((n % s : ℕ) : ℝ) / s) (n / s : ℕ)

/-- A full block with a coprime step visits every point of its uniform grid
once, for every integer-periodic predicate. -/
theorem card_coprime_rational_grid_periodic (s b : ℕ) (hs : 0 < s)
    (hcop : Nat.gcd s b = 1) (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    Fintype.card {j : Fin s // P (y + (j.val : ℝ) * b / s)} =
      Fintype.card {j : Fin s // P (y + (j.val : ℝ) / s)} := by
  apply Fintype.card_congr
  apply (mulModGridEquiv s b hs hcop).subtypeEquiv
  intro j
  simpa only [mulModGridEquiv_val, Nat.cast_mul] using
    periodic_predicate_div_mod P hperiod y (j.val * b) s hs

/-- Repeating the rational step for `d` full denominator blocks multiplies
every periodic-predicate count by `d`. -/
theorem card_repeated_rational_grid_periodic (d s b : ℕ) (hs : 0 < s)
    (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    Fintype.card {z : Fin (d * s) // P (y + (z.val : ℝ) * b / s)} =
      d * Fintype.card {j : Fin s // P (y + (j.val : ℝ) * b / s)} := by
  let Q : Fin s → Prop := fun j => P (y + (j.val : ℝ) * b / s)
  let split : {p : Fin d × Fin s // Q p.2} ≃ Fin d × {j : Fin s // Q j} :=
    { toFun := fun p => (p.val.1, ⟨p.val.2, p.property⟩)
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : ∀ p : Fin d × Fin s,
      Q p.2 ↔ P (y + ((finProdFinEquiv p).val : ℝ) * b / s) := by
    intro p
    change P (y + (p.2.val : ℝ) * b / s) ↔
      P (y + ((p.2.val + s * p.1.val : ℕ) : ℝ) * b / s)
    have hsR : (s : ℝ) ≠ 0 := by positivity
    have heq : y + ((p.2.val + s * p.1.val : ℕ) : ℝ) * b / s =
        (y + (p.2.val : ℝ) * b / s) + ((p.1.val * b : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [heq]
    simpa only [Int.cast_natCast] using
      (hperiod (y + (p.2.val : ℝ) * b / s) (p.1.val * b : ℕ)).symm
  calc
    _ = Fintype.card {p : Fin d × Fin s // Q p.2} :=
      (Fintype.card_congr (finProdFinEquiv.subtypeEquiv hp)).symm
    _ = Fintype.card (Fin d × {j : Fin s // Q j}) := Fintype.card_congr split
    _ = _ := by rw [Fintype.card_prod, Fintype.card_fin]

/-- Exact multiplicity of the reduced rational grid. This applies to any
predicate invariant under integer translation, including circle arcs. -/
theorem card_rational_grid_periodic (h a : ℕ) (hh : 0 < h)
    (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    Fintype.card {z : Fin h // P (y + (z.val : ℝ) * a / h)} =
      Nat.gcd h a * Fintype.card {j : Fin (h / Nat.gcd h a) //
        P (y + (j.val : ℝ) / (h / Nat.gcd h a : ℕ))} := by
  let d := Nat.gcd h a
  let s := h / d
  let b := a / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left a hh
  have hs : 0 < s := Nat.div_gcd_pos_of_pos_left a hh
  have hcop : Nat.gcd s b = 1 := Nat.gcd_div_gcd_div_gcd_of_pos_left hh
  have hfactor : h = d * s := (Nat.mul_div_cancel' (Nat.gcd_dvd_left h a)).symm
  have afactor : a = d * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right h a)).symm
  have hratio (z : ℕ) : (z : ℝ) * a / h = (z : ℝ) * b / s := by
    rw [hfactor, afactor]
    push_cast
    have hdR : (d : ℝ) ≠ 0 := by positivity
    have hsR : (s : ℝ) ≠ 0 := by positivity
    field_simp
  calc
    _ = Fintype.card {z : Fin (d * s) // P (y + (z.val : ℝ) * b / s)} := by
      apply Fintype.card_congr
      apply (finCongr hfactor).subtypeEquiv
      intro z
      change P (y + (z.val : ℝ) * a / h) ↔ P (y + (z.val : ℝ) * b / s)
      rw [hratio]
    _ = d * Fintype.card {j : Fin s // P (y + (j.val : ℝ) * b / s)} :=
      card_repeated_rational_grid_periodic d s b hs P hperiod y
    _ = _ := by rw [card_coprime_rational_grid_periodic s b hs hcop P hperiod y]

/-- Finset-filter form of the exact rational-grid multiplicity formula. -/
theorem card_filter_rational_grid_periodic (h a : ℕ) (hh : 0 < h)
    (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    (Finset.univ.filter (fun z : Fin h => P (y + (z.val : ℝ) * a / h))).card =
      Nat.gcd h a * (Finset.univ.filter (fun j : Fin (h / Nat.gcd h a) =>
        P (y + (j.val : ℝ) / (h / Nat.gcd h a : ℕ)))).card := by
  simpa only [Fintype.card_subtype] using
    card_rational_grid_periodic h a hh P hperiod y

end QuantitativeVanDerWaerden

end OAI
