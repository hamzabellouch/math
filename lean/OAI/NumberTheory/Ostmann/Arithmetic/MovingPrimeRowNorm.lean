import OAI.NumberTheory.Ostmann.Characters.TupleCRTFourier
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # The exact CRT row norm used by the giant-only transfer -/

namespace Ostmann
open scoped Classical BigOperators

/-- Both the giant's bounded row and the exact compensation-prime energies
enter multiplicatively, at their actual modulus sizes. -/
theorem moving_crt_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, NeZero (p j)] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ j, ZMod (p j) → ℂ)
    (henergy : ∀ j, (∑ x, ‖g j x‖ ^ 2) ≤ (p j : ℝ)) :
    (∑ x : ZMod (∏ j, p j), ‖tupleCRTFunction p hc g x‖ ^ 2) ≤ (∏ j, p j : ℕ) := by
  have he := (ZMod.prodEquivPi p hc).toEquiv.sum_comp
    (fun x : ∀ j, ZMod (p j) => ∏ j, ‖g j (x j)‖ ^ 2)
  change (∑ x : ZMod (∏ j, p j), ∏ j,
    ‖g j (ZMod.prodEquivPi p hc x j)‖ ^ 2) = _ at he
  calc
    _ = ∑ x : ∀ j, ZMod (p j), ∏ j, ‖g j (x j)‖ ^ 2 := by
      simpa only [tupleCRTFunction, norm_prod, Finset.prod_pow] using he
    _ = ∏ j, ∑ x : ZMod (p j), ‖g j x‖ ^ 2 := (Fintype.prod_sum (fun j (x : ZMod (p j)) => ‖g j x‖ ^ 2)).symm
    _ ≤ ∏ j, (p j : ℝ) := Finset.prod_le_prod₀
      (fun j _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (fun j _ => henergy j)
    _ = _ := (Nat.cast_prod _ _).symm

/-- The cofactor and outside-denominator units merely permute each local row. -/
theorem moving_crt_scaled_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ j, ZMod (p j) → ℂ) (u : ∀ j, (ZMod (p j))ˣ)
    (henergy : ∀ j, (∑ x, ‖g j x‖ ^ 2) ≤ (p j : ℝ)) :
    (∑ x : ZMod (∏ j, p j),
      ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x)) x‖ ^ 2) ≤
        (∏ j, p j : ℕ) := by
  apply moving_crt_row_energy p hc
  intro j
  have he := Equiv.sum_comp (Equiv.mulLeft₀ (u j : ZMod (p j)) (Units.ne_zero _))
    (fun x => ‖g j x‖ ^ 2)
  exact he.trans_le (henergy j)

/-- This is the counting row indexed by `Fin modulus` in the finite transfer. -/
theorem moving_crt_fin_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ j, ZMod (p j) → ℂ) (u : ∀ j, (ZMod (p j))ˣ)
    (henergy : ∀ j, (∑ x, ‖g j x‖ ^ 2) ≤ (p j : ℝ)) :
    (∑ x : Fin (∏ j, p j),
      ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x))
        (ZMod.finEquiv (∏ j, p j) x)‖ ^ 2) ≤ (∏ j, p j : ℕ) := by
  have he := (ZMod.finEquiv (∏ j, p j)).toEquiv.sum_comp
    (fun x => ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x)) x‖ ^ 2)
  change (∑ x : Fin (∏ j, p j),
    ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x))
      (ZMod.finEquiv (∏ j, p j) x)‖ ^ 2) = _ at he
  exact he.trans_le (moving_crt_scaled_row_energy p hc g u henergy)

/-- The giant factor is bounded by one; all other factors are the paper's
normalized compensation transforms. No bound on an individual compensation
transform is required. -/
theorem moving_crt_compensation_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (giant : J)
    (g : ∀ j, ZMod (p j) → ℂ) (u : ∀ j, (ZMod (p j))ˣ)
    (S : ∀ j, Finset (ZMod (p j)))
    (hg : ∀ x, ‖g giant x‖ ≤ 1)
    (hregular : ∀ j, j ≠ giant → g j = normalizedResidueTransform (S j))
    (hS : ∀ j, j ≠ giant → (S j).Nonempty)
    (hSp : ∀ j, j ≠ giant → (S j).card < p j) :
    (∑ x : Fin (∏ j, p j),
      ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x))
        (ZMod.finEquiv (∏ j, p j) x)‖ ^ 2) ≤ (∏ j, p j : ℕ) := by
  apply moving_crt_fin_row_energy p hc g u
  intro j
  by_cases hj : j = giant
  · subst j
    calc
      (∑ x, ‖g giant x‖ ^ 2) ≤ ∑ _x : ZMod (p giant), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        nlinarith [hg x, norm_nonneg (g giant x)]
      _ = _ := by simp
  · rw [hregular j hj, normalizedResidueTransform_energy (S j) (hS j hj) (hSp j hj)]

private theorem finEquiv_eq_natCast (M : ℕ) [NeZero M] (x : Fin M) :
    ZMod.finEquiv M x = (x.val : ZMod M) := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
    apply Fin.ext
    exact (Nat.mod_eq_of_lt x.isLt).symm

/-- The actual extracted row `G_P(t/d)`: each local argument includes the
outside denominator and the cofactor of that prime. Their inverses are units,
so the exact counting energy remains at most the modulus. -/
theorem moving_compensation_fourier_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (giant : J)
    (g : ∀ j, ZMod (p j) → ℂ) (S : ∀ j, Finset (ZMod (p j)))
    (hg : ∀ x, ‖g giant x‖ ≤ 1)
    (hregular : ∀ j, j ≠ giant → g j = normalizedResidueTransform (S j))
    (hS : ∀ j, j ≠ giant → (S j).Nonempty)
    (hSp : ∀ j, j ≠ giant → (S j).card < p j)
    (D : ℕ) (hD : ∀ j, D.Coprime (p j)) :
    (∑ x : Fin (∏ j, p j), ‖∏ j,
      g j ((x.val : ZMod (p j)) / ((D * tupleCofactor p j : ℕ) : ZMod (p j)))‖ ^ 2) ≤
      (∏ j, p j : ℕ) := by
  let u : ∀ j, (ZMod (p j))ˣ := fun j =>
    (ZMod.unitOfCoprime (D * tupleCofactor p j)
      ((hD j).mul_left (tupleCofactor_coprime p hc j)))⁻¹
  have hh := moving_crt_compensation_row_energy p hc giant g u S hg hregular hS hSp
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  unfold tupleCRTFunction
  apply Finset.prod_congr rfl
  intro j _
  simp only [u, Units.val_inv_eq_inv_val, ZMod.coe_unitOfCoprime,
    finEquiv_eq_natCast, map_natCast, Pi.natCast_apply, div_eq_mul_inv]
  rw [mul_comm]

end Ostmann

end OAI
