import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Exact independent residue averages from the Chinese remainder theorem -/

namespace Ostmann

open scoped BigOperators

/-- CRT on the actual unit residue classes, including prime-square moduli. -/
noncomputable def crtUnitEquiv {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j))) :
    (ZMod (∏ i, a i))ˣ ≃* (∀ i, (ZMod (a i))ˣ) :=
  (Units.mapEquiv (ZMod.prodEquivPi a hc).toMulEquiv).trans MulEquiv.piUnits

theorem crtUnitEquiv_apply {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (u : (ZMod (∏ i, a i))ˣ) (i : I) :
    crtUnitEquiv a hc u i = Units.map
      ((ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i))).toMonoidHom) u := by
  apply Units.ext
  change ZMod.prodEquivPi a hc (u : ZMod (∏ i, a i)) i = _
  exact ZMod.prodEquivPi_apply a hc u i

/-- Uniform CRT unit residues factor exactly into independent local uniform
unit residues; no equidistribution hypothesis is used in this finite step. -/
theorem crt_unit_average {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (f : ∀ i, (ZMod (a i))ˣ → ℝ) :
    (Fintype.card (ZMod (∏ i, a i))ˣ : ℝ)⁻¹ *
      (∑ u : (ZMod (∏ i, a i))ˣ, ∏ i, f i (crtUnitEquiv a hc u i)) =
    ∏ i, (Fintype.card (ZMod (a i))ˣ : ℝ)⁻¹ * ∑ u : (ZMod (a i))ˣ, f i u := by
  classical
  have hsum := (crtUnitEquiv a hc).toEquiv.sum_comp (fun u => ∏ i, f i (u i))
  change (∑ u : (ZMod (∏ i, a i))ˣ, ∏ i, f i (crtUnitEquiv a hc u i)) =
    (∑ u : ∀ i, (ZMod (a i))ˣ, ∏ i, f i (u i)) at hsum
  rw [hsum, Fintype.card_congr (crtUnitEquiv a hc).toEquiv, Fintype.card_pi]
  rw [← Fintype.prod_sum]
  simp only [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Ostmann

end OAI
