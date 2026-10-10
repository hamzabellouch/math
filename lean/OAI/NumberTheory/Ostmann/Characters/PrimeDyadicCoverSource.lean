import OAI.NumberTheory.Ostmann.Characters.PrimeDyadicCoverCost

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.PrimeDyadicCover
open Preliminaries

def sourceUpper (β L : ℝ) : ℕ := ⌊Real.exp (Real.exp (β*L))⌋₊

theorem sourceUpper_pos (β L : ℝ) : 1 ≤ sourceUpper β L := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa only [Nat.cast_one] using Real.one_le_exp (Real.exp_pos (β*L)).le

theorem log_sourceUpper_le (β L : ℝ) : Real.log (sourceUpper β L) ≤ Real.exp (β*L) := by
  have hp : (0:ℝ) < sourceUpper β L := by exact_mod_cast sourceUpper_pos β L
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_pos (Real.exp (β*L))).le)
  simpa only [Real.log_exp] using h

theorem le_sourceUpper_of_log {n : ℕ} (hn : 0 < n) {β L : ℝ}
    (hlog : Real.log n ≤ Real.exp (β*L)) : n ≤ sourceUpper β L := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have h := Real.exp_le_exp.mpr hlog
  simpa only [Real.exp_log (by exact_mod_cast hn : (0:ℝ)<n)] using h

theorem prime_shell_covers_of_le {Q N U : ℕ} (hQ : 0 < Q)
    (E : Finset (PrimeUpTo N)) (hmin : ∀ p ∈ E, Q ≤ p.val)
    (hmax : ∀ p ∈ E, p.val ≤ U) :
    ∀ p ∈ E, ∃ i : Index U, lower Q U i ≤ p.val ∧ p.val ≤ 2*lower Q U i := by
  intro p hp
  exact covers hQ (hmin p hp) (hmax p hp)

theorem source_shell_covers {Q N : ℕ} (hQ : 0 < Q)
    (E : Finset (PrimeUpTo N)) {β L : ℝ}
    (hmin : ∀ p ∈ E, Q ≤ p.val)
    (hmax : ∀ p ∈ E, Real.log p.val ≤ Real.exp (β*L)) :
    ∀ p ∈ E, ∃ i : Index (sourceUpper β L),
      lower Q (sourceUpper β L) i ≤ p.val ∧ p.val ≤ 2*lower Q (sourceUpper β L) i :=
  prime_shell_covers_of_le hQ E hmin (fun p hp =>
    le_sourceUpper_of_log (primeUpTo_prime p).pos (hmax p hp))

theorem source_shell_binary_cost_le_exp {N : ℕ}
    (E : List Bool → Finset (PrimeUpTo N)) (hE : ∀ p, 0 < primeShellMass (E p))
    {β c L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hZ : ∀ p, Real.exp (-c*L) ≤ primeShellMass (E p))
    (hlarge : Real.log costConstant ≤ L) (j : ℕ) (p : List Bool) :
    (BinaryPriorExposure.cost
      (fun p => shellResidueCost (J:=Index (sourceUpper β L)) (E p) (hE p)) j p:ℝ) ≤
      Real.exp ((β+c+1)*(2:ℝ)^j*L) := by
  have hh := binary_cost_le_exp
    (fun p => shellResidueCost (J:=Index (sourceUpper β L)) (E p) (hE p)) ((β+c+1)*L)
    (fun p => shell_cost_le_exp (E p) (hE p) hβ hL (log_sourceUpper_le β L)
      (hZ p) hlarge) j p
  convert hh using 1; congr 1; ring

theorem source_prime_binary_cost_le_exp {N Q : ℕ} [NeZero Q]
    (E : List Bool → Finset (PrimeUpTo N)) (hE : ∀ p, 0 < primeShellMass (E p))
    {β c L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hZ : ∀ p, Real.exp (-c*L) ≤ primeShellMass (E p))
    (hlarge : Real.log costConstant ≤ L) (j : ℕ) (p : List Bool) :
    (BinaryPriorExposure.cost
      (fun p => primeResidueCost (Q:=Q) (J:=Index (sourceUpper β L)) (E p) (hE p)) j p:ℝ) ≤
      Real.exp ((β+c+1)*(2:ℝ)^j*L) :=
  prime_binary_cost_le_exp E hE hβ hL (log_sourceUpper_le β L) hZ hlarge j p

end Ostmann.Characters.PrimeDyadicCover

end

end OAI
