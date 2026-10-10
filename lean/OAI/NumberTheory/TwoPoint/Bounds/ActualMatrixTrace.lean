import OAI.NumberTheory.TwoPoint.Bounds.MatrixTraceSummation

namespace OAI

/-! The actual residue-model matrix moment at the canonical trace length. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_actual_matrix_trace (h : ℕ) (C W : ℝ)
    (hh : 0 < h) (hC : 0 ≤ C) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (_hP : ∀ j, P j ⊆ data.P),
      1 ≤ J → ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ j, primeHarmonicMass (P j) ≤ L ^ (2 : ℕ)) →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (Qmax : ℝ) ≤ Real.exp (100 * L + 1) → (Dmax : ℝ) ≤ Real.exp (2 * L) →
      (∀ dq ∈ data.pairs, dq.2 ≤ Qmax) →
      (∀ w : (j : Fin J) → P j, ∀ j, (∏ l ∈ univ.erase j, (w l).val) ≤ Dmax) →
      (∀ q ∈ Q, Squarefree q) → (∀ q ∈ Q, q.primeFactors ⊆ data.Q) →
      ∀ (u : ℕ → ℝ) (g : ℤ → ℝ) (K : ℝ)
        (eligible : ℕ → ℕ → Prop) (extra : ℕ → ℤ → Prop),
      (∀ q, 0 ≤ u q) → (∀ q, u q ≤ crudePaddingWeight q) →
      (∀ n, 1 ≤ (g n) ^ 2) → 1 ≤ K →
      (∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m) →
      (∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
        (extra d n ↔ extra d m)) →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (embed : V → ((j : Fin J) → P j) × ℤ), Function.Injective embed →
      (Fintype.card V : ℝ) ≤ Real.exp (106 * L) →
      ∀ (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop),
      (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
      let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
      let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
      let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
        L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
      (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
        (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
        (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [eventually_actual_column_trace h C W hh hC hW,
    eventually_ge_atTop (2 : ℝ)] with L hcolumn hL
  intro J M B H Y Qmax Dmax data hB P Q hP hJ hJM hVm hVM hVpoly hmass hPmass hQmass
    hM hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hqmax hdmax hsq hpool
    u g K eligible extra hu hub hg hK hgdep hextra V _ _ embed hinj hdim gate hallowed
  dsimp only
  have hkhi : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hk : 0 < ⌊L⌋₊ := by
    have ht := Nat.lt_floor_add_one L
    have hp : (0 : ℝ) < (⌊L⌋₊ : ℝ) := by linarith
    exact_mod_cast hp
  have hgzero (n : ℤ) : g n ≠ 0 := by
    intro he
    have hb := hg n
    rw [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hb
    linarith
  apply matrix_residue_trace_of_column_bounds data hB hP hprime hdisjoint
    ⌊L ^ (1 / 10 : ℝ)⌋₊
    (2 * ⌊L⌋₊ + ⌊L ^ (1 / 12 : ℝ)⌋₊ * ⌊L ^ (1 / 10 : ℝ)⌋₊)
    (by omega) (by omega) embed hinj Q u eligible g L K _ extra gate hsq hpool
    hgzero hgdep hextra hallowed (by positivity)
    (trace_dimension_allowance L ⌊L⌋₊ (Fintype.card V) (by linarith) hkhi hdim)
  exact hcolumn J M B H Y Qmax Dmax data hB P Q hP hJ hJM hVm hVM hVpoly hmass
    hPmass hQmass hM hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hqmax hdmax
    hsq hpool u g K eligible extra hu hub hg hK hgdep hextra V embed gate

end TwoPointCorrelations

end OAI
