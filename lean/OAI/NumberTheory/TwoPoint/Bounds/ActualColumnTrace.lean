import OAI.NumberTheory.TwoPoint.Bounds.ActualColumnCatalog
import OAI.NumberTheory.TwoPoint.Walks.ColumnTraceTotal
import OAI.NumberTheory.TwoPoint.Bounds.TraceParameterBudget
import OAI.NumberTheory.TwoPoint.Bounds.TraceErrorAbsorption

namespace OAI

/-! The four trace estimates applied to the actual matrix-path fiber.
All caps, singleton costs, padding majorants and witness lengths are discharged. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_actual_column_trace (h : ℕ) (C W : ℝ)
    (hh : 0 < h) (hC : 0 ≤ C) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (hP : ∀ j, P j ⊆ data.P),
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
        (embed : V → ((j : Fin J) → P j) × ℤ)
        (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
        (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * ⌊L⌋₊) → Bool),
      let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
      let D := 2 * ⌊L⌋₊ + ⌊L ^ (1 / 12 : ℝ)⌋₊ * s
      Real.exp (108 * L) * (∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs ⌊L⌋₊ x) forward,
        |prohibitedCenteredAverage data hB s D
          (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (actualColumnLabel data hP a.1)
          (actualColumnWeight data u eligible g L K extra forward a)|) ≤
        (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [eventually_prohibited_column_trace_total h C 0 (2 * C + 1) (4 * C + 402) W
      hC (by norm_num) (by positivity) (by positivity) hW,
    eventually_trace_slot_budgets C hC, eventually_trace_witness_budgets C hC,
    eventually_trace_absorption, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with
    L htrace hslots hwitness habs hL hlog
  intro J M B H Y Qmax Dmax data hB P Q hP hJ hJM hVm hVM hVpoly hmass hPmass hQmass
    hM hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hqmax hdmax hsq hpool
    u g K eligible extra hu hub hg hK hgdep hextra V _ _ embed gate x forward
  dsimp only
  let k := ⌊L⌋₊
  let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
  let n := ⌊L ^ (1 / 12 : ℝ)⌋₊
  let D := 2 * k + n * s
  let F := closedTraceFiber Q
    (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward
  let label (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    actualColumnLabel data hP a.1
  let base (p : ↥(data.P ∪ data.Q)) : Fin B :=
    ⟨0, (data.prime p).pos.trans_le (hB p.val p.property)⟩
  have hklo : L / 2 ≤ (k : ℝ) := hwitness.1
  have hkhi : (k : ℝ) ≤ L := hwitness.2.1
  have hk : 0 < k := by
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hR : 0 < 2 * k := by omega
  have hJC : (J : ℝ) ≤ C * Real.log L :=
    (show (J : ℝ) ≤ (J + M : ℕ) by exact_mod_cast Nat.le_add_right J M).trans hJM
  have hs := hslots k J M hkhi hJM
  obtain ⟨_, _, hspos, hslo, hnpos, hnhi, hKn, hKlo, hKhi, hDL, hcover⟩ := hwitness
  have hpairs (a) (ha : a ∈ F) (i) : (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs :=
    actualColumnCatalog_pairs data embed Q gate x forward a ha i
  have hchains (a) (ha : a ∈ F) :=
    actualColumnCatalog_chains data hprime hdisjoint embed Q gate x forward a ha
  have hb := htrace J M B s D k n (n / 8) H Y Qmax Dmax data hB P Q F hR forward label base
    (actualColumnWeight data u eligible g L K extra forward) (columnCrudeCap L)
    (Real.exp ((4 * C + 402) * L * (Real.log L) ^ 2)) 1 ⟨k, by omega⟩
    u (fun w i => eligible (columnTupleAtNat w i)) g K
    (fun w i => extra (columnTupleAtNat w i)) (actualColumnNext h forward) data.residueOrigin
    hJ hklo hkhi hJM hs.1 hs.2.1 hs.2.2 hP hVm hVM hVpoly hmass hPmass hQmass hM
    hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hpairs
    (fun a ha i => hqmax _ (hpairs a ha i))
    (fun a _ i j => hdmax (fun l => a.1 l i) j) (fun _ _ _ _ => rfl)
    (Real.exp_pos _).le le_rfl (by norm_num) (by simp)
    (fun a _ => columnCrudeCap_nonneg L (by linarith) a)
    (fun a _ z => actualColumnWeight_nonneg data u eligible g L K extra forward
      (by linarith) hu a z)
    (fun a _ z => actualColumnWeight_le_cap data u eligible g L K extra forward
      (by linarith) hu hub hg a z)
    (fun a ha => actualColumnCatalog_crude_cost data hP L C (by linarith) hlog hkhi hJC hM
      embed Q gate x forward a ha)
    (fun a _ ha => columnCrudeCap_small L (by linarith) a ha)
    (fun a _ z t ht => actualColumnWeight_independent data hP u eligible g L K extra forward
      hsq hpool hgdep hextra a z t ht)
    (fun a _ z hz => actualColumnWeight_padding data u eligible g L K extra forward a z hz)
    le_rfl (fun a _ ha => hcover J _ hJC ha) hDL hnpos hnhi hKn hKlo hKhi hh hspos hslo
    (fun a ha => (hchains a ha).1) (fun a ha => (hchains a ha).2) (by linarith) hu
    (fun a _ z => actualColumnWeight_le_retained data u eligible g L K extra forward
      (by linarith) hu a z)
  exact habs J k K W _ hJ (by omega) hK hW hb

end TwoPointCorrelations

end OAI
