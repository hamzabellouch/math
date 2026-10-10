import OAI.NumberTheory.TwoPoint.Walks.RetainedActiveEdges
import OAI.NumberTheory.TwoPoint.Walks.BlockFormPrefixBound
import OAI.NumberTheory.TwoPoint.Bounds.InitialAverage

namespace OAI

/-! Apply the spectral block estimate to the actual retained correlation.
The conclusion records all boundary errors before their asymptotic absorption. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def retainedPrimePrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ e : ((j : Fin J) → P j) × Q,
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
      ((n : ℤ) + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) N / (N : ℂ)

theorem ModFiveThetaInput.eventually_actual_retained_prefix_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      let D := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
        h (progressionEdgeGate h l b) keep N‖ ≤
        (l : ℝ) * ((3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ))) / (2 * L * M) +
        ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M * D +
        2 * (M : ℝ) / N * D := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_progression_block_testing_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hb := hb h l hh hl E hE hEl W hW
  filter_upwards [hb, hprime.eventually_actual_pool_masses E W hW] with L hb hmass
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let M := ⌈Real.exp (103 * L)⌉₊
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  let D := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
  let active := fun d q => (d, q) ∈ data.pairs
  intro b N hN
  let F := ambientLiouvilleBlockForm P M Q Qp actualPaddingCoefficient active
    L K W (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep
  let B := (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
    ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
      Real.exp (-(2 * ⌊L⌋₊ : ℕ))
  have hNp : 0 < N := by exact_mod_cast (Real.exp_pos _).trans_le hN
  have hMp : 0 < M := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have havg : uniformAverage (fun t : Fin N => ‖F t.val‖) ≤ (l : ℝ) * B := by
    have ht := hb hL η hη hηone eligible he b N hN
    exact (uniformAverage_initial_le (fun t => ‖F t‖) (fun _ => norm_nonneg _) l N hl hNp).trans
      (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))
  have hp := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hd := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W := fun j => (hmass.2.1 j).2.1
  have hrow (n : ℕ) (_hn : 0 < n) :
      (∑ e : ((j : Fin J) → P j) × Q,
        ‖retainedPrimeEdge P Q Qp actualPaddingCoefficient active L K W
          (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep e n
          ((n : ℤ) + retainedPrimeStep active h e)‖) ≤ D := by
    simp only [retainedPrimeEdge_active_step_eq]
    exact retainedPrimeEdge_row_bound P hp hd Q Qp actualPaddingCoefficient active L K W
      (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep
      (by linarith) (Real.exp_pos _).le (by linarith)
      (fun q _ => actualPaddingCoefficient_nonneg q) hV n
  have hstep (e : ((j : Fin J) → P j) × Q) :
      retainedPrimeStep active h e ≤ h * ⌊Real.exp (100 * L + 1)⌋₊ := by
    apply retainedPrimeStep_le h hη hηone
    intro d q hmem
    exact he d q (canonicalTraceFamily_pair_eligible h E W L eligible hL hW hE d q hmem)
  have ht := block_form_prefix_bound (retainedPrimeStep active h)
    (fun e n => retainedPrimeEdge P Q Qp actualPaddingCoefficient active L K W
      (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep e n
      ((n : ℤ) + retainedPrimeStep active h e)) F M
    (h * ⌊Real.exp (100 * L + 1)⌋₊) N hMp hNp L ((l : ℝ) * B) D
    (by linarith) (by dsimp [D, K]; positivity) hstep hrow
    (fun t => ambientLiouvilleBlockForm_active P hp hd M Q Qp actualPaddingCoefficient active
      L K W (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b)
      (progressionEdgeGate_symmetric h l b) keep t) havg
  simpa only [retainedPrimeEdge_active_step_eq, retainedPrimePrefix] using ht

theorem ModFiveThetaInput.eventually_actual_retained_prefix
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h l : ℕ) (hh : 0 < h) (hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      let D := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
        h (progressionEdgeGate h l b) keep N‖ ≤
        (l : ℝ) * ((3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ))) / (2 * L * M) +
        ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M * D +
        2 * (M : ℝ) / N * D := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_actual_retained_prefix_uniform hBr
  exact ⟨A, hA, hbound h l hh hl E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
