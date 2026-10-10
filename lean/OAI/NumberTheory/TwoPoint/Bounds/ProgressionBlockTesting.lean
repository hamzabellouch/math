import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineTesting
import OAI.NumberTheory.TwoPoint.Walks.RetainedBlockIdentity
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionPartition

namespace OAI

/-! Combine the residue classes of block origins. The progression gate is
frozen in each class, and every block retains its ambient endpoint cuts. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def ambientLiouvilleBlockForm {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (t : ℕ) : ℂ :=
  let c : ℤ := (t + 2 : ℕ)
  let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) integerLiouville
  inner ℂ v (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp)
    L K W extra h (fun d n m => gate d (n + c) (m + c)) keep c v)

lemma ambientLiouvilleBlockForm_eq {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (t : ℕ) :
    ambientLiouvilleBlockForm P M Q Qp u eligible L K W extra h gate keep t =
      (2 * (L : ℂ)) * edgeBlockSum univ
        (fun e : ((j : Fin J) → P j) × Q => h * e.2.val * ∏ j, (e.1 j).val)
        (fun e n => retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
          ((n : ℤ) + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) M t :=
  primeBlockCompression_retained_blocks P hprime hdisjoint M t Q Qp u eligible
    L K W extra h gate hgate keep

lemma ambientLiouvilleBlockForm_progression {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h l b a k : ℕ) (keep : ℤ → Prop) :
    ambientLiouvilleBlockForm P M Q Qp u eligible L K W extra h
      (progressionEdgeGate h l b) keep (a + l * k) =
      let v := paddingTestVector Qp L
        (fun i : Fin M => (i.val : ℤ) + (a + 2 + l * k : ℕ)) integerLiouville
      inner ℂ v (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp) L K W
        extra h (fun d n m => progressionEdgeGate h l b d
          (n + (a + 2 : ℕ)) (m + (a + 2 : ℕ))) keep (a + 2 + l * k : ℕ) v) := by
  unfold ambientLiouvilleBlockForm
  dsimp only
  rw [show a + l * k + 2 = a + 2 + l * k by omega]
  have hc : ((a + 2 + l * k : ℕ) : ℤ) = (a + 2 : ℕ) + l * k := by
    push_cast
    ring
  rw [hc, primeBlockCompression_progression_freeze]

theorem ModFiveThetaInput.eventually_progression_block_testing_uniform
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
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun t : Fin (l * N) =>
        ‖ambientLiouvilleBlockForm P M Q Qp actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
          h (progressionEdgeGate h l b) keep t.val‖) ≤
        (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_actual_affine_testing_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hb := hb h l hh hl E hE hEl W hW
  filter_upwards [hb] with L hb
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
  intro b N hN
  apply uniformAverage_le_of_progressions
    (fun t => ‖ambientLiouvilleBlockForm P M Q Qp actualPaddingCoefficient
      (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
      h (progressionEdgeGate h l b) keep t‖) l N hl _
  intro a
  have ht := hb hL η hη hηone eligible he
    (fun d n m => progressionEdgeGate h l b d (n + (a.val + 2 : ℕ)) (m + (a.val + 2 : ℕ)))
    (fun d n m => progressionEdgeGate_symmetric h l b d _ _)
    integerLiouville integerLiouville_norm_le_one (a.val + 2) N hN
  simpa only [ambientLiouvilleBlockForm_progression] using ht

theorem ModFiveThetaInput.eventually_progression_block_testing
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
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun t : Fin (l * N) =>
        ‖ambientLiouvilleBlockForm P M Q Qp actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
          h (progressionEdgeGate h l b) keep t.val‖) ≤
        (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_progression_block_testing_uniform hBr
  exact ⟨A, hA, hbound h l hh hl E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
