import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineSpectralTail
import OAI.NumberTheory.TwoPoint.Bounds.PrimePhysicalMatrix
import OAI.NumberTheory.TwoPoint.Bounds.SpectralScale

namespace OAI

/-! The literal compressed graph obeys the trace bound outside an
exponentially small set of origins in each fixed progression. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def primeBlockCompression {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (c : ℤ) :
    EuclideanSpace ℂ (Fin M) →L[ℂ] EuclideanSpace ℂ (Fin M) :=
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
    (fun i : Fin M => (i.val : ℤ) + c) Q u eligible g L K extra h
    (fun d i j => gate d i.val j.val ∧ keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c))
  let proj := coordinateProjection (fun i : Fin M =>
    (actualPaddingDegree (univ.biUnion P) ((i.val : ℤ) + c) : ℝ) ≤ 6 * W * J)
  proj * (∑ d, B d) * proj

theorem ModFiveThetaInput.eventually_actual_affine_compression_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (E : Finset ℕ)
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
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => if
        3 * (Real.exp 1 * (2 * (Real.exp (4 * J) *
          (2 * Real.exp 150 * Real.sqrt W) ^ J))) <
        ‖primeBlockCompression P ⌈Real.exp (103 * L)⌉₊ Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ)‖ then (1 : ℝ) else 0) ≤
        Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, htail⟩ := hprime.eventually_actual_affine_spectral_tail_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh E hE hEl W hW
  have htail := htail h l hh E hE hEl W hW
  filter_upwards [htail, hprime.eventually_actual_pool_masses E W hW] with L htail hmass
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  let M := ⌈Real.exp (103 * L)⌉₊
  have hbounds := actual_spectral_scale_bounds J K W (Real.exp_pos _).le hW
  have hprimeP := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hdisjoint := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W := fun j => (hmass.2.1 j).2.1
  intro gate hgate a N hN
  have ht := htail hL η hη hηone eligible he (fun d n m => gate (∏ j, (d j).val) n m) a N hN
  apply le_trans _ ht
  unfold uniformAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro x _
  by_cases hr : R < realMatrixSpectralRadius
      (shiftMatrix (primeBlockEmbedding (P := P) M)
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h
          (fun d n m => gate (∏ j, (d j).val) n m)
          (fun t n => maskedSignedIntegerWeight Q actualPaddingCoefficient
            (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
            (fun d => centeredTuple d.primeFactors) L K
            (fun _ => actualPaddingDegreeCut Qp L) h keep t
            (n + (a + l * x.val : ℕ)))))
  · change (if _ then (1 : ℝ) else 0) ≤ if R < _ then 1 else 0
    rw [ite_eq_left hr]
    split_ifs <;> norm_num
  · have hc := prime_physical_compression P hprimeP hdisjoint
      (fun i : Fin M => (i.val : ℤ))
      (fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)) Q actualPaddingCoefficient
      (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp) L K W
      (fun _ => actualPaddingDegreeCut Qp L) h gate hgate keep (a + l * x.val : ℕ)
      (by linarith) (Real.exp_pos _).le (fun q _ => actualPaddingCoefficient_nonneg q)
      (actualPaddingVertex_pos Qp) hV R hbounds.1 hbounds.2.1 hbounds.2.2
      (le_of_not_gt hr)
    change ‖primeBlockCompression P M Q actualPaddingCoefficient
      (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp) L K W
      (fun _ => actualPaddingDegreeCut Qp L) h gate keep (a + l * x.val : ℕ)‖ ≤ 3 * R at hc
    change (if 3 * R < _ then (1 : ℝ) else 0) ≤ if R < _ then 1 else 0
    rw [ite_eq_right (not_lt.mpr hc), ite_eq_right hr]

theorem ModFiveThetaInput.eventually_actual_affine_compression
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h l : ℕ) (hh : 0 < h) (E : Finset ℕ)
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
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => if
        3 * (Real.exp 1 * (2 * (Real.exp (4 * J) *
          (2 * Real.exp 150 * Real.sqrt W) ^ J))) <
        ‖primeBlockCompression P ⌈Real.exp (103 * L)⌉₊ Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ)‖ then (1 : ℝ) else 0) ≤
        Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_actual_affine_compression_uniform hBr
  exact ⟨A, hA, hbound h l hh E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
