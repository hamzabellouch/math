import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineCompression
import OAI.NumberTheory.TwoPoint.Bounds.ProjectedGraphTesting

namespace OAI

/-! Average the actual graph test over fixed-progression block origins,
using compression on good blocks and the deterministic bound elsewhere. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_affine_testing_uniform
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
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ f : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun x : Fin N =>
        let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
        ‖inner ℂ v (primeBlockCompression P M Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ) v)‖) ≤
        (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨Ac, hAc, hcomp⟩ := hprime.eventually_actual_affine_compression_uniform hBr
  obtain ⟨Av, hAv, hnorm⟩ := hBr.eventually_padding_test_progression_norm
  refine ⟨Ac + Av, by omega, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hcomp := hcomp h l hh E hE hEl W hW
  filter_upwards [hcomp, hnorm, hprime.eventually_actual_pool_masses E W hW]
    with L hcomp hnorm hmass
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
  have hprimeP := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hdisjoint := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W := fun j => (hmass.2.1 j).2.1
  intro gate hgate f hf a N hN
  have hNc : Real.exp (L ^ Ac / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL (Nat.le_add_right Ac Av)) (by norm_num))).trans hN
  have hNv : Real.exp (L ^ Av / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL (Nat.le_add_left Av Ac)) (by norm_num))).trans hN
  have hNpos : 0 < N := by exact_mod_cast (Real.exp_pos _).trans_le hN
  let : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  let T (x : Fin N) := primeBlockCompression P M Q actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
    L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep (a + l * x.val : ℕ)
  let v (x : Fin N) := paddingTestVector Qp L
    (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
  have hb := hcomp hL η hη hηone eligible he gate hgate a N hNc
  have hv := hnorm Qp (fun p hp => paddingPrimeSupply_prime hp)
    (fun p hp => paddingPrimeSupply_bounds E L hp) (fun i : Fin M => (i.val : ℤ)) f hf a l N hl hNv
  have hv' : uniformAverage (fun x : Fin N => ‖v x‖ ^ 2) ≤
      (l : ℝ) * (2 * M * paddingTiltNormalizer Qp) := by
    simpa only [v, add_comm ((a + l * _ : ℕ) : ℤ), Fintype.card_fin] using hv
  have htest := (FiniteLaw.uniform (Fin N)).average_operator_test T v
    (3 * R) ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L))
    ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) (Real.exp (-(2 * ⌊L⌋₊ : ℕ)))
    (by positivity) (by positivity) ?_ ?_ ?_
  · simpa only [FiniteLaw.uniform_average, T, v, R, K, M, keep, data, Q, Qp, P, J] using htest
  · simpa only [FiniteLaw.uniform_average] using hv'
  · simpa only [FiniteLaw.probability, FiniteLaw.uniform_average, T, R, K, M, keep, data, Q, Qp, P, J] using hb
  · intro x _
    have ht := projected_padding_graph_test P hprimeP hdisjoint
      (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ))
      (fun i j hij => Fin.ext (Int.ofNat_inj.mp (add_right_cancel hij)))
      Q Qp actualPaddingCoefficient (fun d q => (d, q) ∈ data.pairs) L K W
      (fun _ => actualPaddingDegreeCut Qp L) h
      (fun d i j => gate d i.val j.val ∧ keep ((i.val : ℤ) + (a + l * x.val : ℕ)) ∧
        keep ((j.val : ℤ) + (a + l * x.val : ℕ)))
      (by linarith) (Real.exp_pos _).le (by linarith)
      (fun q _ => actualPaddingCoefficient_nonneg q) hV f hf
    simpa only [primeBlockCompression, T, v, Fintype.card_fin] using ht

theorem ModFiveThetaInput.eventually_actual_affine_testing
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
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ f : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun x : Fin N =>
        let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
        ‖inner ℂ v (primeBlockCompression P M Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ) v)‖) ≤
        (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_actual_affine_testing_uniform hBr
  exact ⟨A, hA, hbound h l hh hl E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
