import OAI.NumberTheory.TwoPoint.Bounds.FiniteLawParameters
import OAI.NumberTheory.TwoPoint.Bounds.ScalarComparison

namespace OAI

/-! The explicit polynomial bit and independence budgets give the
finite-interval circuit comparison required in the graph application. -/

namespace TwoPointCorrelations

open Finset Filter

theorem BravermanDepth22Input.eventually_residue_comparison (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (n : ℕ) (coord : Fin n → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n),
      c.depth ≤ 20 → (c.size : ℝ) ≤ Real.exp (L ^ 6) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N =>
          eventIndicator (residueCircuitEvent s coord test c)
            (fun i => (a + x.val : ZMod (s i)))) -
        uniformAverage (eventIndicator (residueCircuitEvent s coord test c))| ≤
          Real.exp (-(L ^ 10)) := by
  obtain ⟨K, C, hK, hC, hcompare⟩ := hBr.finite_residue_comparison
  let T := 17 * C + 1
  let A := T + 1002
  refine ⟨A, by omega, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_encoded_size_bound,
    eventually_bit_count_bound, eventually_braverman_budget K C,
    eventually_fourier_budget T A (by omega) (by omega),
    eventually_total_comparison_error] with L hL hsize hbits hbr hfourier herr
  intro m s _ hm hmexp hcop hs n coord test c hc hcsize a N hN
  let B := ⌈L ^ 15⌉₊
  let t := ⌈L ^ T⌉₊
  have hLone : 1 ≤ L := by linarith
  have hLp : 0 ≤ L := by linarith
  have hBone : 0 < B := by
    have hBbound := (ceil_pow_bounds hLone 15).1
    have hone : (1 : ℝ) ≤ L ^ 15 := one_le_pow₀ hLone
    have hBp : (0 : ℝ) < B := by dsimp only [B]; linarith
    exact_mod_cast hBp
  have hBsize0 : ((encodeResidueCircuit s B coord test c).size : ℝ) ≤
      (1 + (2 : ℝ) ^ B * (1 + B)) * c.size := by
    exact_mod_cast encodeResidueCircuit_size (B := B) s coord test c
  have hBsize : ((encodeResidueCircuit s B coord test c).size : ℝ) ≤ Real.exp (L ^ 17) :=
    hBsize0.trans (hsize B rfl c.size hcsize)
  have hBsizeone : (1 : ℝ) ≤ (encodeResidueCircuit s B coord test c).size := by
    exact_mod_cast (encodeResidueCircuit s B coord test c).size_pos
  have ht := hbr (encodeResidueCircuit s B coord test c).size hBsizeone hBsize
  have hnbits := hbits m B hmexp rfl
  have hfour := hfourier t (m * B) N rfl hnbits hN
  have hNpos : 0 < N := by
    have hNp : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
    exact_mod_cast hNp
  have heps : Real.exp (-(L ^ 11)) ≤ 1 / 2 := by
    have hone : (1 : ℝ) ≤ L ^ 11 := one_le_pow₀ hLone
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_neg]
    exact (inv_anti₀ (by norm_num : (0 : ℝ) < 2)
      (he.trans (Real.exp_le_exp.mpr hone))).trans_eq (by norm_num)
  have hb := hcompare m B (Nat.mul_pos hm hBone) s hcop n coord test c hc
    (Real.exp (-(L ^ 11))) (Real.exp_pos _) heps t ht a N hNpos (Real.exp L)
    (Real.exp (-(L ^ 11))) (Real.one_le_exp hLp) hs hfour
  have hsum : (∑ i : Fin m, (s i : ℝ)) ≤ Real.exp (3 * L) := by
    have hbound : (∑ i : Fin m, (s i : ℝ)) ≤ m * Real.exp L := by
      calc
        _ ≤ ∑ _i : Fin m, Real.exp L := sum_le_sum (fun i _ => hs i)
        _ = _ := by simp
    have hE : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hLp
    have hE2 : (2 : ℝ) ≤ Real.exp L := by
      linarith [Real.add_one_le_exp L]
    calc
      _ ≤ (Real.exp L + 1) * Real.exp L :=
        hbound.trans (mul_le_mul_of_nonneg_right hmexp (Real.exp_pos _).le)
      _ ≤ Real.exp L * Real.exp L * Real.exp L := by nlinarith
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hb.trans
  simpa only [← sum_div, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc] using herr B rfl _ hsum

/-- Scalar expansions preserve their signed coefficients through the
finite-law comparison; only their total absolute mass enters the error. -/
theorem BravermanDepth22Input.eventually_scalar_residue_comparison
    (hBr : BravermanDepth22Input) (C : ℝ) (hC : 0 ≤ C) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (ι : Type) [Fintype ι] (n : ℕ) (coord : Fin n → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (c : ι → AC0Circuit n) (coeff : ι → ℝ),
      (∀ i, (c i).depth ≤ 20) → (∀ i, ((c i).size : ℝ) ≤ Real.exp (L ^ 6)) →
      (∑ i, |coeff i|) ≤ Real.exp (C * L ^ 5) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N => ∑ i, coeff i *
          eventIndicator (residueCircuitEvent s coord test (c i))
            (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage (fun r => ∑ i, coeff i *
          eventIndicator (residueCircuitEvent s coord test (c i)) r)| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hevent⟩ := hBr.eventually_residue_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hevent, eventually_scalar_error C hC] with L hevent herror
  intro m s _ hm hmexp hcop hs ι _ n coord test c coeff hc hsize hcoeff a N hN
  have hb := scalar_average_comparison_uniform
    (fun i (x : Fin N) => eventIndicator (residueCircuitEvent s coord test (c i))
      (fun j => (a + x.val : ZMod (s j))))
    (fun i r => eventIndicator (residueCircuitEvent s coord test (c i)) r)
    coeff (Real.exp (-(L ^ 10)))
    (fun i => hevent m s hm hmexp hcop hs n coord test (c i) (hc i) (hsize i) a N hN)
  exact hb.trans ((mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le).trans herror)

end TwoPointCorrelations

end OAI
