import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeFamily

namespace OAI

/-! Harmonic masses and integer endpoints for the literal prime family.
These derive the trace theorem's prime-pool hypotheses from the single
fixed-modulus published input. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma centeredPrimePool_mass (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) :
    primeHarmonicMass (centeredPrimePool E A W J) =
      ∑ j : Fin J, primeHarmonicMass (centeredPrimeBands E A W J j) :=
  primeTuplePool_mass _ (centeredPrimeBands_disjoint E A W J hA hW)

lemma centeredPrimePool_mass_bounds (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hmass : ∀ j : Fin J,
      W ≤ primeHarmonicMass (centeredPrimeBands E A W J j) ∧
        primeHarmonicMass (centeredPrimeBands E A W J j) ≤ 2 * W) :
    (J : ℝ) * W ≤ primeHarmonicMass (centeredPrimePool E A W J) ∧
      primeHarmonicMass (centeredPrimePool E A W J) ≤ J * (2 * W) := by
  rw [centeredPrimePool_mass E A W J hA hW]
  constructor
  · calc
      _ = ∑ _j : Fin J, W := by simp
      _ ≤ _ := sum_le_sum (fun j _ => (hmass j).1)
  · calc
      _ ≤ ∑ _j : Fin J, 2 * W := sum_le_sum (fun j _ => (hmass j).2)
      _ = _ := by simp

lemma primeSupplyCount_mul_bound (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤
      ((1 / 200 : ℝ) * Real.log L) / (6 * W) := Nat.floor_le (by positivity)
  exact (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj

theorem ModFiveThetaInput.eventually_padding_pool_mass (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      primeHarmonicMass (paddingPrimeSupply E L) ≤ Real.log L := by
  obtain ⟨C, hC, hm⟩ := hP.padding_reciprocal_mass E
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.exp (4 * C))]
      with L hL hLC
  have hlog : 4 * C ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hLC
  rw [primeHarmonicMass_eq_sum]
  linarith [hm L hL]

/-- All pool-mass hypotheses used by the literal column trace hold for
the constructed bands. The numerical eligibility predicate does not
enter these estimates. -/
theorem ModFiveThetaInput.eventually_actual_pool_masses (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let A := L ^ (199 / 200 : ℝ)
      1 ≤ J ∧
      (∀ j : Fin J, 1 ≤ primeHarmonicMass (centeredPrimeBands E A W J j) ∧
        primeHarmonicMass (centeredPrimeBands E A W J j) ≤ 2 * W ∧
        primeHarmonicMass (centeredPrimeBands E A W J j) ≤ L ^ (2 : ℕ)) ∧
      1 ≤ primeHarmonicMass (centeredPrimePool E A W J) ∧
      primeHarmonicMass (centeredPrimePool E A W J) ≤ Real.log L / 600 ∧
      primeHarmonicMass (centeredPrimePool E A W J) ≤ L ^ (2 : ℕ) ∧
      primeHarmonicMass (paddingPrimeSupply E L) ≤ L ^ (2 : ℕ) := by
  filter_upwards [hP.eventually_actual_prime_supplies E W hW,
    hP.eventually_padding_pool_mass E, eventually_ge_atTop (1 : ℝ)] with L hs hq hL
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA : 0 ≤ A := Real.rpow_nonneg hLp.le _
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hmass (j : Fin J) :
      W ≤ primeHarmonicMass (centeredPrimeBands E A W J j) ∧
        primeHarmonicMass (centeredPrimeBands E A W J j) ≤ 2 * W := by
    simpa only [primeHarmonicMass_eq_sum, centeredPrimeBands, A] using (hs.2.2 j.val).2
  have hp := centeredPrimePool_mass_bounds E A W J hA hWp.le hmass
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hs.1
  have hpoolone : 1 ≤ primeHarmonicMass (centeredPrimePool E A W J) := by
    have hprod : 1 ≤ (J : ℝ) * W := hW.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hj hWp.le)
    exact hprod.trans hp.1
  have hpoollog : primeHarmonicMass (centeredPrimePool E A W J) ≤ Real.log L / 600 := by
    have hb := primeSupplyCount_mul_bound W L hWp hL
    change (J : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L at hb
    nlinarith [hp.2]
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hLsq : L ≤ L ^ (2 : ℕ) := by nlinarith
  have hpoolpoly : primeHarmonicMass (centeredPrimePool E A W J) ≤ L ^ (2 : ℕ) := by
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
    exact hpoollog.trans ((by linarith : Real.log L / 600 ≤ Real.log L).trans
      (hlog.trans hLsq))
  refine ⟨hs.1, ?_, hpoolone, hpoollog, hpoolpoly, hq.trans (hlog.trans hLsq)⟩
  intro j
  refine ⟨hW.trans (hmass j).1, (hmass j).2, ?_⟩
  exact (primeHarmonicMass_mono (centeredPrimeBand_subset_pool E A W J j)).trans hpoolpoly

lemma centeredPrimeTuple_upper (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 < A) (hW : 1 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (centeredPrimeBands E A W J)) :
    d ≤ ⌊Real.exp (2 * L)⌋₊ := by
  have hb := centeredPrimeTuple_log_bound hA hW hL hd
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hb.1
  simpa only [Real.exp_log hdpos] using Real.exp_le_exp.mpr hb.2

/-- Removing one prime from an actual tuple only reduces its value. -/
lemma centeredPrimeTuple_complement_upper (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 < A) (hW : 1 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    (x : (j : Fin J) → centeredPrimeBands E A W J j) (j : Fin J) :
    (∏ i ∈ univ.erase j, (x i).val) ≤ ⌊Real.exp (2 * L)⌋₊ := by
  apply le_trans _ (centeredPrimeTuple_upper E A W L J hA hW hL
    (mem_image.mpr ⟨x, mem_univ _, rfl⟩))
  exact Nat.le_of_dvd (prod_pos (fun i _ => (centeredPrimeSupply_mem (x i).property).1.pos))
    (prod_dvd_prod_of_subset (univ.erase j) univ (fun i => (x i).val) (erase_subset _ _))

lemma paddingPairEligible_padding_upper {L η : ℝ} {d q : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (hd : 0 < d)
    (he : PaddingPairEligible L η d q) : q ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
  by_cases hq : q = 0
  · simp [hq]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  let j := paddingBin η 0 (Real.log (d * q : ℕ))
  have hj := (mem_paddingBinIndices_iff L η j hη).mp he.2
  have hx := (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mp rfl
  simp only [add_zero] at hx
  have hxupper : Real.log (d * q : ℕ) ≤ 100 * L + 1 := by
    nlinarith [hj.2, hx.2]
  have hqlog : Real.log q ≤ Real.log (d * q : ℕ) := by
    rw [Nat.cast_mul, Real.log_mul hd0 hq0]
    linarith [log_nat_nonneg d]
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  simpa only [Real.exp_log hqp] using Real.exp_le_exp.mpr (hqlog.trans hxupper)

lemma actualProhibitedPrimeFamily_padding_upper (h J M : ℕ) (E : Finset ℕ)
    (A W L η : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hη : 0 < η) (hηone : η ≤ 1)
    (he : ∀ d q, eligible d q → PaddingPairEligible L η d q)
    {dq : ℕ × ℕ}
    (hdq : dq ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs) :
    dq.2 ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
  have hm := (actualProhibitedPrimeFamily_pairs h J M E A W L eligible hA hW hE
    dq.1 dq.2).mp hdq
  have hs := (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).tuple_squarefree dq hdq
  exact paddingPairEligible_padding_upper hη hηone (Nat.pos_of_ne_zero hs.ne_zero)
    (he dq.1 dq.2 hm.2.2.2)

end TwoPointCorrelations

end OAI
