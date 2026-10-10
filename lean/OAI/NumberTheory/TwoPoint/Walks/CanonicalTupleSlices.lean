import OAI.NumberTheory.TwoPoint.Walks.TupleSliceSupport
import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale

namespace OAI

/-! The actual centered bands satisfy every arithmetic support condition
used by quantitative partial centering, including nonunit progression classes. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma retainedPrimeDivisor_coprime_of_primes (S : Finset ℕ) (l : ℕ)
    (hcop : ∀ p ∈ S, p.Coprime l) {q : ℕ} (hq : q ∈ retainedPrimeDivisors S) :
    q.Coprime l := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hq
  exact Nat.coprime_prod_left_iff.mpr (fun p hp => hcop p ((mem_powerset.mp hU) hp))

lemma centeredPrimeBands_coprime (E : Finset ℕ) (A W : ℝ) (J l : ℕ)
    (hE : ∀ p, p.Prime → p ∣ l → p ∈ E)
    (j : Fin J) {p : ℕ} (hp : p ∈ centeredPrimeBands E A W J j) : p.Coprime l := by
  have hs := centeredPrimeSupply_mem hp
  exact hs.1.coprime_iff_not_dvd.mpr (fun hd => hs.2.2.1 (hE p hs.1 hd))

lemma paddingPrimeDivisor_coprime (E : Finset ℕ) (L : ℝ) (l : ℕ)
    (hE : ∀ p, p.Prime → p ∣ l → p ∈ E)
    {q : ℕ} (hq : q ∈ retainedPrimeDivisors (paddingPrimeSupply E L)) : q.Coprime l := by
  apply retainedPrimeDivisor_coprime_of_primes _ l _ hq
  intro p hp
  exact (paddingPrimeSupply_prime hp).coprime_iff_not_dvd.mpr
    (fun hd => (mem_sdiff.mp hp).2 (hE p (paddingPrimeSupply_prime hp) hd))

lemma paddingPrimeDivisor_coprime_centered (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    {q : ℕ} (hq : q ∈ retainedPrimeDivisors (paddingPrimeSupply E L))
    (j : Fin J) {p : ℕ} (hp : p ∈ centeredPrimeBands E A W J j) : q.Coprime p := by
  apply retainedPrimeDivisor_coprime_of_primes _ p _ hq
  intro r hr
  apply (Nat.coprime_primes (paddingPrimeSupply_prime hr)
    (centeredPrimeBands_prime E A W J j p hp)).mpr
  intro he
  subst r
  exact (disjoint_left.mp (centeredPrimePool_disjoint_padding E A W L J))
    (centeredPrimeBand_subset_pool E A W J j hp) hr

lemma partial_tuple_unit (E : Finset ℕ) (A W L : ℝ) (J l : ℕ)
    (hE : ∀ p, p.Prime → p ∣ l → p ∈ E)
    (I : Finset (Fin J)) {q : ℕ} (hq : q ∈ retainedPrimeDivisors (paddingPrimeSupply E L))
    (y : (j : {j // j ∉ I}) → centeredPrimeBands E A W J j) :
    IsUnit ((q * ∏ j, (y j).val : ℕ) : ZMod l) := by
  apply (ZMod.isUnit_iff_coprime _ l).mpr
  exact Nat.coprime_mul_iff_left.mpr
    ⟨paddingPrimeDivisor_coprime E L l hE hq,
      Nat.coprime_prod_left_iff.mpr (fun j _ =>
        centeredPrimeBands_coprime E A W J l hE j (y j).property)⟩

theorem ModFiveThetaInput.eventually_canonical_tuple_slices (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      (∀ j, (P j).Nonempty) ∧
      (∀ I : Finset (Fin J), I.Nonempty → ∀ z ∈ primeTupleSlice P I,
        Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ Real.exp (2 * L) ∧
          avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) := by
  filter_upwards [hP.eventually_actual_prime_supplies E W hW,
    eventually_ge_atTop (2 : ℝ)] with L hs hL
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hLp : 0 < L := by linarith
  have hA : 0 < A := Real.rpow_pos_of_pos hLp _
  have hendpoint := primeSupplyScale_endpoint W L (by linarith) (by linarith)
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime E A W J
  have hlarge (j : Fin J) (p : ℕ) (hp : p ∈ P j) : Real.exp A < (p : ℝ) :=
    (centeredPrimeSupply_global_bounds hA.le (by linarith) j.isLt hendpoint hp).1
  have hne (j : Fin J) : (P j).Nonempty := by
    by_contra hn
    have he : P j = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hm : W ≤ primeHarmonicMass (P j) := by
      simpa only [primeHarmonicMass_eq_sum, P, A, centeredPrimeBands] using (hs.2.2 j.val).2.1
    rw [he] at hm
    norm_num [primeHarmonicMass] at hm
    linarith
  refine ⟨hne, ?_⟩
  intro I hI z hz
  have hy : Real.exp (L ^ (99 / 100 : ℝ)) < Real.exp A := by
    apply Real.exp_lt_exp.mpr
    exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
  refine ⟨primeTupleSlice_lower P I hp (Real.exp A) (fun j p hp => (hlarge j p hp).le) hI hz,
    primeTupleSlice_le_full_bound P I hp hne _ (fun d hd => ?_) hz,
    primeTupleSlice_avoids P I hp _ (Real.exp_pos _).le
      (fun j p hp => hy.trans (hlarge j p hp)) hz⟩
  exact (show (d : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by
    exact_mod_cast centeredPrimeTuple_upper E A W L J hA hW hendpoint hd).trans
      (Nat.floor_le (Real.exp_pos _).le)

end TwoPointCorrelations

end OAI
