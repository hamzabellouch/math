import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.Structure.ArithmeticCutoffTransport
import OAI.NumberTheory.SiegelZeros.Structure.ConcreteArchimedeanBridge

namespace OAI

section

namespace SiegelZeros.W07
open scoped BigOperators

theorem quadratic_of_real {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a, (χ a).im = 0) : χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · have hn : ‖χ a‖ = 1 := χ.unit_norm_eq_one ha.unit
    have he : ((χ a).re : ℂ) = χ a := by
      apply Complex.ext <;> simp [hreal]
    rw [← he, Complex.norm_real, Real.norm_eq_abs] at hn
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hn with h | h
    · right; left
      apply Complex.ext <;> simp [hreal, h]
    · right; right
      apply Complex.ext <;> simp [hreal, h]
  · exact Or.inl (χ.map_nonunit ha)

noncomputable def primeWeight (p : ℕ) : ℝ := Real.log p / p

noncomputable def primeMass (S : Finset ℕ) : ℝ := ∑ p ∈ S, primeWeight p

noncomputable def valuePrimes {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (v : ℂ) : Finset ℕ := by
  classical
  exact S.filter (fun p => χ (p : ZMod q) = v)

noncomputable def goodPrimes {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (H : ℕ) : Finset ℕ := by
  classical
  exact (valuePrimes χ S (-1)).filter (fun p => H < p ∧ ¬ p ∣ 2 * q)

noncomputable def discardedNegativePrimes {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (H : ℕ) : Finset ℕ := by
  classical
  exact (valuePrimes χ S (-1)).filter (fun p => ¬ (H < p ∧ ¬ p ∣ 2 * q))

theorem prime_mass_partition {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (S : Finset ℕ) :
    primeMass S = primeMass (valuePrimes χ S 0) +
      primeMass (valuePrimes χ S 1) + primeMass (valuePrimes χ S (-1)) := by
  classical
  simp only [primeMass, valuePrimes, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rcases hχ (p : ZMod q) with h | h | h <;> norm_num [h]

theorem negative_mass_partition {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (H : ℕ) :
    primeMass (valuePrimes χ S (-1)) = primeMass (goodPrimes χ S H) +
      primeMass (discardedNegativePrimes χ S H) := by
  classical
  simp only [primeMass, goodPrimes, discardedNegativePrimes, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

theorem good_mass_lower_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (S : Finset ℕ) (H : ℕ)
    (logX ell delta C Bm Br Bd : ℝ)
    (mertens : logX - Bm ≤ primeMass S)
    (primebias : primeMass (valuePrimes χ S 1) ≤
      C * ell + C * delta * logX ^ 2 / ell)
    (ramified : primeMass (valuePrimes χ S 0) ≤ Br)
    (deletion : primeMass (discardedNegativePrimes χ S H) ≤ Bd) :
    logX - C * ell - C * delta * logX ^ 2 / ell - (Bm + Br + Bd) ≤
      primeMass (goodPrimes χ S H) := by
  have hp := prime_mass_partition χ hχ S
  have hn := negative_mass_partition χ S H
  linarith

theorem negative_prime_not_dvd {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hχ : χ (p : ZMod q) = -1) : ¬ p ∣ q := by
  apply (ZMod.isUnit_prime_iff_not_dvd hp).mp
  by_contra hu
  have hz := χ.map_nonunit hu
  rw [hχ] at hz
  norm_num at hz

theorem negative_large_prime_not_dvd_two_mul {q p H : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hH : 2 ≤ H)
    (hlarge : H < p) (hχ : χ (p : ZMod q) = -1) : ¬ p ∣ 2 * q := by
  intro hd
  rcases hp.dvd_mul.mp hd with h2 | hq
  · have := Nat.le_of_dvd (show 0 < 2 by norm_num) h2
    omega
  · exact negative_prime_not_dvd χ hp hχ hq

theorem prime_value_zero_iff_dvd {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) : χ (p : ZMod q) = 0 ↔ p ∣ q := by
  constructor
  · intro hz
    by_contra hn
    have hu := (ZMod.isUnit_prime_iff_not_dvd hp).mpr hn
    exact (hu.map χ).ne_zero hz
  · intro hd
    apply χ.map_nonunit
    simpa only [ZMod.isUnit_prime_iff_not_dvd hp, not_not] using hd

theorem discarded_eq_small_negative {q H : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hH : 2 ≤ H) :
    discardedNegativePrimes χ S H = (valuePrimes χ S (-1)).filter (fun p => p ≤ H) := by
  classical
  ext p
  simp only [discardedNegativePrimes, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp, ?_⟩
    by_contra hn
    have hp' := Finset.mem_filter.mp hp
    exact hd ⟨by omega, negative_large_prime_not_dvd_two_mul χ (hS p hp'.1)
      hH (by omega) hp'.2⟩
  · rintro ⟨hp, hs⟩
    exact ⟨hp, fun h => (Nat.not_lt_of_ge hs) h.1⟩

end SiegelZeros.W07

end

namespace SiegelZeros

section

open scoped BigOperators NumberField

namespace SiegelZerosAwei.W46

open SiegelZerosAwei.W31

theorem order_image_card {m : ℕ} (orders : Fin m → MultiIndex)
    (hinj : Function.Injective orders) :
    (Finset.univ.image orders).card = m := by
  classical
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem order_image_sum {m : ℕ} (orders : Fin m → MultiIndex)
    (hinj : Function.Injective orders) (f : MultiIndex → ℝ) :
    (∑ i, f (orders i)) = ∑ α ∈ Finset.univ.image orders, f α := by
  classical
  exact (Finset.sum_image (fun i _ j _ hij => hinj hij)).symm

theorem concrete_master_of_norm_divisibility
    (H N q : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hq : 3 ≤ q)
    (a b : ℂ) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (hheight : |(d : ℝ)| ≤ (q : ℝ))
    (exponents : Fin (N ^ 4) → Fin 4 →₀ ℕ)
    (hn : ∀ j i, exponents j i ≤ N)
    (orders : Fin (N ^ 4) → MultiIndex) (hinj : Function.Injective orders)
    (hcut : ∀ i, weight (H : ℝ) (orders i) ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ))
    (hΔ : W37.concreteDelta a b d hd hd1 hd2 ha hb exponents orders ≠ 0)
    (C CH delta : ℝ) (hC : Real.log 4 ≤ C) (good : Finset ℕ)
    (hsub : good ⊆ SiegelZeros.W08.primesUpTo ((N : ℝ) ^ (4 / 3 : ℝ)))
    (hmass : Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) - C * Real.log q -
      C * delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q - CH ≤
        ∑ p ∈ good, Real.log (p : ℝ) / p)
    (hdiv : ∀ p ∈ good, (p : ℤ) ^ (4 * (∑ i, orders i 0 / p)) ∣
      Algebra.norm ℤ (W37.concreteDelta a b d hd hd1 hd2 ha hb exponents orders)) :
    let P := Finset.univ.image orders
    1 ≤ masterRHS (∑ α ∈ P, (α 0 : ℝ))
      (∑ α ∈ P, ((α 1 : ℝ) + (α 2 : ℝ))) P.card
      ((N : ℝ) ^ (4 / 3 : ℝ)) C CH (Real.log q) delta
      (Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) (Real.log P.card) (Real.log 8) := by
  classical
  let L := SiegelZeros.W10.rootField a b
  let : NumberField L :=
    SiegelZeros.W10.squarefreeRootField_numberField a b d hd hd1 hd2 ha hb
  let Δ : 𝓞 L := W37.concreteDelta a b d hd hd1 hd2 ha hb exponents orders
  let P := Finset.univ.image orders
  change 1 ≤ masterRHS (∑ α ∈ P, (α 0 : ℝ))
    (∑ α ∈ P, ((α 1 : ℝ) + (α 2 : ℝ))) P.card
    ((N : ℝ) ^ (4 / 3 : ℝ)) C CH (Real.log q) delta
    (Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) (Real.log P.card) (Real.log 8)
  have hcard : P.card = N ^ 4 := order_image_card orders hinj
  have hcutP : ∀ α ∈ P, weight (H : ℝ) α ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
    intro α hα
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hα
    exact hcut i
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hU : 0 ≤ (N : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbridge : (Δ : L) =
      (W36.concreteThetaMatrix a b d hd hd1 hd2 ha hb orders
        (fun j i => exponents j i)).det :=
    W37.deltaIntegral_eq_concreteThetaMatrix_det a b d hd hd1 hd2 ha hb orders _
  have hdet0 : (W36.concreteThetaMatrix a b d hd hd1 hd2 ha hb orders
      (fun j i => exponents j i)).det ≠ 0 := by
    rw [← hbridge]
    intro hz
    exact hΔ (Subtype.ext hz)
  have harch := W36.concrete_archimedean_norm_bound (pow_pos hNpos 4)
    a b d hd hd1 hd2 ha hb q N orders (fun j i => exponents j i)
    (by omega) hNpos hheight hn hdet0
  have horders : (∑ i, ((orders i 0 + orders i 1 + orders i 2 : ℕ) : ℝ)) =
      (∑ α ∈ P, (α 0 : ℝ)) + ∑ α ∈ P, ((α 1 : ℝ) + (α 2 : ℝ)) := by
    simpa only [P, Nat.cast_add, Finset.sum_add_distrib, add_assoc] using
      order_image_sum orders hinj (fun α => ((α 0 + α 1 + α 2 : ℕ) : ℝ))
  rw [horders, ← hbridge, ← integral_field_log_norm, ← hcard] at harch
  have hpall : ∀ p ∈ SiegelZeros.W08.primesUpTo ((N : ℝ) ^ (4 / 3 : ℝ)),
      Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hnorm : Algebra.norm ℤ Δ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hΔ
  have hnormlower := WeightedTorusJets.W45.quartic_weighted_prime_log_le good
    (fun p => ∑ i, orders i 0 / p) (Algebra.norm ℤ Δ) hnorm
    (fun p hp => hpall p (hsub hp)) hdiv
  have hfloor := SiegelZeros.W44.logarithmic_exponent_lower_subset
    (Finset.univ : Finset (Fin (N ^ 4))) (fun i => orders i 0) good
    (SiegelZeros.W08.primesUpTo ((N : ℝ) ^ (4 / 3 : ℝ))) hsub
    (fun p hp => (hpall p hp).one_le)
  simp only [SiegelZeros.W44.exponent, Finset.card_univ,
    Fintype.card_fin] at hfloor
  have hfinite := hfloor.trans hnormlower
  have hfirst : (∑ i, (orders i 0 : ℝ)) = ∑ α ∈ P, (α 0 : ℝ) :=
    order_image_sum orders hinj (fun α => (α 0 : ℝ))
  have hcardR : ((N ^ 4 : ℕ) : ℝ) = (P.card : ℝ) :=
    congrArg (fun m : ℕ => (m : ℝ)) hcard.symm
  rw [hfirst, hcardR] at hfinite
  have hcheb := SiegelZeros.W08.replace_chebyshev_error hU
    (Nat.cast_nonneg P.card) hfinite
  have hs : 0 ≤ ∑ α ∈ P, (α 0 : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hmass' := mul_le_mul_of_nonneg_left hmass hs
  have herror : Real.log 4 * (P.card : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ≤
      C * (P.card : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) hU
  have hlower : (∑ α ∈ P, (α 0 : ℝ)) *
      (Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) - C * Real.log q -
        C * (delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q) - CH) -
      C * P.card * (N : ℝ) ^ (4 / 3 : ℝ) ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℤ Δ : ℝ)| := by
    have heq : C * (delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q) =
        C * delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q := by ring
    rw [heq]
    linarith
  exact master_from_power_scale _ _ _ _ _ C CH delta _
    (cutoff_first_sum_pos P H N hH hHN hN hcard hcutP) hNr hqr harch hlower

end SiegelZerosAwei.W46

end

section

noncomputable section
open scoped BigOperators NumberField

namespace SiegelZerosAwei.W50

open WeightedTorusJets

theorem actual_character_selection
    {q N : ℕ} [NeZero q] (hq3 : 3 ≤ q) (hq8 : q ≠ 8)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hreal : W09.IsRealCharacter χ) (hn : χ ≠ 1)
    (H : ℕ) (hH : 2 ≤ H)
    (hgeometry : ∀ (d : ℤ) (a : ℂ), Squarefree d → d ≠ 1 → d ≠ 2 →
      ∀ ha : a ^ 2 = (d : ℂ), ActualCutoffSpanning H N d a ha) :
    ∃ (d k : ℤ) (a : ℂ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
      (ha : a ^ 2 = (d : ℂ)),
      W09.signedConductor χ = k ^ 2 * d ∧ d.natAbs ≤ q ∧
      IntermediateField.adjoin ℚ ({a} : Set ℂ) = W09.characterField χ ∧
      let L := SiegelZeros.W10.rootField a W60.sqrtTwo
      let f := algebraMap (𝓞 L) L
      let u := W37.integralRootA a W60.sqrtTwo d ha W60.sqrtTwo_sq
      let v := W37.integralRootB a W60.sqrtTwo d ha W60.sqrtTwo_sq
      let n : Fin (N ^ 4) → Fin 4 → ℤ := fun j i => (boxExponents N j i : ℤ)
      ∃ hcard : (W60.greedySet f H (sourceCutoff H N)
        (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j))).card = N ^ 4,
      let idx := W60.greedyIndex f H (sourceCutoff H N)
        (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j)) hcard
      let Δ := W37.concreteDelta a W60.sqrtTwo d hd hd1 hd2 ha W60.sqrtTwo_sq
        (boxExponents N) (fun i => (idx i).coords)
      Function.Injective (fun i => (idx i).coords) ∧
      (∀ i, W31.weight (H : ℝ) (idx i).coords ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) ∧
      Δ ≠ 0 ∧ Algebra.norm ℤ Δ ≠ 0 ∧
      (Algebra.norm ℤ Δ : ℚ) = Algebra.norm ℚ (Δ : L) ∧
      ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ (p : ZMod q) = -1 →
        (p : ℤ) ^ (4 * (∑ i, (idx i).coords 0 / p)) ∣ Algebra.norm ℤ Δ := by
  obtain ⟨d, k, a, hd, hd1, hd2, ha, hD, hbound, hfield, hspan⟩ :=
    W60.actual_character_determinant_norm_divisibility hq3 hq8 χ hprim hreal hn
      H (sourceCutoff H N) hH (boxExponents N)
  refine ⟨d, k, a, hd, hd1, hd2, ha, hD, hbound, hfield, ?_⟩
  dsimp only at hspan ⊢
  obtain ⟨hc, hne, hnorm, hcoe, hdiv⟩ := hspan (hgeometry d a hd hd1 hd2 ha)
  refine ⟨hc, ?_, ?_, hne, hnorm, hcoe, hdiv⟩
  · exact W62.orderedCoords_injective _ hc
  · intro i
    exact (W62.orderedCoords_weight_le (by omega) _ hc i).trans (sourceCutoff_le H N)

theorem actual_character_orders
    {q N : ℕ} [NeZero q] (hq3 : 3 ≤ q) (hq8 : q ≠ 8)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hreal : W09.IsRealCharacter χ) (hn : χ ≠ 1)
    (H : ℕ) (hH : 2 ≤ H)
    (hgeometry : ∀ (d : ℤ) (a : ℂ), Squarefree d → d ≠ 1 → d ≠ 2 →
      ∀ ha : a ^ 2 = (d : ℂ), ActualCutoffSpanning H N d a ha) :
    ∃ (d : ℤ) (a : ℂ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
      (ha : a ^ 2 = (d : ℂ)), d.natAbs ≤ q ∧
      ∃ orders : Fin (N ^ 4) → W31.MultiIndex,
        Function.Injective orders ∧
        (∀ i, W31.weight (H : ℝ) (orders i) ≤
          96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) ∧
        W37.concreteDelta a W60.sqrtTwo d hd hd1 hd2 ha W60.sqrtTwo_sq
          (boxExponents N) orders ≠ 0 ∧
        ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ (p : ZMod q) = -1 →
          (p : ℤ) ^ (4 * (∑ i, orders i 0 / p)) ∣ Algebra.norm ℤ
            (W37.concreteDelta a W60.sqrtTwo d hd hd1 hd2 ha W60.sqrtTwo_sq
              (boxExponents N) orders) := by
  obtain ⟨d, k, a, hd, hd1, hd2, ha, hD, hbound, hfield, hdata⟩ :=
    actual_character_selection hq3 hq8 χ hprim hreal hn H hH hgeometry
  dsimp only at hdata
  obtain ⟨hc, hinj, hcut, hΔ, hnorm, hcoe, hdiv⟩ := hdata
  exact ⟨d, a, hd, hd1, hd2, ha, hbound, _, hinj, hcut, hΔ, hdiv⟩

end SiegelZerosAwei.W50

end

end

section

noncomputable section
open scoped BigOperators NumberField

namespace SiegelZerosAwei.W50

open WeightedTorusJets Result.Workers.W33

theorem exists_actual_character_pivot_master
    {q N : ℕ} [NeZero q] (hq3 : 3 ≤ q) (hq8 : q ≠ 8)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hreal : W09.IsRealCharacter χ) (hn : χ ≠ 1)
    (H : ℕ) (hH : 2 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N)
    (C CH delta : ℝ) (hC : Real.log 4 ≤ C)
    (hgeometry : ∀ (d : ℤ) (a : ℂ), Squarefree d → d ≠ 1 → d ≠ 2 →
      ∀ ha : a ^ 2 = (d : ℂ), ActualCutoffSpanning H N d a ha)
    (hmass : Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) - C * Real.log q -
      C * delta * Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) ^ 2 / Real.log q - CH ≤
      SiegelZeros.W07.primeMass (SiegelZeros.W07.goodPrimes χ
        (SiegelZeros.W08.primesUpTo ((N : ℝ) ^ (4 / 3 : ℝ))) H)) :
    ∃ P : Finset W31.MultiIndex, P.card = N ^ 4 ∧
      (∀ α ∈ P, W31.weight (H : ℝ) α ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) ∧
      1 ≤ W46.masterRHS (firstOrder P) (transverseOrder P) P.card
        ((N : ℝ) ^ (4 / 3 : ℝ)) C CH (Real.log q) delta
        (Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) (Real.log P.card) (Real.log 8) := by
  classical
  obtain ⟨d, a, hd, hd1, hd2, ha, hbound, orders, hinj, hcut, hΔ, hdiv⟩ :=
    actual_character_orders hq3 hq8 χ hprim hreal hn H hH hgeometry
  let P := Finset.univ.image orders
  let good := SiegelZeros.W07.goodPrimes χ
    (SiegelZeros.W08.primesUpTo ((N : ℝ) ^ (4 / 3 : ℝ))) H
  have hsub : good ⊆ SiegelZeros.W08.primesUpTo ((N : ℝ) ^ (4 / 3 : ℝ)) := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hheight : |(d : ℝ)| ≤ (q : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hbound
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hgooddiv : ∀ p ∈ good,
      (p : ℤ) ^ (4 * (∑ i, orders i 0 / p)) ∣ Algebra.norm ℤ
        (W37.concreteDelta a W60.sqrtTwo d hd hd1 hd2 ha W60.sqrtTwo_sq
          (boxExponents N) orders) := by
    intro p hp
    have hpout := Finset.mem_filter.mp hp
    have hpin := Finset.mem_filter.mp hpout.1
    have hprime := (Finset.mem_filter.mp hpin.1).2
    exact hdiv p hprime hpout.2.1 hpout.2.2 hpin.2
  refine ⟨P, W46.order_image_card orders hinj, ?_, ?_⟩
  · intro α hα
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hα
    exact hcut i
  · exact W46.concrete_master_of_norm_divisibility H N q (by omega) hHN hN hq3
      a W60.sqrtTwo d hd hd1 hd2 ha W60.sqrtTwo_sq hheight
      (boxExponents N) (fun j i => (boxExponents_lt N j i).le)
      orders hinj hcut hΔ C CH delta hC good hsub hmass hgooddiv

end SiegelZerosAwei.W50

end

end

end SiegelZeros

end OAI
