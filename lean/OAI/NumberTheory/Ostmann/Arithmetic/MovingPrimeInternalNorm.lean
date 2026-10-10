import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeAverages

namespace OAI

/-! # Retaining the internal line factor in the two-prime environment -/

namespace Ostmann
open scoped Classical BigOperators

private theorem internal_sum_norm {σ A : Type*} [Fintype A] {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (v : A → ZMod (p ^ 2) × ZMod (p ^ 2)) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, movingInternalPairFactor value T p (v a).1 (v a).2‖ =
      (Fintype.card A : ℝ)⁻¹ * ∑ a, ‖movingInternalPairFactor value T p (v a).1 (v a).2‖ := by
  have he (a : A) : movingInternalPairFactor value T p (v a).1 (v a).2 =
      (‖movingInternalPairFactor value T p (v a).1 (v a).2‖ : ℂ) := by
    unfold movingInternalPairFactor
    split_ifs <;> simp
  have hs : (∑ a, movingInternalPairFactor value T p (v a).1 (v a).2) =
      ((∑ a, ‖movingInternalPairFactor value T p (v a).1 (v a).2‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun a _ => he a)
  rw [hs, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

private theorem unit_pair_average_le_twice_mixed (p : ℕ) [Fact p.Prime]
    (f : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℝ)⁻¹ *
      (∑ z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ, f (z.1.val, z.2)) ≤
    2 * ((Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℝ)⁻¹ * ∑ z, f z) := by
  let e : ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) ↪
      (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) :=
    Function.Embedding.prodMap
      (⟨Units.val, fun _ _ h => Units.ext h⟩ : (ZMod (p ^ 2))ˣ ↪ ZMod (p ^ 2))
      (Function.Embedding.refl _)
  have hs : (∑ z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ, f (e z)) ≤ ∑ z, f z := by
    calc
      _ = ∑ z ∈ Finset.univ.map e, f z := (Finset.sum_map _ _ _).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
        (fun z _ _ => hf z)
  have hp : p.Prime := Fact.out
  have hphi : Nat.totient (p ^ 2) = p * (p - 1) := by
    simpa only [pow_one] using Nat.totient_prime_pow_succ hp 1
  have hsize : p ^ 2 ≤ 2 * Nat.totient (p ^ 2) := by
    rw [hphi]
    have hsub := Nat.sub_add_cancel hp.one_le
    have htwo := hp.two_le
    nlinarith
  have hc : (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℝ) ≤
      2 * (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℝ) := by
    simp only [Fintype.card_prod, ZMod.card, ZMod.card_units_eq_totient, Nat.cast_mul]
    have hmul := Nat.mul_le_mul_right (Nat.totient (p ^ 2)) hsize
    exact_mod_cast (by simpa only [mul_assoc] using hmul)
  have hcp : (0 : ℝ) < Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) := by
    exact_mod_cast Fintype.card_pos
  have hcm : (0 : ℝ) < Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) := by
    exact_mod_cast Fintype.card_pos
  have hi : (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℝ)⁻¹ ≤
      2 * (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℝ)⁻¹ := by
    have h : (1 : ℝ) / (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℝ) ≤
        2 / (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℝ) := by
      apply (div_le_div_iff₀ hcp hcm).mpr
      simpa only [one_mul] using hc
    simpa only [div_eq_mul_inv, one_mul] using h
  calc
    _ ≤ (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℝ)⁻¹ * ∑ z, f z :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hcp.le)
    _ ≤ (2 * (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℝ)⁻¹) * ∑ z, f z :=
      mul_le_mul_of_nonneg_right hi (Finset.sum_nonneg (fun z _ => hf z))
    _ = _ := by ring

/-- Restricting the first giant to units costs at most two at each distinct
internal prime, while retaining the full simultaneous line probability. -/
theorem movingInternalPrimeAverage_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    ‖movingInternalPrimeAverage value T p‖ ≤ 2 * movingInternalLineProbability value T p := by
  have hpavg := internal_sum_norm value T p
    (fun z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ =>
      ((z.1 : ZMod (p ^ 2)), (z.2 : ZMod (p ^ 2))))
  have hmavg := internal_sum_norm value T p
    (fun z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ => (z.1, (z.2 : ZMod (p ^ 2))))
  have hunit := unit_pair_average_le_twice_mixed p
    (fun z => ‖movingInternalPairFactor value T p z.1 z.2‖) (fun _ => norm_nonneg _)
  have hmix := movingInternalPairFactor_probability_norm_le value T p
  exact hpavg.le.trans (hunit.trans
    (mul_le_mul_of_nonneg_left (hmavg.symm.le.trans hmix) (by norm_num)))

/-- Only a fixed factor per equality class is paid, and every class retains
its original inverse-prime line probability. -/
theorem movingInternalPrimeAverage_product_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n)
    (P : Finset ℕ) [∀ p : P, Fact p.val.Prime] :
    ‖∏ p : P, movingInternalPrimeAverage value T p.val‖ ≤
      (2 : ℝ) ^ P.card * ∏ p : P, movingInternalLineProbability value T p.val := by
  rw [norm_prod]
  calc
    _ ≤ ∏ p : P, (2 * movingInternalLineProbability value T p.val) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun p _ => movingInternalPrimeAverage_norm_le value T p.val)
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_coe]

end Ostmann

end OAI
