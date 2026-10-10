import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeSetQuadratic

namespace OAI

/-! # Absolute residue mass of the actual density correlations -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem norm_sum_le_of_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : (∑ x : ZMod q, ‖f x‖ ^ 2) ≤ q) :
    (∑ x : ZMod q, ‖f x‖) ≤ q := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖f x‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at hc
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hh := mul_le_mul_of_nonneg_right hf hq
  have hs : 0 ≤ ∑ x : ZMod q, ‖f x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith

theorem norm_product_sum_le_of_energy {q : ℕ} [NeZero q] (f g : ZMod q → ℂ)
    (hf : (∑ x : ZMod q, ‖f x‖ ^ 2) ≤ q)
    (hg : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q) :
    (∑ x : ZMod q, ‖f x * conj (g x)‖) ≤ q := by
  simp only [norm_mul, Complex.norm_conj]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖f x‖) (fun x => ‖g x‖)
  have hh := mul_le_mul hf hg (by positivity) (Nat.cast_nonneg q)
  have hs : 0 ≤ ∑ x : ZMod q, ‖f x‖ * ‖g x‖ := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith

theorem correlationPrimeFactor_mass (p : ℕ) [NeZero p]
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ x, ‖f p x‖ ≤ 1)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) :
    (∑ x : ZMod p, ‖correlationPrimeFactor f side a b p x‖) ≤ p := by
  have ha : (∑ x : ZMod p, ‖densityFourier (f p) ((a p : ZMod p) * x)‖ ^ 2) ≤ p := by
    rw [unit_dilation_energy]
    exact densityFourier_energy_le _ hf
  have hb : (∑ x : ZMod p, ‖densityFourier (f p) ((b p : ZMod p) * x)‖ ^ 2) ≤ p := by
    rw [unit_dilation_energy]
    exact densityFourier_energy_le _ hf
  simp only [correlationPrimeFactor, primeDensityFourier_eq]
  cases side p with
  | left => exact norm_sum_le_of_energy _ ha
  | right => simpa only [Complex.norm_conj] using norm_sum_le_of_energy _ hb
  | both => exact norm_product_sum_le_of_energy _ _ ha hb

theorem primeCRTFunction_mass (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ)
    (hF : ∀ p (h : p ∈ ps), let : NeZero p := ⟨(hp p h).ne_zero⟩;
      (∑ x : ZMod p, ‖F p x‖) ≤ p) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (∑ x : ZMod ps.prod, ‖primeCRTFunction ps hp hc F x‖) ≤ ps.prod := by
  induction ps with
  | nil =>
    intro _
    simp only [primeCRTFunction, norm_one, Finset.sum_const, nsmul_eq_mul,
      mul_one, List.prod_nil, Nat.cast_one]
    have hcard : (Finset.univ : Finset (ZMod ([] : List ℕ).prod)).card = 1 := by
      rw [Finset.card_univ, ZMod.card, List.prod_nil]
    exact_mod_cast hcard.le
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    intro _
    let e := ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)
    change (∑ x : ZMod (p * ps.prod), ‖F p (e x).1 * primeCRTFunction ps hp' hcp.2 F (e x).2‖) ≤ _
    rw [← e.symm.bijective.sum_comp (fun x =>
      ‖F p (e x).1 * primeCRTFunction ps hp' hcp.2 F (e x).2‖)]
    simp only [e.apply_symm_apply]
    simp only [Fintype.sum_prod_type, norm_mul]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    have ht := ih hp' hcp.2 (fun q hq => hF q (List.mem_cons_of_mem p hq))
    simpa only [List.prod_cons, Nat.cast_mul] using
      mul_le_mul (hF p List.mem_cons_self) ht (by positivity) (Nat.cast_nonneg p)

/-- The original two density transforms have a common periodic model whose
absolute mass is at most one after probability normalization. -/
theorem primeSet_density_correlation_mass_model (U V : Finset ℕ)
    (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p))
    (vp : (ZMod U.toList.prod)ˣ) (vq : (ZMod V.toList.prod)ˣ) :
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
    let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
    ∃ F : ZMod (U ∪ V).toList.prod → ℂ,
      (∀ n : ℤ,
        densityFourier (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) S).value
          ((vp : ZMod U.toList.prod) * (n : ZMod U.toList.prod)) *
        conj (densityFourier (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) S).value
          ((vq : ZMod V.toList.prod) * (n : ZMod V.toList.prod))) = F (n : ZMod (U ∪ V).toList.prod)) ∧
      (let : NeZero (U ∪ V).toList.prod := ⟨(prime_list_prod_pos _
        (primeSet_list_prime (U ∪ V) (fun p hp => (Finset.mem_union.mp hp).elim (hpU p) (hpV p)))).ne'⟩
       (∑ x : ZMod (U ∪ V).toList.prod, ‖F x‖) ≤ (U ∪ V).toList.prod) := by
  intro _ _
  let hpUV : ∀ p ∈ U ∪ V, p.Prime := fun p hp =>
    (Finset.mem_union.mp hp).elim (hpU p) (hpV p)
  let : NeZero (U ∪ V).toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime _ hpUV)).ne'⟩
  let f : ∀ p : ℕ, ZMod p → ℂ := fun p x => (centeredDensity (S p) x : ℂ)
  obtain ⟨a, ha⟩ := densityFourier_centered_unit_product U.toList
    (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) S vp
  obtain ⟨b, hb⟩ := densityFourier_centered_unit_product V.toList
    (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) S vq
  refine ⟨primeCRTFunction (U ∪ V).toList (primeSet_list_prime _ hpUV)
    (primeSet_list_coprime _ hpUV) (correlationPrimeFactor f (supportCorrelationSide U V) a b), ?_, ?_⟩
  · intro n
    rw [ha, hb, primeCRTFunction_intCast,
      ← List.prod_toFinset _ U.nodup_toList,
      ← List.prod_toFinset _ V.nodup_toList,
      ← List.prod_toFinset _ (U ∪ V).nodup_toList]
    simp only [Finset.toList_toFinset]
    exact (local_correlation_product U V (U ∪ V) rfl f a b n).symm
  · apply primeCRTFunction_mass
    intro p hp
    let : NeZero p := ⟨(primeSet_list_prime _ hpUV p hp).ne_zero⟩
    apply correlationPrimeFactor_mass
    intro x
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using centeredDensity_abs_le (S p) x

end Ostmann

end OAI
