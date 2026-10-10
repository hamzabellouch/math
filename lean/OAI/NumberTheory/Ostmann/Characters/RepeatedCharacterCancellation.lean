import OAI.NumberTheory.Ostmann.Characters.TupleCRTFourier
import OAI.NumberTheory.Ostmann.Arithmetic.PeriodicWeightPoisson
import OAI.NumberTheory.Ostmann.Characters.GaussFourier

namespace OAI

/-! # A singleton prime makes a short-period repeated tuple vanish -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem periodic_poisson_complete_mean {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hH : H < X / N) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)) =
      (X : ℂ) * 𝓕 ψ 0 * additiveFourier F 0 := by
  rw [scaled_periodic_poisson F ψ X hX]
  have hn (n : ℤ) (hne : n ≠ 0) :
      𝓕 ψ ((n : ℝ) * X / N) * additiveFourier F (-(n : ZMod N)) = 0 := by
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |n| by have hh := abs_pos.mpr hne; omega)
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hlarge : H < |(n : ℝ) * X / N| := by
      rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hN, div_eq_mul_inv, mul_assoc]
      exact hH.trans_le (by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_right habs (mul_nonneg hX.le (inv_nonneg.mpr hN.le)))
    rw [hsupp _ hlarge, zero_mul]
  rw [tsum_eq_single 0 hn]
  simp only [Int.cast_zero, zero_mul, zero_div, neg_zero]
  ring

noncomputable def groupedSlotValue {I : Type*} [Fintype I] (P : Finset ℕ)
    (p : I → P) (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q)
    (t : ∀ q : ℕ, ZMod q) (q : P) (x : ZMod (q : ℕ)) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => p i = q), χ i q (x - t q)

theorem groupedSlotValue_product {I : Type*} [Fintype I] (P : Finset ℕ)
    (p : I → P) (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q)
    (t : ∀ q : ℕ, ZMod q) (n : ℤ) :
    (∏ q : P, groupedSlotValue P p χ t q (n : ZMod (q : ℕ))) =
      ∏ i, χ i (p i) ((n : ZMod (p i : ℕ)) - t (p i)) := by
  unfold groupedSlotValue
  have he (q : P) :
      (∏ i ∈ Finset.univ.filter (fun i => p i = q), χ i q ((n : ZMod (q : ℕ)) - t q)) =
        ∏ i ∈ Finset.univ.filter (fun i => p i = q),
          χ i (p i) ((n : ZMod (p i : ℕ)) - t (p i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [he]
  exact Finset.prod_fiberwise Finset.univ p _

theorem groupedSlotValue_singleton {I : Type*} [Fintype I] (P : Finset ℕ)
    (p : I → P) (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q)
    (t : ∀ q : ℕ, ZMod q) (i : I) (hi : ∀ j, p j = p i → j = i) :
    groupedSlotValue P p χ t (p i) = fun x => χ i (p i) (x - t (p i)) := by
  have hf : Finset.univ.filter (fun j => p j = p i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hi j, fun h => by rw [h]⟩
  funext x
  simp only [groupedSlotValue, hf, Finset.prod_singleton]

theorem grouped_singleton_fourier_zero {I : Type*} [Fintype I] (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (i : I) (hi : ∀ j, p j = p i → j = i) (hχ : χ i (p i) ≠ 1) :
    let q : P → ℕ := fun q => q
    let : ∀ q : P, NeZero (q : ℕ) := fun q => ⟨(hP q q.property).ne_zero⟩
    let : NeZero (∏ q : P, (q : ℕ)) := ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ)) (fun q _ => (hP q q.property).pos)).ne'⟩
    let hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
      fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
        (fun h => hab (Subtype.ext h))
    additiveFourier (tupleCRTFunction q hc (groupedSlotValue P p χ t)) 0 = 0 := by
  intro q _ _ hc
  rw [tupleCRTFunction_fourier]
  apply Finset.prod_eq_zero (Finset.mem_univ (p i))
  simp only [map_zero, Pi.zero_apply, mul_zero, groupedSlotValue_singleton P p χ t i hi]
  let : Fact (p i : ℕ).Prime := ⟨hP (p i) (p i).property⟩
  rw [additiveFourier_translate, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  exact additiveFourier_mulChar_zero (χ i (p i)) hχ

/-- Once the repeated tuple's actual period is below the Fourier cutoff,
one singly occurring nonprincipal character annihilates its entire sum. -/
theorem grouped_singleton_poisson_zero {I : Type*} [Fintype I] (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (i : I) (hi : ∀ j, p j = p i → j = i) (hχ : χ i (p i) ≠ 1)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, (∏ j, χ j (p j) ((n : ZMod (p j : ℕ)) - t (p j))) *
      ψ ((n : ℝ) / X)) = 0 := by
  let q : P → ℕ := fun q => q
  let : ∀ q : P, NeZero (q : ℕ) := fun q => ⟨(hP q q.property).ne_zero⟩
  let : NeZero (∏ q : P, (q : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ))
      (fun q _ => (hP q q.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  have hz : additiveFourier (tupleCRTFunction q hc (groupedSlotValue P p χ t)) 0 = 0 :=
    grouped_singleton_fourier_zero P hP p χ t i hi hχ
  have hs := periodic_poisson_complete_mean (tupleCRTFunction q hc (groupedSlotValue P p χ t))
    ψ X H hX hperiod hsupp
  simp_rw [tupleCRTFunction_intCast, groupedSlotValue_product] at hs
  rw [hs, hz, mul_zero]

theorem bounded_complete_mean_norm {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) : ‖additiveFourier F 0‖ ≤ 1 := by
  have hsum : ‖∑ x, F x‖ ≤ (N : ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ x : ZMod N, ‖F x‖) ≤ ∑ _x : ZMod N, (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => hF x)
      _ = N := by simp
  rw [additiveFourier_apply]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, norm_mul,
    norm_inv, Complex.norm_natCast]
  calc
    (N : ℝ)⁻¹ * ‖∑ x, F x‖ ≤ (N : ℝ)⁻¹ * N :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (by exact_mod_cast NeZero.ne N)

theorem short_period_character_sum_bound {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / N) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ‖∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)‖ ≤ X * ‖𝓕 ψ 0‖ := by
  rw [periodic_poisson_complete_mean F ψ X H hX hperiod hsupp, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
  exact mul_le_of_le_one_right (by positivity) (bounded_complete_mean_norm F hF)

end Ostmann

end OAI
