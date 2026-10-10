import Mathlib.NumberTheory.DirichletCharacter.Bounds
import OAI.NumberTheory.Ostmann.Characters.RepeatedPrimePeriod
import OAI.NumberTheory.Ostmann.Characters.RepeatedCharacterCancellation

namespace OAI

/-! # The original product bounds imply the short-period cancellation -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def characterTupleSum {I : Type*} [Fintype I] (p : I → ℕ)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑' a : ℤ, (∏ i, χ i (p i) ((a : ZMod (p i)) - t (p i))) * ψ ((a : ℝ) / X)

theorem repeated_tuple_short_period {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (X H R : ℝ) (hR : 0 < R)
    (hsmall : ∀ i, H * R < p i) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    H < X / (∏ r ∈ sampledPrimeSet p, r : ℕ) := by
  let P := sampledPrimeSet p
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp l
  have hmem (l : I) : p l ∈ P := Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  have hcount : 2 ≤ primeSlotCount p (p i) := by
    have hh : ({i, j} : Finset I) ⊆ Finset.univ.filter (fun l => p l = p i) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · simp
      · simp [heq]
    have hc := Finset.card_le_card hh
    simpa only [Finset.card_pair hij, primeSlotCount] using hc
  have hperiod : (p i) * (∏ r ∈ P, r) ≤ ∏ l, p l :=
    repeated_prime_period_bound p (fun l => (hp l).one_lt.le) (hmem i) hcount
  have hpos : (0 : ℝ) < (∏ r ∈ P, r : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun r hr => (hP r hr).pos)
  have hupper : (p i : ℝ) * (∏ r ∈ P, r : ℕ) ≤ X * R := by
    have hh : (p i : ℝ) * (∏ r ∈ P, r : ℕ) ≤ (∏ l, p l : ℕ) := by exact_mod_cast hperiod
    exact hh.trans (by simpa only [Nat.cast_prod] using hprod)
  have hshort : H < X / (∏ r ∈ P, r : ℕ) := by
    rw [lt_div_iff₀ hpos]
    have hh := mul_lt_mul_of_pos_right (hsmall i) hpos
    have hr : (H * (∏ r ∈ P, r : ℕ)) * R < X * R := by nlinarith
    exact (mul_lt_mul_iff_left₀ hR).mp hr
  exact hshort

theorem repeated_tuple_singleton_zero {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < p i) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j)
    (k : I) (hk : ∀ l, p l = p k → l = k) (hχ : χ k (p k) ≠ 1) :
    characterTupleSum p χ t ψ X = 0 := by
  let P := sampledPrimeSet p
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp l
  have hmem (l : I) : p l ∈ P := Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  let q : I → P := fun l => ⟨p l, hmem l⟩
  have hshort := repeated_tuple_short_period p hp X H R hR hsmall hprod i j hij heq
  have hshort' : H < X / (∏ r : P, (r : ℕ)) := by
    have he : (∏ r : P, (r : ℕ)) = ∏ r ∈ P, r := Finset.prod_coe_sort P (fun r : ℕ => r)
    rw [he]
    exact hshort
  exact grouped_singleton_poisson_zero P hP q χ t k
    (fun l h => hk l (congrArg Subtype.val h)) hχ ψ X H hX hshort' hsupp

theorem repeated_tuple_sum_bound {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < p i) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    ‖characterTupleSum p χ t ψ X‖ ≤ X * ‖𝓕 ψ 0‖ := by
  let P := sampledPrimeSet p
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp l
  have hmem (l : I) : p l ∈ P := Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  let q : I → P := fun l => ⟨p l, hmem l⟩
  let v : P → ℕ := fun r => r
  let : ∀ r : P, NeZero (r : ℕ) := fun r => ⟨(hP r r.property).ne_zero⟩
  let : NeZero (∏ r : P, (r : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun r : P => (r : ℕ))
      (fun r _ => (hP r r.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  let F := tupleCRTFunction v hc (groupedSlotValue P q χ t)
  have hF (a : ZMod (∏ r : P, (r : ℕ))) : ‖F a‖ ≤ 1 := by
    dsimp [F, tupleCRTFunction, groupedSlotValue]
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun r _ => norm_nonneg _)
    intro r _
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun l _ => norm_nonneg _) (fun l _ => (χ l r).norm_le_one _)
  have hshort : H < X / (∏ r : P, (r : ℕ)) := by
    have hs := repeated_tuple_short_period p hp X H R hR hsmall hprod i j hij heq
    have he : (∏ r : P, (r : ℕ)) = ∏ r ∈ P, r := Finset.prod_coe_sort P (fun r : ℕ => r)
    rw [he]
    exact hs
  have hb := short_period_character_sum_bound F hF ψ X H hX hshort hsupp
  simpa only [F, tupleCRTFunction_intCast, groupedSlotValue_product, characterTupleSum] using hb

end Ostmann

end OAI
