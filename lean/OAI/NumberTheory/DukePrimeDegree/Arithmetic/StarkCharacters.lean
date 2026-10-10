import OAI.NumberTheory.PrimePackets.CharacterPairs

namespace OAI

/-!
# Simple zeros in cyclic Artin factorizations

The cyclic step in Stark's exceptional-zero argument uses finite,
nonnegative orders of the Hecke factors. If their product has a simple
zero, exactly one factor has order one. Its zero-order character is
therefore a one-dimensional character, expressed using the actual
meromorphic orders in the cyclic factorization.
-/

open scoped BigOperators

namespace DukePrimeDegree

private theorem sum_nat_one_support {I : Type*} [Fintype I]
    (m : I → ℕ) (hm : ∑ i, m i = 1) :
    ∃ i, m i = 1 ∧ ∀ j, j ≠ i → m j = 0 := by
  classical
  have hex : ∃ i, m i ≠ 0 := by
    by_contra! h
    simp [h] at hm
  obtain ⟨i, hi⟩ := hex
  have hle : m i ≤ 1 := by
    rw [← hm]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
  have hmi : m i = 1 := by omega
  refine ⟨i, hmi, ?_⟩
  have hs : ∑ j ∈ Finset.univ.erase i, m j = 0 := by
    have H := Finset.sum_erase_add Finset.univ m (Finset.mem_univ i)
    rw [hmi, hm] at H
    omega
  intro j hji
  have hle' := Finset.single_le_sum (s := Finset.univ.erase i)
    (f := m) (fun k _ => Nat.zero_le (m k))
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  rw [hs] at hle'
  omega

/-- A simple zero of a product of holomorphic nonzero factors comes
from exactly one simple factor. The finite nonnegative order hypothesis
is supplied by the proved Hecke continuation theorems. -/
theorem unique_factor_order_of_simple_product
    {I : Type*} [Fintype I] (f : I → ℂ → ℂ) (β : ℂ)
    (hf : ∀ i, MeromorphicAt (f i) β)
    (hord : ∀ i, ∃ m : ℕ, meromorphicOrderAt (f i) β = (m : WithTop ℤ))
    (hsimple : meromorphicOrderAt (fun z => ∏ i, f i z) β = 1) :
    ∃ i, meromorphicOrderAt (f i) β = 1 ∧
      ∀ j, j ≠ i → meromorphicOrderAt (f j) β = 0 := by
  classical
  choose m hm using hord
  have hsum : ∑ i, m i = 1 := by
    have H := meromorphicOrderAt_fun_prod (s := Finset.univ) (fun i _ => hf i)
    rw [hsimple] at H
    simp only [hm] at H
    exact_mod_cast H.symm
  obtain ⟨i, hi, hrest⟩ := sum_nat_one_support m hsum
  refine ⟨i, ?_, ?_⟩
  · rw [hm, hi]
    rfl
  · intro j hji
    rw [hm, hrest j hji]
    rfl

/-- The zero-order sum on a cyclic group is one linear character once
the orders of its factors sum to one. -/
theorem cyclic_zero_order_character
    {C : Type*} [Group C] [Fintype (C →* ℂˣ)]
    (m : (C →* ℂˣ) → ℕ) (hm : ∑ χ, m χ = 1) :
    ∃ χ : C →* ℂˣ, ∀ g : C,
      (∑ ψ : C →* ℂˣ, (m ψ : ℂ) * (ψ g : ℂ)) = (χ g : ℂ) := by
  classical
  obtain ⟨χ, hχ, hrest⟩ := sum_nat_one_support m hm
  refine ⟨χ, fun g => ?_⟩
  rw [Finset.sum_eq_single χ]
  · simp [hχ]
  · intro ψ _ hψ
    simp [hrest ψ hψ]
  · simp

/-- Complex conjugation of a one-dimensional character. -/
def conjugateLinearCharacter {C : Type*} [Group C] (χ : C →* ℂˣ) : C →* ℂˣ :=
  (Units.map (starRingEnd ℂ).toMonoidHom).comp χ

@[simp] theorem conjugateLinearCharacter_apply {C : Type*} [Group C]
    (χ : C →* ℂˣ) (g : C) :
    (conjugateLinearCharacter χ g : ℂ) = starRingEnd ℂ (χ g : ℂ) := rfl

/-- At a real simple zero, conjugation-invariance of the factor orders
forces the unique character supporting that zero to be real-valued. -/
theorem real_character_of_simple_conjugate_orders
    {C : Type*} [Group C] [Fintype (C →* ℂˣ)]
    (m : (C →* ℂˣ) → ℕ) (hm : ∑ χ, m χ = 1)
    (hc : ∀ χ, m (conjugateLinearCharacter χ) = m χ) :
    ∃ χ : C →* ℂˣ, m χ = 1 ∧
      (∀ ψ, ψ ≠ χ → m ψ = 0) ∧ ∀ g, (χ g : ℂ).im = 0 := by
  classical
  obtain ⟨χ, hχ, hrest⟩ := sum_nat_one_support m hm
  have he : conjugateLinearCharacter χ = χ := by
    by_contra hn
    have hzero := hrest _ hn
    rw [hc, hχ] at hzero
    norm_num at hzero
  refine ⟨χ, hχ, hrest, fun g => ?_⟩
  have H := congrArg (fun ψ : C →* ℂˣ => (ψ g : ℂ).im) he
  simp only [conjugateLinearCharacter_apply, Complex.conj_im] at H
  linarith

/-- A real-valued complex linear character regarded as a real character. -/
def realLinearCharacter {C : Type*} [Group C] (χ : C →* ℂˣ)
    (hr : ∀ g, (χ g : ℂ).im = 0) : C →* ℝˣ where
  toFun g :=
    { val := (χ g : ℂ).re
      inv := (χ g⁻¹ : ℂ).re
      val_inv := by
        have H := congrArg (fun z : ℂˣ => (z : ℂ).re) (χ.map_mul g g⁻¹)
        simp only [mul_inv_cancel, map_one, Units.val_mul, Units.val_one,
          Complex.mul_re, hr, mul_zero, sub_zero, Complex.one_re] at H
        exact H.symm
      inv_val := by
        have H := congrArg (fun z : ℂˣ => (z : ℂ).re) (χ.map_mul g⁻¹ g)
        simp only [inv_mul_cancel, map_one, Units.val_mul, Units.val_one,
          Complex.mul_re, hr, mul_zero, sub_zero, Complex.one_re] at H
        exact H.symm }
  map_one' := by apply Units.ext; simp
  map_mul' g h := by
    apply Units.ext
    change (χ (g * h) : ℂ).re = (χ g : ℂ).re * (χ h : ℂ).re
    rw [map_mul, Units.val_mul, Complex.mul_re, hr, hr]
    ring

@[simp] theorem realLinearCharacter_apply {C : Type*} [Group C]
    (χ : C →* ℂˣ) (hr : ∀ g, (χ g : ℂ).im = 0) (g : C) :
    (realLinearCharacter χ hr g : ℝ) = (χ g : ℂ).re := rfl

end DukePrimeDegree

end OAI
