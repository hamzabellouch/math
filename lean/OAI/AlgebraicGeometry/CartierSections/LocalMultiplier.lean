/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license.
Authors: OpenAI
-/
import Mathlib

namespace OAI

/-!
# Local principality and rounded divisor inequalities

Local algebra for uniform Cartier sections.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal

namespace CartierSections.LocalMultiplier

/-- In a local domain, if finitely many principal ideals sum to a nonzero
principal ideal, one generator divided by the latter generator is a unit.
This is the local invertible-sum-ideal assertion used on the log resolution. -/
theorem exists_unit_quotient_of_span_eq
    {A ι : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [Fintype ι]
    (f : ι → A) (g : A) (hg : g ≠ 0)
    (hspan : Ideal.span (Set.range f) = Ideal.span ({g} : Set A)) :
    ∃ i b, IsUnit b ∧ f i = g * b := by
  classical
  have hdvd (i : ι) : g ∣ f i := by
    apply Ideal.mem_span_singleton.mp
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose b hb using hdvd
  have hmem : g ∈ Ideal.span (Set.range f) := by
    rw [hspan]
    exact Ideal.subset_span (Set.mem_singleton g)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hsum : ∑ i, c i * b i = 1 := by
    apply mul_left_cancel₀ hg
    calc
      g * ∑ i, c i * b i = ∑ i, c i * (g * b i) := by
        rw [Finset.mul_sum]
        congr 1
        funext i
        ring
      _ = g := by simpa only [← hb] using hc
      _ = g * 1 := by simp
  have hu : IsUnit (∑ i, c i * b i) := hsum ▸ isUnit_one
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum hu
  exact ⟨i, b i, (IsUnit.mul_iff.mp hi).2, hb i⟩

/-- Literal Laurent-monomial membership in the rounded divisor sheaf becomes
a strict linear inequality. The strict inequality retains rounding walls. -/
theorem rounding_criterion (n : ℤ) (K t : ℝ) :
    -n ≤ ⌈K - t⌉ ↔ t < K + n + 1 := by
  rw [Int.le_ceil_iff]
  push_cast
  constructor <;> intro h <;> linarith

/-- Exponents giving a fixed Laurent monomial in a mixed rounded divisor.
`D i j` is the coefficient of the i-th resolved summand along the j-th snc
component. `K j` and `n j` are the relative-canonical and monomial exponents. -/
def admittingExponents {ι κ : Type*} [Fintype ι]
    (c : ℝ) (D : ι → κ → ℝ) (K : κ → ℝ) (n : κ → ℤ) : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = c ∧
    ∀ j, -n j ≤ ⌈K j - ∑ i, p i * D i j⌉}

theorem mem_admittingExponents_iff {ι κ : Type*} [Fintype ι]
    (c : ℝ) (D : ι → κ → ℝ) (K : κ → ℝ) (n : κ → ℤ) (p : ι → ℝ) :
    p ∈ admittingExponents c D K n ↔
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = c ∧
      ∀ j, (∑ i, p i * D i j) < K j + n j + 1 := by
  simp only [admittingExponents, Set.mem_ofPred_eq, rounding_criterion]

/-- The admitting set is convex, including all simplex faces. -/
theorem admittingExponents_convex {ι κ : Type*} [Fintype ι]
    (c : ℝ) (D : ι → κ → ℝ) (K : κ → ℝ) (n : κ → ℤ) :
    Convex ℝ (admittingExponents c D K n) := by
  rw [convex_iff_forall_pos]
  intro p hp q hq a b ha hb hab
  rw [mem_admittingExponents_iff] at hp hq ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha.le (hp.1 i)) (mul_nonneg hb.le (hq.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.2.1, hq.2.1]
    rw [← add_mul, hab, one_mul]
  · intro j
    have hs : (∑ i, (a • p + b • q) i * D i j) =
        a * (∑ i, p i * D i j) + b * (∑ i, q i * D i j) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hs]
    have h1 := mul_lt_mul_of_pos_left (hp.2.2 j) ha
    have h2 := mul_lt_mul_of_pos_left (hq.2.2 j) hb
    calc
      _ < a * (K j + n j + 1) + b * (K j + n j + 1) := add_lt_add h1 h2
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- If the resolved sum divisor is a coefficientwise minimum achieved by one
summand, the admitting set is nonempty exactly for the target Laurent monomials.
This bridges actual local principality to the rounding-cell calculation. -/
theorem admittingExponents_nonempty_iff {ι κ : Type*} [Fintype ι]
    (c : ℝ) (hc : 0 ≤ c) (D : ι → κ → ℝ) (d K : κ → ℝ) (n : κ → ℤ)
    (hle : ∀ i j, d j ≤ D i j) (i₀ : ι) (heq : ∀ j, D i₀ j = d j) :
    (admittingExponents c D K n).Nonempty ↔
      ∀ j, -n j ≤ ⌈K j - c * d j⌉ := by
  classical
  constructor
  · rintro ⟨p, hp⟩ j
    rw [mem_admittingExponents_iff] at hp
    rw [rounding_criterion]
    have h : c * d j ≤ ∑ i, p i * D i j := by
      rw [← hp.2.1, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i j) (hp.1 i)
    exact h.trans_lt (hp.2.2 j)
  · intro h
    refine ⟨Pi.single i₀ c, ?_⟩
    rw [mem_admittingExponents_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = i₀
      · subst i
        simpa using hc
      · simp [hi]
    · simp
    · intro j
      simpa [Pi.single_apply, heq j] using (rounding_criterion (n j) (K j) (c * d j)).mp (h j)

/-- The simplex on which the rounding subdivision is made; no face is omitted. -/
def exponentSimplex {ι : Type*} [Fintype ι] (c : ℝ) : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = c}

/-- For finitely many snc components, the admitting set is relatively open
in the closed exponent simplex, not in its affine ambient space. -/
theorem admittingExponents_relativelyOpen {ι κ : Type*} [Fintype ι] [Finite κ]
    (c : ℝ) (D : ι → κ → ℝ) (K : κ → ℝ) (n : κ → ℤ) :
    IsOpen {p : exponentSimplex (ι := ι) c |
      (p : ι → ℝ) ∈ admittingExponents c D K n} := by
  have heq : {p : exponentSimplex (ι := ι) c |
      (p : ι → ℝ) ∈ admittingExponents c D K n} =
      ⋂ j, {p : exponentSimplex (ι := ι) c |
        (∑ i, p.val i * D i j) < K j + n j + 1} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, mem_admittingExponents_iff]
    constructor
    · exact fun h => h.2.2
    · exact fun h => ⟨p.property.1, p.property.2, h⟩
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt _ continuous_const
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

/-- A nonempty coefficientwise admitting region is contractible. -/
theorem admittingExponents_contractible {ι κ : Type*} [Fintype ι]
    (c : ℝ) (D : ι → κ → ℝ) (K : κ → ℝ) (n : κ → ℤ)
    (hne : (admittingExponents c D K n).Nonempty) :
    ContractibleSpace (admittingExponents c D K n) :=
  (admittingExponents_convex c D K n).contractibleSpace hne

/-- In a local ring even an arbitrarily indexed sum of ideals can be the unit
ideal only if one summand is the unit ideal. Here `iSup` is the literal ideal
sum; no finiteness of the real exponent index set is required. -/
theorem exists_eq_top_of_iSup_eq_top {A ι : Type*}
    [CommRing A] [IsLocalRing A] (I : ι → Ideal A)
    (hI : (⨆ i, I i) = ⊤) : ∃ i, I i = ⊤ := by
  by_contra! h
  have hs : (⨆ i, I i) ≤ IsLocalRing.maximalIdeal A :=
    iSup_le fun i => IsLocalRing.le_maximalIdeal (h i)
  rw [hI] at hs
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp hs)

end CartierSections.LocalMultiplier

end

end OAI
