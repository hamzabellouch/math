import OAI.AlgebraicGeometry.CartierSections.EulerOperators
import Mathlib.Data.Finsupp.PWO
import Mathlib.RingTheory.Ideal.BigOperators

namespace OAI

/-!
# Isolation of algebraic power series jets

Bounded Euler and transverse differential operators isolate a monomial modulo the ideal
of strictly higher weight. Dickson finiteness identifies support conditions with membership
in algebraic monomial ideals.
-/

open scoped BigOperators

namespace CartierSections

section IsolationCoefficients
variable {ι k : Type*} [Fintype ι] [Field k] [CharZero k]

/-- Bounded Euler and partial operators isolate the chosen boundary exponent. -/
theorem euler_isolates_coefficients
    (B : Finset ι) (N : ℕ) (w : ι → ℝ)
    (hwzero : ∀ i ∉ B, w i = 0)
    {f : MvPowerSeries ι k} {γ : ι →₀ ℕ}
    (hγ : IsInitialExponent w f γ)
    (hbound : ∀ d, IsInitialExponent w f d → partialDegree B d ≤ N) :
    ∃ α β : ι →₀ ℕ,
      α + β = γ ∧
      (∀ i ∉ B, α i = 0) ∧ (∀ i ∈ B, β i = 0) ∧
      let g := iterPartial β.toMultiset.toList (iterEuler (eulerFactors B N α) f)
      MvPowerSeries.coeff α g ≠ 0 ∧
      ∀ d, MvPowerSeries.coeff d g ≠ 0 →
        realWeight w α ≤ realWeight w d ∧
        (realWeight w d = realWeight w α → ∀ i ∈ B, d i = α i) := by
  classical
  let α := γ.filter (fun i => i ∈ B)
  let β := γ.filter (fun i => i ∉ B)
  have hab : α + β = γ := by
    ext i
    simp [α, β]
  have hα : ∀ i ∉ B, α i = 0 := by
    intro i hi; simp [α, hi]
  have hβ : ∀ i ∈ B, β i = 0 := by
    intro i hi; simp [β, hi]
  have hwβ : realWeight w β = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ B
    · simp [hβ i hi]
    · simp [hwzero i hi]
  have hwγ : realWeight w γ = realWeight w α := by
    rw [← hab, realWeight_add, hwβ, add_zero]
  refine ⟨α, β, hab, hα, hβ, ?_⟩
  dsimp only
  constructor
  · rw [coeff_iterPartial_ne_zero_iff, listExponent_toList, hab]
    apply coeff_eulerFactors_self_ne_zero B N α γ _ hγ.1
    intro i hi; simp [α, hi]
  · intro d hd
    have hdE : MvPowerSeries.coeff (d + β) (iterEuler (eulerFactors B N α) f) ≠ 0 := by
      simpa using (coeff_iterPartial_ne_zero_iff _ _ d).mp hd
    have hdf : MvPowerSeries.coeff (d + β) f ≠ 0 := by
      intro h; apply hdE; simp [h]
    have hweight : realWeight w α ≤ realWeight w d := by
      simpa [realWeight_add, hwβ, hwγ] using hγ.2 (d + β) hdf
    refine ⟨hweight, ?_⟩
    intro heq i hi
    have hinit : IsInitialExponent w f (d + β) := by
      refine ⟨hdf, ?_⟩
      intro e he
      simpa [realWeight_add, hwβ, heq, hwγ] using hγ.2 e he
    have hdegree := hbound (d + β) hinit
    have hdi : d i ≤ N := by
      have hle : (d + β) i ≤ partialDegree B (d + β) :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
      simpa [hβ i hi] using hle.trans hdegree
    by_contra hne
    apply hdE
    apply coeff_eulerFactors_eq_zero B N α (d + β) _ f
    exact ⟨i, hi, by simpa [hβ i hi] using hdi, by simpa [hβ i hi] using hne⟩

omit [CharZero k] in
/-- An isolated initial coefficient is a monomial times a formal unit,
up to terms of strictly greater weight. -/
theorem isolated_series_unit_remainder
    (B : Finset ι) (w : ι → ℝ) (α : ι →₀ ℕ)
    (hα : ∀ i ∉ B, α i = 0)
    (g : MvPowerSeries ι k) (hcoeff : MvPowerSeries.coeff α g ≠ 0)
    (hle : ∀ d, MvPowerSeries.coeff d g ≠ 0 → realWeight w α ≤ realWeight w d)
    (hisolate : ∀ d, MvPowerSeries.coeff d g ≠ 0 →
      realWeight w d = realWeight w α → ∀ i ∈ B, d i = α i) :
    ∃ u q : MvPowerSeries ι k, IsUnit u ∧
      g = MvPowerSeries.monomial α 1 * u + q ∧
      ∀ d, MvPowerSeries.coeff d q ≠ 0 → realWeight w α < realWeight w d := by
  classical
  let u : MvPowerSeries ι k := fun d => MvPowerSeries.coeff (α + d) g
  let q := g - MvPowerSeries.monomial α 1 * u
  have hu : IsUnit u := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    change MvPowerSeries.coeff (α + 0) g ≠ 0
    simpa using hcoeff
  refine ⟨u, q, hu, by simp [q], ?_⟩
  intro d hdq
  have hnot : ¬ α ≤ d := by
    intro had
    apply hdq
    simp only [q, map_sub, MvPowerSeries.coeff_monomial_mul, ite_eq_left had, one_mul]
    change MvPowerSeries.coeff d g - MvPowerSeries.coeff (α + (d - α)) g = 0
    rw [add_tsub_cancel_of_le had, sub_self]
  have hdg : MvPowerSeries.coeff d g ≠ 0 := by
    simpa [q, MvPowerSeries.coeff_monomial_mul, ite_eq_right hnot] using hdq
  refine lt_of_le_of_ne (hle d hdg) ?_
  intro heq
  apply hnot
  intro i
  by_cases hi : i ∈ B
  · exact (hisolate d hdg heq.symm i hi).ge
  · simp [hα i hi]

end IsolationCoefficients

section MonomialIdeals
variable {ι k : Type*} [CommRing k]

/-- Dickson finiteness supplies a finite subset of any collection of exponent
vectors, with every vector dominating one of those generators. -/
theorem finite_dominated_generators [Fintype ι] (S : Set (ι →₀ ℕ)) :
    ∃ T : Finset (ι →₀ ℕ), (↑T : Set (ι →₀ ℕ)) ⊆ S ∧
      ∀ d ∈ S, ∃ e ∈ T, e ≤ d := by
  classical
  let M : Set (ι →₀ ℕ) := {e | Minimal (fun a => a ∈ S) e}
  have hM : M.Finite := by
    apply WellQuasiOrderedLE.finite_of_isAntichain
    intro a ha b hb hne hab
    exact hne (le_antisymm hab (hb.2 ha.1 hab))
  refine ⟨hM.toFinset, ?_, ?_⟩
  · intro e he
    exact (hM.mem_toFinset.mp he).1
  · intro d hd
    obtain ⟨e, hed, he⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hd
    exact ⟨e, hM.mem_toFinset.mpr he, hed⟩

/-- A formal power series supported on multiples of finitely many monomials
is a finite sum of those monomials times formal power series. -/
theorem series_mem_span_finite_monomials
    (T : Finset (ι →₀ ℕ)) (f : MvPowerSeries ι k)
    (hcover : ∀ d, MvPowerSeries.coeff d f ≠ 0 → ∃ e ∈ T, e ≤ d) :
    f ∈ Ideal.span ((fun e => (MvPowerSeries.monomial e 1 : MvPowerSeries ι k)) ''
      (T : Set (ι →₀ ℕ))) := by
  classical
  let choose : (ι →₀ ℕ) → (ι →₀ ℕ) := fun d =>
    if h : MvPowerSeries.coeff d f ≠ 0 then (hcover d h).choose else 0
  have hchoose (d) (hd : MvPowerSeries.coeff d f ≠ 0) :
      choose d ∈ T ∧ choose d ≤ d := by
    simpa only [choose, dite_eq_left hd] using (hcover d hd).choose_spec
  let u : (ι →₀ ℕ) → MvPowerSeries ι k := fun e a =>
    if choose (e + a) = e then MvPowerSeries.coeff (e + a) f else 0
  have hcoeff (e d : ι →₀ ℕ) :
      MvPowerSeries.coeff d (MvPowerSeries.monomial e 1 * u e) =
      if e ≤ d ∧ choose d = e then MvPowerSeries.coeff d f else 0 := by
    rw [MvPowerSeries.coeff_monomial_mul]
    by_cases hed : e ≤ d
    · simp only [one_mul, hed, true_and]
      change (if choose (e + (d - e)) = e then MvPowerSeries.coeff (e + (d - e)) f else 0) = _
      rw [add_tsub_cancel_of_le hed]
    · simp [hed]
  have heq : f = ∑ e ∈ T, MvPowerSeries.monomial e 1 * u e := by
    ext d
    simp only [map_sum, hcoeff]
    by_cases hd : MvPowerSeries.coeff d f = 0
    · simp [hd]
    · have hc := hchoose d hd
      rw [Finset.sum_eq_single_of_mem (choose d) hc.1]
      · simp [hc.2]
      · intro e he hne
        simp [Ne.symm hne]
  rw [heq]
  apply Ideal.sum_mem
  intro e he
  apply Ideal.mul_mem_right
  exact Ideal.subset_span ⟨e, he, rfl⟩

/-- Coefficient support in an arbitrary monomial up-set implies membership
in the algebraic ideal span. -/
theorem series_mem_span_monomials [Fintype ι]
    (S : Set (ι →₀ ℕ)) (f : MvPowerSeries ι k)
    (hcover : ∀ d, MvPowerSeries.coeff d f ≠ 0 → ∃ e ∈ S, e ≤ d) :
    f ∈ Ideal.span ((fun e => (MvPowerSeries.monomial e 1 : MvPowerSeries ι k)) '' S) := by
  classical
  obtain ⟨T, hTS, hT⟩ := finite_dominated_generators S
  have hf : f ∈ Ideal.span ((fun e => (MvPowerSeries.monomial e 1 : MvPowerSeries ι k)) ''
      (T : Set (ι →₀ ℕ))) := by
    apply series_mem_span_finite_monomials
    intro d hd
    obtain ⟨e, he, hed⟩ := hcover d hd
    obtain ⟨a, ha, hae⟩ := hT e he
    exact ⟨a, ha, hae.trans hed⟩
  exact Ideal.span_mono (Set.image_mono hTS) hf

end MonomialIdeals

section IsolatedJet
variable {ι k : Type*} [Fintype ι] [Field k]

/-- The ideal generated by boundary monomials of weight strictly above `L`. -/
noncomputable def boundaryWeightIdeal (B : Finset ι) (w : ι → ℝ) (L : ℝ) :
    Ideal (MvPowerSeries ι k) :=
  Ideal.span ((fun d => (MvPowerSeries.monomial d 1 : MvPowerSeries ι k)) ''
    {d | (∀ i ∉ B, d i = 0) ∧ L < realWeight w d})

theorem strict_support_mem_boundaryWeightIdeal
    (B : Finset ι) (w : ι → ℝ) (L : ℝ) (hwzero : ∀ i ∉ B, w i = 0)
    (q : MvPowerSeries ι k)
    (hq : ∀ d, MvPowerSeries.coeff d q ≠ 0 → L < realWeight w d) :
    q ∈ boundaryWeightIdeal B w L := by
  classical
  apply series_mem_span_monomials
  intro d hd
  let e := d.filter (fun i => i ∈ B)
  have hew : realWeight w e = realWeight w d := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ B
    · simp [e, hi]
    · simp [e, hi, hwzero i hi]
  refine ⟨e, ⟨?_, by simpa [hew] using hq d hd⟩, ?_⟩
  · intro i hi; simp [e, hi]
  · intro i
    by_cases hi : i ∈ B <;> simp [e, hi]

/-- An algebraic power series admits an isolated jet modulo the boundary weight ideal,
with a uniform linear bound on differential order. -/
theorem algebraic_series_isolated_jet [CharZero k]
    {f : MvPowerSeries ι k} (hf : f ≠ 0)
    (s : Finset ℕ) (p : ℕ → MvPolynomial ι k) (N : ℕ)
    (hdeg : ∀ j ∈ s, (p j).totalDegree ≤ N)
    (hnonzero : ∃ j ∈ s, p j ≠ 0)
    (hrelation : ∑ j ∈ s, (p j : MvPowerSeries ι k) * f ^ j = 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (B : Finset ι)
    (hB : ∀ i ∈ B, 0 < w i) (hwzero : ∀ i ∉ B, w i = 0) :
    ∃ (γ α β : ι →₀ ℕ) (u q : MvPowerSeries ι k),
      IsInitialExponent w f γ ∧ exponentDegree γ ≤ N ∧
      α + β = γ ∧ (∀ i ∉ B, α i = 0) ∧ (∀ i ∈ B, β i = 0) ∧
      realWeight w α = realWeight w γ ∧
      (eulerFactors B N α).length + β.toMultiset.toList.length ≤ (B.card + 1) * (N+1) ∧
      IsUnit u ∧
      iterPartial β.toMultiset.toList (iterEuler (eulerFactors B N α) f) =
        MvPowerSeries.monomial α 1 * u + q ∧
      q ∈ boundaryWeightIdeal B w (realWeight w γ) := by
  classical
  obtain ⟨γ, hγ, hγdeg⟩ := exists_bounded_initial_exponent hf s p N hdeg hnonzero hrelation w hw
  have hbound : ∀ d, IsInitialExponent w f d → partialDegree B d ≤ N := by
    intro d hd
    exact algebraic_initial_partial_degree_le hf s p N hdeg hnonzero hrelation w hw B hB hd
  obtain ⟨α, β, hab, hα, hβ, hc, hiso⟩ :=
    euler_isolates_coefficients B N w hwzero hγ hbound
  let g := iterPartial β.toMultiset.toList (iterEuler (eulerFactors B N α) f)
  have hc' : MvPowerSeries.coeff α g ≠ 0 := hc
  obtain ⟨u, q, hu, heq, hq⟩ := isolated_series_unit_remainder B w α hα g hc'
    (fun d hd => (hiso d hd).1) (fun d hd => (hiso d hd).2)
  have hwβ : realWeight w β = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ B
    · simp [hβ i hi]
    · simp [hwzero i hi]
  have hwα : realWeight w α = realWeight w γ := by
    rw [← hab, realWeight_add, hwβ, add_zero]
  have hβdeg : exponentDegree β ≤ N := by
    have hh := hγdeg
    rw [← hab, exponentDegree_add] at hh
    omega
  refine ⟨γ, α, β, u, q, hγ, hγdeg, hab, hα, hβ, hwα, ?_, hu, heq, ?_⟩
  · have hlen := eulerFactors_length_le B N α
    rw [length_exponent_toList]
    calc
      (eulerFactors B N α).length + exponentDegree β ≤ B.card * (N+1) + N :=
        Nat.add_le_add hlen hβdeg
      _ ≤ (B.card + 1) * (N+1) := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left (Nat.le_succ N) _
  · apply strict_support_mem_boundaryWeightIdeal B w _ hwzero q
    intro d hd
    simpa [hwα] using hq d hd

end IsolatedJet

end CartierSections

end OAI
