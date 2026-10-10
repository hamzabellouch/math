import OAI.AlgebraicGeometry.CartierSections.InitialExponents
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.MvPowerSeries.Derivative

namespace OAI

/-!
# Euler operators on formal power series

Euler operators act diagonally on coefficients, and iterated transverse derivatives shift
the coefficient exponent. These formulas yield finite operators that isolate bounded exponents.
-/

open scoped BigOperators

namespace CartierSections

section EulerOperators
variable {ι k : Type*} [Field k] [CharZero k]

/-- The Euler differential operator minus a scalar. -/
noncomputable def eulerStep (i : ι) (l : ℕ) (f : MvPowerSeries ι k) :
    MvPowerSeries ι k :=
  MvPowerSeries.X i * MvPowerSeries.pderiv (R := k) i f - (l : k) • f

@[simp] theorem coeff_eulerStep (i : ι) (l : ℕ) (f : MvPowerSeries ι k)
    (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (eulerStep i l f) =
      ((d i : k) - l) * MvPowerSeries.coeff d f := by
  classical
  have hX : (MvPowerSeries.X i : MvPowerSeries ι k) =
      MvPowerSeries.monomial (Finsupp.single i 1) 1 := rfl
  simp only [eulerStep, map_sub, map_smul, smul_eq_mul, hX,
    MvPowerSeries.coeff_monomial_mul]
  by_cases hi : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hi, one_mul, MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hi]
    have hd : 1 ≤ d i := by simpa using hi i
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    rw [Nat.cast_sub hd]
    ring
  · have hd : d i = 0 := by
      by_contra h
      apply hi
      intro j
      by_cases hj : j = i
      · subst j; simpa using Nat.one_le_iff_ne_zero.mpr h
      · simp [Finsupp.single_eq_of_ne hj]
    simp [hd]

noncomputable def iterEuler : List (ι × ℕ) → MvPowerSeries ι k → MvPowerSeries ι k
  | [] => id
  | (i,l) :: L => fun f => eulerStep i l (iterEuler L f)

@[simp] theorem coeff_iterEuler (L : List (ι × ℕ)) (f : MvPowerSeries ι k)
    (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (iterEuler L f) =
      (L.map (fun a => ((d a.1 : k) - a.2))).prod * MvPowerSeries.coeff d f := by
  induction L with
  | nil => simp [iterEuler]
  | cons a L ih =>
    simp only [iterEuler, coeff_eulerStep, List.map_cons, List.prod_cons, ih, mul_assoc]

/-- Euler factors selecting one boundary exponent among those bounded by `N`. -/
noncomputable def eulerFactors (B : Finset ι) (N : ℕ) (α : ι →₀ ℕ) :
    List (ι × ℕ) := by
  classical
  exact ((B ×ˢ Finset.range (N+1)).filter (fun a => a.2 ≠ α a.1)).toList

@[simp] theorem mem_eulerFactors (B : Finset ι) (N : ℕ) (α : ι →₀ ℕ)
    (i : ι) (l : ℕ) :
    (i,l) ∈ eulerFactors B N α ↔ i ∈ B ∧ l ≤ N ∧ l ≠ α i := by
  classical
  simp [eulerFactors, and_assoc]

/-- The chosen coefficient survives over a field of characteristic zero. -/
theorem coeff_eulerFactors_self_ne_zero (B : Finset ι) (N : ℕ)
    (α γ : ι →₀ ℕ) (hαγ : ∀ i ∈ B, γ i = α i)
    {f : MvPowerSeries ι k} (hf : MvPowerSeries.coeff γ f ≠ 0) :
    MvPowerSeries.coeff γ (iterEuler (eulerFactors B N α) f) ≠ 0 := by
  classical
  rw [coeff_iterEuler]
  apply mul_ne_zero _ hf
  apply List.prod_ne_zero
  intro hc
  obtain ⟨⟨i,l⟩, hil, hz⟩ := List.mem_map.mp hc
  have h := (mem_eulerFactors B N α i l).mp hil
  have hne : (γ i : k) - l ≠ 0 := sub_ne_zero.mpr (by
    rw [hαγ i h.1]
    exact_mod_cast h.2.2.symm)
  exact hne hz

/-- Every other bounded exponent in the boundary coordinates is killed. -/
theorem coeff_eulerFactors_eq_zero (B : Finset ι) (N : ℕ)
    (α d : ι →₀ ℕ) (hd : ∃ i ∈ B, d i ≤ N ∧ d i ≠ α i)
    (f : MvPowerSeries ι k) :
    MvPowerSeries.coeff d (iterEuler (eulerFactors B N α) f) = 0 := by
  classical
  rw [coeff_iterEuler]
  obtain ⟨i, hi, hdi, hne⟩ := hd
  have hm : (0 : k) ∈ (eulerFactors B N α).map (fun a => (d a.1 : k) - a.2) := by
    apply List.mem_map.mpr
    exact ⟨(i,d i), (mem_eulerFactors B N α i (d i)).mpr ⟨hi,hdi,hne⟩, sub_self _⟩
  rw [List.prod_eq_zero_iff.mpr hm, zero_mul]

/-- The number of Euler factors is at most s(N+1), uniformly in the weights. -/
theorem eulerFactors_length_le (B : Finset ι) (N : ℕ) (α : ι →₀ ℕ) :
    (eulerFactors B N α).length ≤ B.card * (N+1) := by
  classical
  simpa [eulerFactors] using
    (Finset.card_filter_le (B ×ˢ Finset.range (N+1)) (fun a => a.2 ≠ α a.1))

noncomputable def iterPartial : List ι → MvPowerSeries ι k → MvPowerSeries ι k
  | [] => id
  | i :: L => fun f => MvPowerSeries.pderiv (R := k) i (iterPartial L f)

noncomputable def listExponent (L : List ι) : ι →₀ ℕ := by
  classical
  exact (L : Multiset ι).toFinsupp

@[simp] theorem listExponent_nil : listExponent ([] : List ι) = 0 := by
  classical
  simp [listExponent]
@[simp] theorem listExponent_cons (i : ι) (L : List ι) :
    listExponent (i :: L) = Finsupp.single i 1 + listExponent L := by
  classical
  ext j
  by_cases h : j = i
  · subst j; simp [listExponent, add_comm]
  · simp [listExponent, h, Ne.symm h]

/-- Iterated transverse derivatives shift coefficients by their multidegree; the factorial coefficient is nonzero in characteristic zero. -/
theorem coeff_iterPartial_ne_zero_iff (L : List ι) (f : MvPowerSeries ι k)
    (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (iterPartial L f) ≠ 0 ↔
      MvPowerSeries.coeff (d + listExponent L) f ≠ 0 := by
  induction L generalizing d with
  | nil => simp [iterPartial]
  | cons i L ih =>
    rw [iterPartial, MvPowerSeries.coeff_pderiv, mul_ne_zero_iff, ih]
    have hn : (d i : k) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (d i)
    simp [listExponent_cons, hn, add_assoc]

@[simp] theorem listExponent_toList (β : ι →₀ ℕ) :
    listExponent β.toMultiset.toList = β := by
  classical
  simp [listExponent]

@[simp] theorem length_exponent_toList [Fintype ι] (β : ι →₀ ℕ) :
    β.toMultiset.toList.length = exponentDegree β := by
  simp [exponentDegree, Finsupp.card_toMultiset, Finsupp.sum_fintype]

end EulerOperators

end CartierSections

end OAI
