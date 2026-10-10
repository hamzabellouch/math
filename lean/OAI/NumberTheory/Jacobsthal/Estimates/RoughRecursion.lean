import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace ErdosAverageCertificates

def PairwiseCoprime (A : Finset ℕ) : Prop :=
  (A : Set ℕ).Pairwise Nat.Coprime

def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Ico 1 n ∧ PairwiseCoprime A

def shiftedWeightQ (n : ℕ) (A : Finset ℕ) : ℚ :=
  ∑ a ∈ A, 1 / ((n - a : ℕ) : ℚ)

noncomputable def admissibleSets (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Ico 1 n).powerset.filter (Admissible n)

@[simp]
theorem mem_admissibleSets {n : ℕ} {A : Finset ℕ} :
    A ∈ admissibleSets n ↔ Admissible n A := by
  simp [admissibleSets, Admissible]

@[simp]
theorem empty_admissible (n : ℕ) : Admissible n ∅ := by
  simp [Admissible, PairwiseCoprime]

theorem admissibleSets_nonempty (n : ℕ) : (admissibleSets n).Nonempty :=
  ⟨∅, by simp⟩

noncomputable def attainableWeights (n : ℕ) : Finset ℚ := by
  classical
  exact (admissibleSets n).image (shiftedWeightQ n)

theorem attainableWeights_nonempty (n : ℕ) : (attainableWeights n).Nonempty := by
  refine ⟨0, ?_⟩
  refine Finset.mem_image.mpr ⟨∅, ?_, ?_⟩
  · exact mem_admissibleSets.mpr (empty_admissible n)
  · simp [shiftedWeightQ]

noncomputable def extremalQ (n : ℕ) : ℚ :=
  (attainableWeights n).max' (attainableWeights_nonempty n)

noncomputable def extremal (n : ℕ) : ℝ :=
  extremalQ n

theorem exists_extremizer (n : ℕ) :
    ∃ A : Finset ℕ, Admissible n A ∧ shiftedWeightQ n A = extremalQ n := by
  have hmax : extremalQ n ∈ attainableWeights n := by
    exact Finset.max'_mem _ _
  obtain ⟨A, hA, hw⟩ := Finset.mem_image.mp hmax
  exact ⟨A, mem_admissibleSets.mp hA, hw⟩

theorem shiftedWeightQ_le_extremalQ {n : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) : shiftedWeightQ n A ≤ extremalQ n := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨A, mem_admissibleSets.mpr hA, rfl⟩

def IsRough (m y : ℕ) : Prop :=
  m = 1 ∨ ∀ p : ℕ, p.Prime → p ∣ m → y < p

@[simp]
theorem one_isRough (y : ℕ) : IsRough 1 y :=
  Or.inl rfl

theorem isRough_of_minFac_lt {m y : ℕ} (h : y < m.minFac) :
    IsRough m y := by
  right
  intro p hp hpm
  exact h.trans_le (Nat.minFac_le_of_dvd hp.two_le hpm)

theorem minFac_lt_of_isRough {m y : ℕ} (hm : m ≠ 1) (h : IsRough m y) :
    y < m.minFac := by
  rcases h with h_one | h_divisors
  · exact (hm h_one).elim
  exact h_divisors m.minFac (Nat.minFac_prime hm) (Nat.minFac_dvd m)

theorem isRough_iff_minFac {m y : ℕ} (hm : m ≠ 1) :
    IsRough m y ↔ y < m.minFac :=
  ⟨minFac_lt_of_isRough hm, isRough_of_minFac_lt⟩

noncomputable def roughCount (x y : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter fun m ↦ IsRough m y).card

noncomputable def selfRoughSet (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 n).filter fun a ↦ IsRough a (n - a)

noncomputable def selfRoughSumQ (n : ℕ) : ℚ :=
  shiftedWeightQ n (selfRoughSet n)

end ErdosAverageCertificates

end

section

open scoped BigOperators

namespace ErdosAverageCertificates

noncomputable section

noncomputable def roughSet (x y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun m ↦ IsRough m y

@[simp]
theorem mem_roughSet {x y m : ℕ} :
    m ∈ roughSet x y ↔ 1 ≤ m ∧ m ≤ x ∧ IsRough m y := by
  classical
  simp [roughSet, and_assoc]

theorem roughCount_eq_card (x y : ℕ) :
    roughCount x y = (roughSet x y).card := by
  rfl

noncomputable def roughLayer (x y z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 x).filter fun m ↦ y < m.minFac ∧ m.minFac ≤ z

@[simp]
theorem mem_roughLayer {x y z m : ℕ} :
    m ∈ roughLayer x y z ↔
      2 ≤ m ∧ m ≤ x ∧ y < m.minFac ∧ m.minFac ≤ z := by
  classical
  simp [roughLayer, and_assoc]

noncomputable def leastPrimeFiber (x p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 x).filter fun m ↦ m.minFac = p

@[simp]
theorem mem_leastPrimeFiber {x p m : ℕ} :
    m ∈ leastPrimeFiber x p ↔ 2 ≤ m ∧ m ≤ x ∧ m.minFac = p := by
  classical
  simp [leastPrimeFiber, and_assoc]

def layerPrimes (y z : ℕ) : Finset ℕ :=
  (Finset.Ioc y z).filter Nat.Prime

@[simp]
theorem mem_layerPrimes {y z p : ℕ} :
    p ∈ layerPrimes y z ↔ y < p ∧ p ≤ z ∧ p.Prime := by
  simp [layerPrimes, and_assoc]

theorem minFac_mul_eq_left_of_prime_of_rough {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) (hrough : IsRough k (p - 1)) :
    (p * k).minFac = p := by
  have hprod : p * k ≠ 1 := by
    have hpk : 2 * 1 ≤ p * k := Nat.mul_le_mul hp.two_le hk
    have : 2 ≤ p * k := by simpa using hpk
    omega
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p k)
  · have hqprime : (p * k).minFac.Prime := Nat.minFac_prime hprod
    have hqdiv : (p * k).minFac ∣ p * k := Nat.minFac_dvd (p * k)
    rcases hqprime.dvd_mul.mp hqdiv with hqp | hqk
    · exact le_of_eq (Nat.prime_dvd_prime_iff_eq hqprime hp |>.mp hqp).symm
    · rcases hrough with hk_one | hk_divisors
      · subst k
        simpa using (le_of_eq hp.minFac_eq.symm)
      · have := hk_divisors (p * k).minFac hqprime hqk
        omega

theorem rough_of_minFac_eq_prime {m p : ℕ}
    (_hm : 2 ≤ m) (_hp : p.Prime) (hmin : m.minFac = p) :
    IsRough (m / p) (p - 1) := by
  right
  intro q hq hqdiv
  have hpdiv : p ∣ m := by simpa [hmin] using Nat.minFac_dvd m
  have hrecover : p * (m / p) = m := Nat.mul_div_cancel' hpdiv
  have hqdivm : q ∣ m := by
    rw [← hrecover]
    exact dvd_mul_of_dvd_right hqdiv p
  have hle : p ≤ q := by
    rw [← hmin]
    exact Nat.minFac_le_of_dvd hq.two_le hqdivm
  have hq2 : 2 ≤ q := hq.two_le
  omega

theorem card_leastPrimeFiber_eq_roughCount {x p : ℕ} (hp : p.Prime) :
    (leastPrimeFiber x p).card = roughCount (x / p) (p - 1) := by
  rw [roughCount_eq_card]
  symm
  apply Finset.card_bij (fun k _ ↦ p * k)
  · intro k hk
    rw [mem_leastPrimeFiber]
    have hk' := mem_roughSet.mp hk
    refine ⟨?_, ?_, minFac_mul_eq_left_of_prime_of_rough hp hk'.1 hk'.2.2⟩
    · have hpk : 2 * 1 ≤ p * k := Nat.mul_le_mul hp.two_le hk'.1
      simpa using hpk
    · have hmul : k * p ≤ x :=
        (Nat.le_div_iff_mul_le hp.pos).mp hk'.2.1
      simpa [mul_comm] using hmul
  · intro k₁ hk₁ k₂ hk₂ hmul
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmul
  · intro m hm
    have hm' := mem_leastPrimeFiber.mp hm
    have hpdiv : p ∣ m := by
      simpa [hm'.2.2] using Nat.minFac_dvd m
    refine ⟨m / p, ?_, ?_⟩
    · rw [mem_roughSet]
      refine ⟨?_, Nat.div_le_div_right hm'.2.1,
        rough_of_minFac_eq_prime hm'.1 hp hm'.2.2⟩
      exact Nat.div_pos (by
        rw [← hm'.2.2]
        exact Nat.minFac_le (by omega)) hp.pos
    · exact Nat.mul_div_cancel' hpdiv

theorem roughSet_eq_union_layer {x y z : ℕ} (hyz : y ≤ z) :
    roughSet x y = roughSet x z ∪ roughLayer x y z := by
  classical
  ext m
  by_cases hm1 : m = 1
  · subst m
    simp
  have hmrough_y : IsRough m y ↔ y < m.minFac := isRough_iff_minFac hm1
  have hmrough_z : IsRough m z ↔ z < m.minFac := isRough_iff_minFac hm1
  by_cases hmx : 1 ≤ m ∧ m ≤ x
  · have hm2 : 2 ≤ m := by omega
    simp only [mem_roughSet, Finset.mem_union, mem_roughLayer, hmrough_y,
      hmrough_z, hmx.1, hmx.2, hm2, true_and]
    omega
  · simp only [mem_roughSet, Finset.mem_union, mem_roughLayer, hmrough_y,
      hmrough_z]
    omega

theorem roughSet_disjoint_layer (x y z : ℕ) :
    Disjoint (roughSet x z) (roughLayer x y z) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmrough hmlayer
  have hm1 : m ≠ 1 := by
    have := (mem_roughLayer.mp hmlayer).1
    omega
  have hzlt : z < m.minFac :=
    (isRough_iff_minFac hm1).mp (mem_roughSet.mp hmrough).2.2
  exact (not_lt_of_ge (mem_roughLayer.mp hmlayer).2.2.2) hzlt

theorem roughCount_eq_add_layer {x y z : ℕ} (hyz : y ≤ z) :
    roughCount x y = roughCount x z + (roughLayer x y z).card := by
  simp only [roughCount_eq_card, roughSet_eq_union_layer hyz,
    Finset.card_union_of_disjoint (roughSet_disjoint_layer x y z)]

theorem roughLayer_mapsTo_layerPrimes {x y z : ℕ} :
    (roughLayer x y z : Set ℕ).MapsTo Nat.minFac (layerPrimes y z) := by
  intro m hm
  have hm' := mem_roughLayer.mp hm
  exact mem_layerPrimes.mpr
    ⟨hm'.2.2.1, hm'.2.2.2, Nat.minFac_prime (by omega)⟩

theorem roughLayer_fiber_eq {x y z p : ℕ} (hp : p ∈ layerPrimes y z) :
    {m ∈ roughLayer x y z | m.minFac = p} = leastPrimeFiber x p := by
  classical
  ext m
  have hp' := mem_layerPrimes.mp hp
  simp only [Finset.mem_filter, mem_roughLayer, mem_leastPrimeFiber]
  constructor
  · rintro ⟨⟨hm2, hmx, -, -⟩, hmin⟩
    exact ⟨hm2, hmx, hmin⟩
  · rintro ⟨hm2, hmx, hmin⟩
    exact ⟨⟨hm2, hmx, hmin ▸ hp'.1, hmin ▸ hp'.2.1⟩, hmin⟩

theorem card_roughLayer_eq_sum_roughCount (x y z : ℕ) :
    (roughLayer x y z).card =
      ∑ p ∈ layerPrimes y z, roughCount (x / p) (p - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise roughLayer_mapsTo_layerPrimes]
  apply Finset.sum_congr rfl
  intro p hp
  rw [roughLayer_fiber_eq hp, card_leastPrimeFiber_eq_roughCount
    (mem_layerPrimes.mp hp).2.2]

theorem roughCount_buchstab_recursion {x y z : ℕ} (hyz : y ≤ z) :
    roughCount x y = roughCount x z +
      ∑ p ∈ layerPrimes y z, roughCount (x / p) (p - 1) := by
  rw [roughCount_eq_add_layer hyz, card_roughLayer_eq_sum_roughCount]

end

end ErdosAverageCertificates

end

end Erdos970

end OAI
