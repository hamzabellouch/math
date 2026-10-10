import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Model
import OAI.Combinatorics.KMedian.Instance

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian
namespace Complexity

def ManyOneReduces (L M : Language) : Prop :=
  ∃ f : Word → Word, FinitePolyTime id id f ∧ ∀ x, x ∈ L ↔ f x ∈ M

end Complexity

end MetricKMedian

namespace MetricKMedian.Coverage
open Finset

structure Input where
  m : ℕ
  n : ℕ
  incident : Fin m → Fin n → Bool
  k : ℕ
  m_pos : 0 < m
  k_pos : 1 ≤ k
  k_le : k ≤ n

namespace Input

def encode (C : Input) : List Bool :=
  encodeNat C.m ++ encodeNat C.n ++ encodeNat C.k ++
    (List.ofFn (fun j : Fin C.m => List.ofFn (C.incident j))).flatten

def covered (C : Input) (S : Finset (Fin C.n)) : Finset (Fin C.m) :=
  univ.filter (fun j => ∃ i ∈ S, C.incident j i = true)

def Perfect (C : Input) : Prop :=
  ∃ S : Finset (Fin C.n), S.card ≤ C.k ∧ C.covered S = univ

def Sound (C : Input) (δ : ℝ) : Prop :=
  ∀ S : Finset (Fin C.n), S.card ≤ C.k →
    ((C.covered S).card : ℝ) ≤ (1 - 1 / Real.exp 1 + δ) * C.m

abbrev Point (C : Input) := Fin C.m ⊕ Fin C.n

def pointDistance (C : Input) : C.Point → C.Point → ℚ
  | .inl i, .inl j => if i = j then 0 else 2
  | .inr i, .inr j => if i = j then 0 else 2
  | .inl j, .inr i => if C.incident j i then 1 else 3
  | .inr i, .inl j => if C.incident j i then 1 else 3

theorem pointDistance_nonneg (C : Input) (x y : C.Point) :
    0 ≤ C.pointDistance x y := by
  cases x <;> cases y <;> simp only [pointDistance] <;> split <;> norm_num

theorem pointDistance_eq_zero (C : Input) (x y : C.Point) :
    C.pointDistance x y = 0 ↔ x = y := by
  cases x <;> cases y <;> simp only [pointDistance] <;> split <;> simp_all

theorem pointDistance_symm (C : Input) (x y : C.Point) :
    C.pointDistance x y = C.pointDistance y x := by
  cases x <;> cases y <;> simp only [pointDistance] <;> split_ifs <;> simp_all

theorem pointDistance_triangle (C : Input) (x y z : C.Point) :
    C.pointDistance x z ≤ C.pointDistance x y + C.pointDistance y z := by
  cases x <;> cases y <;> cases z <;>
    simp only [pointDistance] <;> split_ifs <;> subst_vars <;> (try simp_all) <;> norm_num

def client (C : Input) (j : Fin C.m) : Fin (C.m + C.n) :=
  finSumFinEquiv (Sum.inl j)

def facility (C : Input) (i : Fin C.n) : Fin (C.m + C.n) :=
  finSumFinEquiv (Sum.inr i)

theorem client_injective (C : Input) : Function.Injective C.client := by
  intro i j h
  exact Sum.inl.inj (finSumFinEquiv.injective h)

theorem facility_injective (C : Input) : Function.Injective C.facility := by
  intro i j h
  exact Sum.inr.inj (finSumFinEquiv.injective h)

theorem client_ne_facility (C : Input) (j : Fin C.m) (i : Fin C.n) :
    C.client j ≠ C.facility i := by
  intro h
  have hh := finSumFinEquiv.injective h
  cases hh

def chosenFacilities (C : Input) (S : Finset (Fin C.n)) : Finset (Fin (C.m + C.n)) :=
  S.image C.facility

@[simp] theorem chosenFacilities_card (C : Input) (S : Finset (Fin C.n)) :
    (C.chosenFacilities S).card = S.card :=
  card_image_of_injective _ C.facility_injective

@[simp] theorem chosenFacilities_nonempty (C : Input) (S : Finset (Fin C.n)) :
    (C.chosenFacilities S).Nonempty ↔ S.Nonempty := image_nonempty

def toMedian (C : Input) : Instance where
  n := C.m + C.n
  distance x y := C.pointDistance (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)
  clients := univ.image C.client
  facilities := C.chosenFacilities univ
  k := C.k
  distance_nonneg x y := C.pointDistance_nonneg _ _
  distance_eq_zero x y := (C.pointDistance_eq_zero _ _).trans finSumFinEquiv.symm.injective.eq_iff
  distance_symm x y := C.pointDistance_symm _ _
  distance_triangle x y z := C.pointDistance_triangle _ _ _
  k_pos := C.k_pos
  k_le := by simpa using C.k_le

@[simp] theorem distance_client_facility (C : Input) (j : Fin C.m) (i : Fin C.n) :
    C.toMedian.distance (C.client j) (C.facility i) =
      if C.incident j i then 1 else 3 := by
  simp [toMedian, client, facility, pointDistance]

theorem chosenFacilities_subset (C : Input) (S : Finset (Fin C.n)) :
    C.chosenFacilities S ⊆ C.toMedian.facilities :=
  image_subset_image (subset_univ S)

@[simp] theorem mem_covered (C : Input) (S : Finset (Fin C.n)) (j : Fin C.m) :
    j ∈ C.covered S ↔ ∃ i ∈ S, C.incident j i = true := by
  simp [covered]

theorem nearest_chosen_ge_one (C : Input) (j : Fin C.m)
    (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    1 ≤ nearest C.toMedian (C.client j) (C.chosenFacilities S) := by
  obtain ⟨x, hx, he⟩ := C.toMedian.nearest_attained (C.client j)
    (C.chosenFacilities S) ((C.chosenFacilities_nonempty S).mpr hS)
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  rw [he, C.distance_client_facility]
  split <;> norm_num

theorem nearest_chosen (C : Input) (j : Fin C.m)
    (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    nearest C.toMedian (C.client j) (C.chosenFacilities S) =
      if j ∈ C.covered S then 1 else 3 := by
  split_ifs with hj
  · obtain ⟨i, hi, hji⟩ := (C.mem_covered S j).mp hj
    apply le_antisymm _ (C.nearest_chosen_ge_one j S hS)
    have h := C.toMedian.nearest_le (C.client j) (mem_image_of_mem C.facility hi)
    simpa only [chosenFacilities, C.distance_client_facility, hji, Bool.true_eq, ↓reduceIte,
      Rat.cast_one] using h
  · obtain ⟨x, hx, he⟩ := C.toMedian.nearest_attained (C.client j)
      (C.chosenFacilities S) ((C.chosenFacilities_nonempty S).mpr hS)
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hji : C.incident j i ≠ true := fun h => hj ((C.mem_covered S j).mpr ⟨i, hi, h⟩)
    rw [he, C.distance_client_facility]
    simp [hji]

theorem cost_chosen (C : Input) (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    cost C.toMedian (C.chosenFacilities S) =
      3 * (C.m : ℝ) - 2 * ((C.covered S).card : ℝ) := by
  unfold cost
  change (∑ j ∈ univ.image C.client,
    nearest C.toMedian j (C.chosenFacilities S)) = _
  rw [sum_image]
  · simp_rw [C.nearest_chosen _ S hS]
    calc
      ∑ j : Fin C.m, (if j ∈ C.covered S then (1 : ℝ) else 3) =
          ∑ j : Fin C.m, (3 - 2 * (if j ∈ C.covered S then (1 : ℝ) else 0)) := by
        apply sum_congr rfl
        intro j _
        split_ifs <;> norm_num
      _ = _ := by
        rw [sum_sub_distrib, ← mul_sum]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          sum_boole, filter_mem_eq_inter, univ_inter]
        ring
  · intro i _ j _ hij
    exact C.client_injective hij

def selected (C : Input) (T : Finset (Fin (C.m + C.n))) : Finset (Fin C.n) :=
  univ.filter (fun i => C.facility i ∈ T)

theorem chosen_selected (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) : C.chosenFacilities (C.selected T) = T := by
  ext x
  simp only [chosenFacilities, selected, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    obtain ⟨i, _, hi⟩ := mem_image.mp (hT hx)
    exact ⟨i, hi ▸ hx, hi⟩

@[simp] theorem selected_chosen (C : Input) (S : Finset (Fin C.n)) :
    C.selected (C.chosenFacilities S) = S := by
  ext i
  simp only [selected, chosenFacilities, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨j, hj, hij⟩
    exact C.facility_injective hij ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem cost_selected (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty) :
    cost C.toMedian T = 3 * (C.m : ℝ) - 2 * ((C.covered (C.selected T)).card : ℝ) := by
  have he := C.chosen_selected hT
  have hs : (C.selected T).Nonempty := (C.chosenFacilities_nonempty _).mp (he.symm ▸ hne)
  simpa only [he] using C.cost_chosen (C.selected T) hs

theorem covered_card_le (C : Input) (S : Finset (Fin C.n)) :
    (C.covered S).card ≤ C.m := by
  simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ (C.covered S))

theorem cost_ge_universe (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty) :
    (C.m : ℝ) ≤ cost C.toMedian T := by
  rw [C.cost_selected hT hne]
  have h : ((C.covered (C.selected T)).card : ℝ) ≤ C.m := by
    exact_mod_cast C.covered_card_le (C.selected T)
  linarith

theorem perfect_nonempty (C : Input) {S : Finset (Fin C.n)}
    (h : C.covered S = univ) : S.Nonempty := by
  let j : Fin C.m := ⟨0, C.m_pos⟩
  have hj : j ∈ C.covered S := by rw [h]; exact mem_univ j
  obtain ⟨i, hi, _⟩ := (C.mem_covered S j).mp hj
  exact ⟨i, hi⟩

theorem optimum_of_perfect (C : Input) (h : C.Perfect) :
    optimum C.toMedian = C.m := by
  apply le_antisymm
  · obtain ⟨S, hk, hcover⟩ := h
    have hne := C.perfect_nonempty hcover
    have hb := C.toMedian.optimum_le (C.chosenFacilities_subset S)
      ((C.chosenFacilities_nonempty _).mpr hne) (by
        change (C.chosenFacilities S).card ≤ C.k
        simpa only [chosenFacilities_card] using hk)
    rw [C.cost_chosen S hne, hcover] at hb
    simp only [card_univ, Fintype.card_fin] at hb
    linarith
  · obtain ⟨T, hT, hne, _, he⟩ := C.toMedian.optimum_attained
    rw [← he]
    exact C.cost_ge_universe hT hne

theorem cost_of_sound (C : Input) (δ : ℝ) (h : C.Sound δ)
    {T : Finset (Fin (C.m + C.n))} (hT : T ⊆ C.toMedian.facilities)
    (hne : T.Nonempty) (hk : T.card ≤ C.k) :
    (1 + 2 / Real.exp 1 - 2 * δ) * C.m ≤ cost C.toMedian T := by
  have he := C.chosen_selected hT
  have hs : (C.selected T).card ≤ C.k := by
    rw [← C.chosenFacilities_card, he]
    exact hk
  have hc := h (C.selected T) hs
  rw [C.cost_selected hT hne]
  simp only [div_eq_mul_inv, one_mul] at hc ⊢
  nlinarith

end Input

def GapNPReductions : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ L ∈ Complexity.NP,
    ∃ reduce : Complexity.Word → Input,
      Complexity.FinitePolyTime id Input.encode reduce ∧
      (∀ x, x ∈ L → (reduce x).Perfect) ∧
      (∀ x, x ∉ L → (reduce x).Sound δ)

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
