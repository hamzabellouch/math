import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.SliceMoments

variable {V : Type*} [sectionDecidableEqV : DecidableEq V]

def average (U : Finset V) (q : ℕ) (f : Finset V → ℝ) : ℝ :=
  (∑ S ∈ U.powersetCard q, f S) / (U.card.choose q : ℝ)

def coord (i : V) (S : Finset V) : ℝ := if i ∈ S then 1 else 0

theorem average_containment (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) (hCq : C.card ≤ q) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  have hdenC : (U.card.choose C.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hCq.trans hq)).ne'
  have hmul := Nat.choose_mul (n := U.card) hCq
  have hmulR : (U.card.choose q : ℝ) * (q.choose C.card : ℝ) =
      (U.card.choose C.card : ℝ) * ((U.card - C.card).choose (q - C.card) : ℝ) := by
    exact_mod_cast hmul
  unfold average
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_filter_powersetCard_subset C U q hCU hCq]
  apply (div_eq_div_iff hden hdenC).mpr
  nlinarith

theorem average_containment_all (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  by_cases hCq : C.card ≤ q
  · exact average_containment U C q hCU hq hCq
  · have hlt : q < C.card := by omega
    have hempty : (U.powersetCard q).filter (C ⊆ ·) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro S hS hCS
      have hcard := Finset.card_le_card hCS
      have hScard := (Finset.mem_powersetCard.mp hS).2
      omega
    unfold average
    rw [← Finset.sum_filter, hempty]
    simp [Nat.choose_eq_zero_of_lt hlt]

theorem average_coord (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i : V) (hi : i ∈ U) :
    average U q (coord i) = (q : ℝ) / U.card := by
  change average U q (fun S => if i ∈ S then 1 else 0) = _
  simpa using average_containment_all U {i} q
    (Finset.singleton_subset_iff.mpr hi) hq

theorem average_coord_mul (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (fun S => coord i S * coord j S) =
      (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
  have hpair : ({i, j} : Finset V).card = 2 := by simp [hne]
  have hCU : ({i, j} : Finset V) ⊆ U := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
  have hfun : (fun S => coord i S * coord j S) =
      (fun S : Finset V => if ({i, j} : Finset V) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S <;> simp [coord, Finset.insert_subset_iff, Finset.singleton_subset_iff, hiS, hjS]
  rw [hfun, average_containment_all U {i, j} q hCU hq, hpair,
    Nat.cast_choose_two, Nat.cast_choose_two]
  exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _

@[simp] theorem coord_sq (i : V) (S : Finset V) : (coord i S)^2 = coord i S := by
  by_cases hi : i ∈ S <;> simp [coord, hi]

include sectionDecidableEqV in
@[simp] theorem average_add (U : Finset V) (q : ℕ) (f g : Finset V → ℝ) :
    average U q (fun S => f S + g S) = average U q f + average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.sum_add_distrib, add_div]

include sectionDecidableEqV in
@[simp] theorem average_mul_left (U : Finset V) (q : ℕ) (c : ℝ) (f : Finset V → ℝ) :
    average U q (fun S => c * f S) = c * average U q f := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, ← Finset.mul_sum, mul_div_assoc]

include sectionDecidableEqV in
theorem average_sum {I : Type*} (U : Finset V) (q : ℕ) (s : Finset I)
    (f : I → Finset V → ℝ) :
    average U q (fun S => ∑ i ∈ s, f i S) = ∑ i ∈ s, average U q (f i) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem average_linear (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (u : V → ℝ) :
    average U q (fun S => ∑ i ∈ U, u i * coord i S) =
      ((q : ℝ) / U.card) * ∑ i ∈ U, u i := by
  rw [average_sum]
  simp only [average_mul_left]
  calc
    (∑ i ∈ U, u i * average U q (coord i)) =
        ∑ i ∈ U, u i * ((q : ℝ) / U.card) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [average_coord U q hq i hi]
    _ = ((q : ℝ) / U.card) * ∑ i ∈ U, u i := by
      rw [← Finset.sum_mul]
      ring

theorem average_linear_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (u : V → ℝ) :
    average U q (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      ((q : ℝ) / U.card -
        (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1))) *
        (∑ i ∈ U, (u i)^2) +
      ((q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1))) *
        (∑ i ∈ U, u i)^2 := by
  let p₁ : ℝ := (q : ℝ) / U.card
  let p₂ : ℝ := (q : ℝ) * ((q : ℝ) - 1) /
    ((U.card : ℝ) * ((U.card : ℝ) - 1))
  have hm : ∀ i ∈ U, ∀ j ∈ U,
      average U q (fun S => coord i S * coord j S) = if i = j then p₁ else p₂ := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      simpa only [↓reduceIte, ← pow_two, coord_sq] using average_coord U q hq i hi
    · simpa only [ite_eq_right hij] using average_coord_mul U q hq i j hi hj hij
  have hfun : (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      (fun S => ∑ i ∈ U, ∑ j ∈ U, (u i * u j) * (coord i S * coord j S)) := by
    funext S
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun, average_sum]
  simp only [average_sum, average_mul_left]
  have hrearrange : (∑ i ∈ U, ∑ j ∈ U,
      (u i * u j) * average U q (fun S => coord i S * coord j S)) =
      ∑ i ∈ U, ∑ j ∈ U,
        (p₂ * (u i * u j) + if i = j then (p₁ - p₂) * (u i)^2 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm i hi j hj]
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte]
      ring
    · simp only [ite_eq_right hij, add_zero]
      ring
  rw [hrearrange]
  have hconstant : (∑ i ∈ U, ∑ j ∈ U, p₂ * (u i * u j)) =
      p₂ * (∑ i ∈ U, u i)^2 := by
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  have hdiag : (∑ i ∈ U, ∑ j ∈ U,
      if i = j then (p₁ - p₂) * (u i)^2 else 0) =
      (p₁ - p₂) * ∑ i ∈ U, (u i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  simp only [Finset.sum_add_distrib]
  rw [hconstant, hdiag]
  change p₂ * (∑ i ∈ U, u i)^2 + (p₁ - p₂) * (∑ i ∈ U, (u i)^2) =
    (p₁ - p₂) * (∑ i ∈ U, (u i)^2) + p₂ * (∑ i ∈ U, u i)^2
  ring

theorem average_linear_zero_sum (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (u : V → ℝ) (hu : ∑ i ∈ U, u i = 0) :
    average U q (fun S => ∑ i ∈ U, u i * coord i S) = 0 := by
  rw [average_linear U q hq u, hu, mul_zero]

theorem average_linear_sq_zero_sum (U : Finset V) (q : ℕ)
    (hN : 2 ≤ U.card) (hq : q ≤ U.card) (u : V → ℝ)
    (hu : ∑ i ∈ U, u i = 0) :
    average U q (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      ((q : ℝ) * ((U.card : ℝ) - q) /
        ((U.card : ℝ) * ((U.card : ℝ) - 1))) * (∑ i ∈ U, (u i)^2) := by
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hcoeff : (q : ℝ) / U.card -
      (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) =
      (q : ℝ) * ((U.card : ℝ) - q) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
    field_simp
    ; ring
  rw [average_linear_sq U q hq u, hu, hcoeff]
  simp

include sectionDecidableEqV in
theorem average_congr (U : Finset V) (q : ℕ) (f g : Finset V → ℝ)
    (h : ∀ S ∈ U.powersetCard q, f S = g S) : average U q f = average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  unfold average
  congr 1
  exact Finset.sum_congr rfl h

include sectionDecidableEqV in
@[simp] theorem average_const (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (c : ℝ) :
    average U q (fun _ => c) = c := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  simp [average, Finset.card_powersetCard, hden]

include sectionDecidableEqV in
@[simp] theorem average_sub (U : Finset V) (q : ℕ) (f g : Finset V → ℝ) :
    average U q (fun S => f S - g S) = average U q f - average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.sum_sub_distrib, sub_div]

def equalIndicator (i j : V) (S : Finset V) : ℝ :=
  if (i ∈ S ↔ j ∈ S) then 1 else 0

theorem equalIndicator_eq (i j : V) (S : Finset V) :
    equalIndicator i j S = 1 - coord i S - coord j S + 2 * (coord i S * coord j S) := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> norm_num [equalIndicator, coord, hi, hj]

@[simp] theorem equalIndicator_sq (i j : V) (S : Finset V) :
    (equalIndicator i j S)^2 = equalIndicator i j S := by
  unfold equalIndicator
  split_ifs <;> norm_num

def equalMean (U : Finset V) (q : ℕ) : ℝ :=
  ((q : ℝ) * ((q : ℝ) - 1) +
    ((U.card : ℝ) - q) * ((U.card : ℝ) - q - 1)) /
    ((U.card : ℝ) * ((U.card : ℝ) - 1))

theorem average_equalIndicator (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (equalIndicator i j) = equalMean U q := by
  have hN : 2 ≤ U.card := by
    have hsub : ({i, j} : Finset V) ⊆ U := by
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have := Finset.card_le_card hsub
    simpa [hne] using this
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hf : equalIndicator i j =
      (fun S => 1 - coord i S - coord j S + 2 * (coord i S * coord j S)) := by
    funext S
    exact equalIndicator_eq i j S
  rw [hf, average_add, average_sub, average_sub, average_const U q hq 1,
    average_coord U q hq i hi, average_coord U q hq j hj,
    average_mul_left, average_coord_mul U q hq i j hi hj hne]
  unfold equalMean
  field_simp
  ring

def centeredEqual (U : Finset V) (q : ℕ) (i j : V) (S : Finset V) : ℝ :=
  equalIndicator i j S - equalMean U q

theorem average_centeredEqual (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (centeredEqual U q i j) = 0 := by
  unfold centeredEqual
  rw [average_sub, average_equalIndicator U q hq i j hi hj hne,
    average_const U q hq]
  ring

theorem average_centeredEqual_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (fun S => (centeredEqual U q i j S)^2) =
      equalMean U q * (1 - equalMean U q) := by
  have hf : (fun S => (centeredEqual U q i j S)^2) =
      (fun S => equalIndicator i j S -
        (2 * equalMean U q) * equalIndicator i j S + (equalMean U q)^2) := by
    funext S
    have hs := equalIndicator_sq i j S
    unfold centeredEqual
    nlinarith
  rw [hf, average_add, average_sub, average_mul_left,
    average_equalIndicator U q hq i j hi hj hne, average_const U q hq]
  ring

include sectionDecidableEqV in
theorem average_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) (f : Finset W → ℝ) :
    average (U.map e) q f = average U q (fun S => f (S.map e)) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.powersetCard_map]

@[simp] theorem coord_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (i : V) (S : Finset V) :
    coord (e i) (S.map e) = coord i S := by
  simp [coord]

@[simp] theorem equalIndicator_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (i j : V) (S : Finset V) :
    equalIndicator (e i) (e j) (S.map e) = equalIndicator i j S := by
  simp [equalIndicator]

include sectionDecidableEqV in
@[simp] theorem equalMean_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) :
    equalMean (U.map e) q = equalMean U q := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [equalMean]

@[simp] theorem centeredEqual_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) (i j : V) (S : Finset V) :
    centeredEqual (U.map e) q (e i) (e j) (S.map e) = centeredEqual U q i j S := by
  simp [centeredEqual]

theorem average_permute (e : Equiv.Perm V) (U : Finset V) (q : ℕ)
    (hU : U.map e.toEmbedding = U) (f : Finset V → ℝ) :
    average U q (fun S => f (S.map e.toEmbedding)) = average U q f := by
  rw [← average_map_embedding, hU]

theorem centeredEqual_covariance_map {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) (i j k l : V) :
    average (U.map e) q (fun S => centeredEqual (U.map e) q (e i) (e j) S *
      centeredEqual (U.map e) q (e k) (e l) S) =
    average U q (fun S => centeredEqual U q i j S * centeredEqual U q k l S) := by
  rw [average_map_embedding]
  simp

include sectionDecidableEqV in
theorem average_sq_eq_zero_iff (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f : Finset V → ℝ) :
    average U q (fun S => (f S)^2) = 0 ↔ ∀ S ∈ U.powersetCard q, f S = 0 := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  constructor
  · intro h S hS
    have hsum : (∑ T ∈ U.powersetCard q, (f T)^2) = 0 := by
      exact (div_eq_zero_iff.mp h).resolve_right hden
    have hf := (Finset.sum_eq_zero_iff_of_nonneg
      (fun T _ => sq_nonneg (f T))).mp hsum S hS
    exact sq_eq_zero_iff.mp hf
  · intro h
    unfold average
    have hs : (∑ S ∈ U.powersetCard q, (f S)^2) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      rw [h S hS]
      norm_num
    rw [hs, zero_div]

theorem centeredEqual_eq_zero_of_degenerate_mean (U : Finset V) (q : ℕ)
    (hq : q ≤ U.card) (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j)
    (hp : equalMean U q = 0 ∨ equalMean U q = 1) :
    ∀ S ∈ U.powersetCard q, centeredEqual U q i j S = 0 := by
  apply (average_sq_eq_zero_iff U q hq (centeredEqual U q i j)).mp
  rw [average_centeredEqual_sq U q hq i j hi hj hne]
  rcases hp with hp | hp <;> rw [hp] <;> norm_num

theorem centeredEqual_eq_zero_of_boundary (U : Finset V) (q : ℕ)
    (hq : q ≤ U.card) (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j)
    (hboundary : q = 0 ∨ q = U.card ∨ U.card ≤ 2) :
    ∀ S ∈ U.powersetCard q, centeredEqual U q i j S = 0 := by
  have hN : 2 ≤ U.card := by
    have hsub : ({i, j} : Finset V) ⊆ U := by
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have := Finset.card_le_card hsub
    simpa [hne] using this
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  apply centeredEqual_eq_zero_of_degenerate_mean U q hq i j hi hj hne
  rcases hboundary with hzero | hfull | hsmall
  · right
    subst q
    unfold equalMean
    field_simp
    ring
  · right
    subst q
    unfold equalMean
    field_simp
    ring
  · have hcard : U.card = 2 := by omega
    have hq2 : q ≤ 2 := by omega
    interval_cases q <;> norm_num [equalMean, hcard]

abbrev State (U : Finset V) (q : ℕ) := ↥(U.powersetCard q)

include sectionDecidableEqV in
theorem average_eq_fintype_sum (U : Finset V) (q : ℕ) (f : Finset V → ℝ) :
    average U q f = (∑ S : State U q, f S.val) / (Fintype.card (State U q) : ℝ) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, State, Finset.sum_attach, Finset.card_powersetCard]

def vector (U : Finset V) (q : ℕ) (f : Finset V → ℝ) : EuclideanSpace ℝ (State U q) :=
  WithLp.toLp 2 (fun S => f S.val)

theorem vector_norm_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f : Finset V → ℝ) :
    ‖vector U q f‖^2 = (U.card.choose q : ℝ) * average U q (fun S => (f S)^2) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  rw [EuclideanSpace.real_norm_sq_eq, average_eq_fintype_sum]
  simp [vector, State, Finset.card_powersetCard]
  field_simp

theorem vector_inner (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f g : Finset V → ℝ) :
    inner ℝ (vector U q f) (vector U q g) =
      (U.card.choose q : ℝ) * average U q (fun S => f S * g S) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  rw [PiLp.inner_apply, average_eq_fintype_sum]
  simp [vector, State, Finset.card_powersetCard, mul_comm]
  field_simp

end Problem315.SliceMoments

end

end OAI
