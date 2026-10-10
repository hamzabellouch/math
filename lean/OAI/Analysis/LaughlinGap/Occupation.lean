import Mathlib

namespace OAI

/-! Occupation. -/

noncomputable section


namespace LaughlinGap
namespace Occupation
open scoped BigOperators InnerProduct

abbrev Hilbert (n : ℕ) := EuclideanSpace ℂ (Finset (Fin n))

def flip {n : ℕ} (j : Fin n) : Equiv.Perm (Finset (Fin n)) :=
  let f : Finset (Fin n) → Finset (Fin n) := fun A => if j ∈ A then A.erase j else insert j A
  have h : Function.Involutive f := by
    intro A
    by_cases hj : j ∈ A <;> simp [f, hj]
  ⟨f, f, h, h⟩

@[simp] lemma flip_of_mem {n : ℕ} {j : Fin n} {A : Finset (Fin n)} (h : j ∈ A) :
    flip j A = A.erase j := ite_eq_left h

@[simp] lemma flip_of_not_mem {n : ℕ} {j : Fin n} {A : Finset (Fin n)} (h : j ∉ A) :
    flip j A = insert j A := ite_eq_right h

@[simp] lemma flip_flip {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : flip j (flip j A) = A :=
  (flip j).left_inv A

@[simp] lemma mem_flip_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    j ∈ flip j A ↔ j ∉ A := by
  by_cases hj : j ∈ A <;> simp [hj]

@[simp] lemma mem_flip_other {n : ℕ} {i j : Fin n} (hij : i ≠ j) (A : Finset (Fin n)) :
    i ∈ flip j A ↔ i ∈ A := by
  by_cases hj : j ∈ A <;> simp [hj, hij]

lemma flip_comm {n : ℕ} (i j : Fin n) (A : Finset (Fin n)) :
    flip i (flip j A) = flip j (flip i A) := by
  by_cases hij : i = j
  · subst j; rfl
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  by_cases hkj : k = j
  · subst k
    simp [Ne.symm hij]
  simp [hki, hkj]

def sign {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : ℂ :=
  (-1 : ℂ) ^ (A.filter (fun k => k < j)).card

@[simp] lemma sign_norm {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : ‖sign j A‖ = 1 := by
  simp [sign, norm_pow]

@[simp] lemma sign_star {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : star (sign j A) = sign j A := by
  simp [sign]

@[simp] lemma sign_sq {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : sign j A * sign j A = 1 := by
  unfold sign
  rw [← mul_pow]
  norm_num

lemma sign_insert {n : ℕ} (j : Fin n) {i : Fin n} {A : Finset (Fin n)} (hi : i ∉ A) :
    sign j (insert i A) = if i < j then -sign j A else sign j A := by
  by_cases hij : i < j
  · simp [sign, Finset.filter_insert, hij, Finset.card_insert_of_notMem, hi, pow_succ]
  · simp [sign, Finset.filter_insert, hij]

lemma sign_flip {n : ℕ} (i j : Fin n) (A : Finset (Fin n)) :
    sign j (flip i A) = if i < j then -sign j A else sign j A := by
  by_cases hi : i ∈ A
  · have h := sign_insert j (Finset.notMem_erase i A)
    rw [Finset.insert_erase hi] at h
    rw [flip_of_mem hi]
    split_ifs with hij
    · simp only [ite_eq_left hij] at h
      rw [h, neg_neg]
    · simpa [hij] using h.symm
  · rw [flip_of_not_mem hi, sign_insert j hi]

@[simp] lemma sign_flip_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    sign j (flip j A) = sign j A := by simp [sign_flip]

@[simp] lemma sign_conj {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    starRingEnd ℂ (sign j A) = sign j A := by
  simp only [sign, map_pow, map_neg, map_one]

@[simp] lemma sign_erase_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    sign j (A.erase j) = sign j A := by
  simp [sign, Finset.filter_erase]

@[simp] lemma sign_insert_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    sign j (insert j A) = sign j A := by
  simp [sign, Finset.filter_insert]

noncomputable def transition {n : ℕ} (j : Fin n) (ε : Bool) : Hilbert n →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A =>
    if (decide (j ∈ A)) = ε then sign j A * x (flip j A) else 0)
  map_add' x y := by
    ext A
    by_cases h : (decide (j ∈ A)) = ε <;> simp [h, mul_add]
  map_smul' c x := by
    ext A
    by_cases h : (decide (j ∈ A)) = ε <;> simp [h, mul_left_comm]

@[simp] lemma transition_apply {n : ℕ} (j : Fin n) (ε : Bool) (x : Hilbert n)
    (A : Finset (Fin n)) :
    transition j ε x A = if (decide (j ∈ A)) = ε then sign j A * x (flip j A) else 0 := rfl

noncomputable abbrev annihilation {n : ℕ} (j : Fin n) := transition j false

noncomputable abbrev creation {n : ℕ} (j : Fin n) := transition j true

theorem transition_norm_le {n : ℕ} (j : Fin n) (ε : Bool) (x : Hilbert n) :
    ‖transition j ε x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    (∑ A, ‖transition j ε x A‖ ^ 2) ≤ ∑ A, ‖x (flip j A)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro A _
      rw [transition_apply]
      split_ifs
      · simp
      · simp
    _ = _ := Equiv.sum_comp (flip j) (fun A => ‖x A‖ ^ 2)

theorem transition_adjoint {n : ℕ} (j : Fin n) (ε : Bool) :
    (transition j ε).adjoint = transition j (!ε) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [← Equiv.sum_comp (flip j) (fun A => inner ℂ (x A) (transition j ε y A))]
  apply Finset.sum_congr rfl
  intro A _
  cases ε <;> by_cases hj : j ∈ A <;>
    simp [transition_apply, hj] <;> ring

theorem transition_anticommute_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ε η : Bool) :
    (transition i ε ∘ₗ transition j η) = -(transition j η ∘ₗ transition i ε) := by
  ext x A
  change transition i ε (transition j η x) A = -transition j η (transition i ε x) A
  simp only [transition_apply, mem_flip_other hij, mem_flip_other (Ne.symm hij), sign_flip]
  rw [flip_comm j i A]
  by_cases hi : (decide (i ∈ A)) = ε <;> by_cases hj : (decide (j ∈ A)) = η
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp [hi, hj, hlt, not_lt_of_ge (le_of_lt hlt)]
      ring
    · simp [hi, hj, hgt, not_lt_of_ge (le_of_lt hgt)]
      ring
  all_goals simp [hi, hj]

theorem transition_square {n : ℕ} (j : Fin n) (ε : Bool) :
    transition j ε ∘ₗ transition j ε = 0 := by
  ext x A
  change transition j ε (transition j ε x) A = 0
  cases ε <;> by_cases hj : j ∈ A <;> simp [transition_apply, hj]

theorem transition_complement {n : ℕ} (j : Fin n) (ε : Bool) :
    transition j ε ∘ₗ transition j (!ε) + transition j (!ε) ∘ₗ transition j ε =
      LinearMap.id := by
  ext x A
  change transition j ε (transition j (!ε) x) A +
    transition j (!ε) (transition j ε x) A = x A
  cases ε <;> by_cases hj : j ∈ A <;> simp [transition_apply, hj, ← mul_assoc]

theorem annihilation_creation_CAR {n : ℕ} (i j : Fin n) :
    annihilation i ∘ₗ creation j + creation j ∘ₗ annihilation i =
      if i = j then LinearMap.id else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using transition_complement i false
  · rw [ite_eq_right hij, transition_anticommute_of_ne hij false true]
    exact neg_add_cancel _

@[simp] lemma annihilation_adjoint {n : ℕ} (i : Fin n) :
    (annihilation i).adjoint = creation i := transition_adjoint i false

@[simp] lemma creation_adjoint {n : ℕ} (i : Fin n) :
    (creation i).adjoint = annihilation i := transition_adjoint i true

lemma adjoint_mul {n : ℕ} (A B : Module.End ℂ (Hilbert n)) :
    (A * B).adjoint = B.adjoint * A.adjoint := LinearMap.adjoint_comp A B

theorem annihilation_creation {n : ℕ} (i j : Fin n) :
    annihilation i * creation j = (if i = j then 1 else 0) - creation j * annihilation i := by
  exact eq_sub_of_add_eq (annihilation_creation_CAR i j)

theorem annihilation_creation_mul {n : ℕ} (i j : Fin n)
    (X : Module.End ℂ (Hilbert n)) :
    annihilation i * (creation j * X) =
      (if i = j then X else 0) - creation j * (annihilation i * X) := by
  rw [← mul_assoc, annihilation_creation, sub_mul]
  by_cases hij : i = j <;> simp [hij, mul_assoc]

theorem pair_normal_order {n : ℕ} (i j k l : Fin n) :
    annihilation j * annihilation i * creation k * creation l =
      (if i = k ∧ j = l then 1 else 0) -
      (if j = k ∧ i = l then 1 else 0) -
      (if i = k then creation l * annihilation j else 0) +
      (if j = k then creation l * annihilation i else 0) +
      (if i = l then creation k * annihilation j else 0) -
      (if j = l then creation k * annihilation i else 0) +
      creation k * creation l * annihilation j * annihilation i := by
  rw [mul_assoc, mul_assoc, annihilation_creation_mul]
  simp only [mul_sub]
  rw [annihilation_creation_mul]
  rw [annihilation_creation]
  simp only [mul_sub, mul_ite, mul_one, mul_zero, annihilation_creation_mul]
  rw [annihilation_creation]
  simp only [ite_and]
  split_ifs <;> noncomm_ring

theorem auxiliary_normal_order {n : ℕ} (i k : Fin n)
    (A B : Module.End ℂ (Hilbert n)) :
    (creation i * A).adjoint * (creation k * B) =
      (if i = k then A.adjoint * B else 0) -
      (annihilation k * A).adjoint * (annihilation i * B) := by
  rw [adjoint_mul, creation_adjoint, mul_assoc, annihilation_creation_mul,
    mul_sub, adjoint_mul, annihilation_adjoint, mul_assoc]
  by_cases hik : i = k <;> simp [hik]

noncomputable def auxiliaryRow {n : ℕ} {ι : Type*} [Fintype ι] (lam : ℝ)
    (Bt : Module.End ℂ (Hilbert n)) (α : ι → ℝ) (i : ι → Fin n)
    (A : ι → Module.End ℂ (Hilbert n)) : Module.End ℂ (Hilbert n) :=
  (lam : ℂ) • Bt + ∑ b, (α b : ℂ) • (creation (i b) * A b)

theorem auxiliaryRow_square {n : ℕ} {ι : Type*} [Fintype ι] (lam : ℝ)
    (Bt : Module.End ℂ (Hilbert n)) (α : ι → ℝ) (i : ι → Fin n)
    (A : ι → Module.End ℂ (Hilbert n)) :
    (auxiliaryRow lam Bt α i A).adjoint * auxiliaryRow lam Bt α i A =
      ((lam ^ 2 : ℝ) : ℂ) • (Bt.adjoint * Bt) +
      (∑ b, ((lam * α b : ℝ) : ℂ) •
        ((annihilation (i b) * Bt).adjoint * A b + (A b).adjoint * (annihilation (i b) * Bt))) +
      (∑ b, ∑ c, ((α b * α c : ℝ) : ℂ) •
        (if i b = i c then (A b).adjoint * A c else 0)) -
      (∑ b, ∑ c, ((α b * α c : ℝ) : ℂ) •
        ((annihilation (i c) * A b).adjoint * (annihilation (i b) * A c))) := by
  classical
  have hcross (b : ι) :
      Bt.adjoint * (creation (i b) * A b) = (annihilation (i b) * Bt).adjoint * A b := by
    rw [adjoint_mul, annihilation_adjoint, mul_assoc]
  rw [auxiliaryRow, map_add, map_sum]
  simp only [map_smulₛₗ, Complex.conj_ofReal, add_mul, mul_add,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  simp only [smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun c b => ((α c : ℂ) * (α b : ℂ)) • (LinearMap.adjoint (creation (i b) * A b) * (creation (i c) * A c)))]
  simp only [auxiliary_normal_order, smul_sub, Finset.sum_sub_distrib, hcross]
  simp only [adjoint_mul, creation_adjoint, annihilation_adjoint, mul_assoc,
    Complex.ofReal_mul, pow_two]
  simp only [mul_comm]
  abel

theorem double_annihilation_norm_le {n : ℕ} (j k : Fin n) (x : Hilbert n) :
    ‖annihilation k (annihilation j x)‖ ≤ ‖x‖ :=
  (transition_norm_le k false _).trans (transition_norm_le j false x)

noncomputable def weight {n : ℕ} (d : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∏ j ∈ A, d j

noncomputable def diagonal {n : ℕ} (d : Fin n → ℝ) : Hilbert n →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A => (weight d A : ℂ) * x A)
  map_add' x y := by ext A; simp [mul_add]
  map_smul' c x := by ext A; simp [mul_left_comm]

@[simp] lemma diagonal_apply {n : ℕ} (d : Fin n → ℝ) (x : Hilbert n) (A : Finset (Fin n)) :
    diagonal d x A = (weight d A : ℂ) * x A := rfl

lemma weight_nonneg {n : ℕ} {d : Fin n → ℝ} (hd : ∀ j, 0 ≤ d j) (A : Finset (Fin n)) :
    0 ≤ weight d A := Finset.prod_nonneg (fun j _ => hd j)

lemma weight_le_one {n : ℕ} {d : Fin n → ℝ} (hd₀ : ∀ j, 0 ≤ d j) (hd₁ : ∀ j, d j ≤ 1)
    (A : Finset (Fin n)) : weight d A ≤ 1 :=
  Finset.prod_le_one₀ (fun index _ => hd₀ index) (fun index _ => hd₁ index)

theorem diagonal_norm_le {n : ℕ} {d : Fin n → ℝ} (hd₀ : ∀ j, 0 ≤ d j)
    (hd₁ : ∀ j, d j ≤ 1) (x : Hilbert n) : ‖diagonal d x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, diagonal_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (weight_nonneg hd₀ _)]
  apply Finset.sum_le_sum
  intro A _
  exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg hd₀ A) (norm_nonneg _))
    (mul_le_of_le_one_left (norm_nonneg _) (weight_le_one hd₀ hd₁ A)) 2

@[simp] theorem diagonal_one {n : ℕ} : diagonal (fun _ : Fin n => (1 : ℝ)) = LinearMap.id := by
  ext x A
  simp [diagonal_apply, weight]

theorem diagonal_comp {n : ℕ} (d e : Fin n → ℝ) :
    diagonal d ∘ₗ diagonal e = diagonal (fun j => d j * e j) := by
  ext x A
  simp [diagonal_apply, weight, Finset.prod_mul_distrib, mul_assoc]

theorem diagonal_comp_inv {n : ℕ} (d : Fin n → ℝ) (hd : ∀ j, d j ≠ 0) :
    diagonal d ∘ₗ diagonal (fun j => (d j)⁻¹) = LinearMap.id := by
  rw [diagonal_comp]
  have h : (fun j => d j * (d j)⁻¹) = (fun _ : Fin n => (1 : ℝ)) := by
    funext j
    exact mul_inv_cancel₀ (hd j)
  rw [h, diagonal_one]

theorem annihilation_diagonal {n : ℕ} (d : Fin n → ℝ) (j : Fin n) :
    annihilation j ∘ₗ diagonal d = (d j : ℂ) • (diagonal d ∘ₗ annihilation j) := by
  ext x A
  change annihilation j (diagonal d x) A = (d j : ℂ) * diagonal d (annihilation j x) A
  by_cases hj : j ∈ A
  · simp [transition_apply, hj]
  · simp [transition_apply, hj, weight, Finset.prod_insert, mul_assoc, mul_comm, mul_left_comm]

noncomputable def word {n : ℕ} : List (Fin n) → Hilbert n →ₗ[ℂ] Hilbert n
  | [] => LinearMap.id
  | j :: js => word js ∘ₗ annihilation j

theorem word_diagonal {n : ℕ} (d : Fin n → ℝ) (js : List (Fin n)) :
    word js ∘ₗ diagonal d = ((js.map (fun j => (d j : ℂ))).prod) • (diagonal d ∘ₗ word js) := by
  induction js with
  | nil => simp [word]
  | cons j js ih =>
    rw [word, LinearMap.comp_assoc, annihilation_diagonal,
      LinearMap.comp_smul, ← LinearMap.comp_assoc, ih]
    simp only [List.map_cons, List.prod_cons, LinearMap.smul_comp, smul_smul,
      LinearMap.comp_assoc]

noncomputable def pairAnnihilator {n : ℕ} (v : Fin n → Fin n → ℂ) :
    Module.End ℂ (Hilbert n) :=
  ∑ x, ∑ y, if x < y then star (v x y) • (annihilation y * annihilation x) else 0

lemma pairAnnihilator_smul_real {n : ℕ} (v : Fin n → Fin n → ℂ) (r : ℝ) :
    pairAnnihilator (fun x y => (r : ℂ) * v x y) = (r : ℂ) • pairAnnihilator v := by
  simp only [pairAnnihilator, Finset.smul_sum, smul_ite, smul_zero, star_mul,
    Complex.star_def, Complex.conj_ofReal, smul_smul, mul_comm]

theorem pairAnnihilator_diagonal {n : ℕ} (d : Fin n → ℝ) (v : Fin n → Fin n → ℂ) :
    pairAnnihilator v * diagonal d =
      diagonal d * pairAnnihilator (fun x y => (d x * d y : ℝ) * v x y) := by
  simp only [pairAnnihilator, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x < y
  · simp only [ite_eq_left hxy, smul_mul_assoc, mul_smul_comm, star_mul, Complex.ofReal_mul,
      Complex.star_def, Complex.conj_ofReal]
    have hw := word_diagonal d [x,y]
    simp only [word, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
      mul_one, LinearMap.id_comp] at hw
    change starRingEnd ℂ (v x y) • ((annihilation y ∘ₗ annihilation x) ∘ₗ diagonal d) = _
    rw [hw, smul_smul]
    simp only [mul_comm]
    rfl
  · simp [hxy]

theorem pairAnnihilator_conjugation {n : ℕ} (d : Fin n → ℝ) (hd : ∀ j, d j ≠ 0)
    (v : Fin n → Fin n → ℂ) (r : ℝ) :
    pairAnnihilator (fun x y => (r : ℂ) * ((d x * d y : ℝ) * v x y)) =
      (r : ℂ) • (diagonal (fun j => (d j)⁻¹) * pairAnnihilator v * diagonal d) := by
  rw [pairAnnihilator_smul_real]
  congr 1
  rw [mul_assoc, pairAnnihilator_diagonal, ← mul_assoc]
  have hd' : ∀ j, (d j)⁻¹ ≠ 0 := fun j => inv_ne_zero (hd j)
  have hinv := diagonal_comp_inv (fun j => (d j)⁻¹) hd'
  simp only [inv_inv] at hinv
  change _ = (diagonal (fun j => (d j)⁻¹) ∘ₗ diagonal d) * _
  rw [hinv]
  exact (one_mul _).symm

theorem fourAnnihilator_conjugation {n : ℕ} (d : Fin n → ℝ) (hd : ∀ j, d j ≠ 0)
    (v : Fin n → Fin n → ℂ) (r : ℝ) (j k : Fin n) :
    annihilation k * annihilation j *
      pairAnnihilator (fun x y => (r : ℂ) * ((d x * d y : ℝ) * v x y)) =
      ((r / (d j * d k) : ℝ) : ℂ) •
        (diagonal (fun s => (d s)⁻¹) * (annihilation k * annihilation j * pairAnnihilator v) * diagonal d) := by
  rw [pairAnnihilator_conjugation d hd v r, mul_smul_comm, ← mul_assoc, ← mul_assoc]
  have hw := word_diagonal (fun s => (d s)⁻¹) [j,k]
  simp only [word, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
    mul_one, LinearMap.id_comp] at hw
  change (r : ℂ) • ((((annihilation k ∘ₗ annihilation j) ∘ₗ diagonal (fun s => (d s)⁻¹)) *
    pairAnnihilator v) * diagonal d) = _
  rw [hw]
  simp only [← Module.End.mul_eq_comp, smul_mul_assoc, smul_smul, mul_assoc,
    Complex.ofReal_inv, Complex.ofReal_mul, mul_inv_rev, div_eq_mul_inv, mul_comm]

theorem pairAnnihilator_energy_transfer {n : ℕ} (d : Fin n → ℝ)
    (hd₀ : ∀ j, 0 ≤ d j) (hd₁ : ∀ j, d j ≤ 1)
    (v : Fin n → Fin n → ℂ) {r : ℝ} (hr : 1 ≤ r) (x : Hilbert n) :
    ‖pairAnnihilator v (diagonal d x)‖ ^ 2 ≤
      ‖pairAnnihilator (fun i j => (r : ℂ) * ((d i * d j : ℝ) * v i j)) x‖ ^ 2 := by
  have hc := LinearMap.congr_fun (pairAnnihilator_diagonal d v) x
  change pairAnnihilator v (diagonal d x) =
    diagonal d (pairAnnihilator (fun i j => (d i * d j : ℝ) * v i j) x) at hc
  rw [hc, pairAnnihilator_smul_real, LinearMap.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by linarith : 0 ≤ r)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (diagonal_norm_le hd₀ hd₁ _).trans (le_mul_of_one_le_left (norm_nonneg _) hr)

end Occupation
end LaughlinGap
namespace LaughlinGap
open scoped BigOperators Topology
open Filter

noncomputable def orbitalDiagonalFactor (Q x : ℕ) : ℝ :=
  Real.sqrt ((Q.descFactorial x : ℝ) / (Q : ℝ)^x)

noncomputable def pairRescalingFactor (Q p : ℕ) : ℝ :=
  Real.sqrt ((2 * (Q : ℝ))^p / ((2*Q-2).descFactorial p : ℝ))

noncomputable def sphericalExteriorPairCoefficient (Q p x y : ℕ) : ℝ :=
  if x + y = p + 1 then
    ((x : ℝ) - (y : ℝ)) * Real.sqrt
      ((Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * (p.factorial : ℝ) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.factorial : ℝ) * (y.factorial : ℝ)))
  else 0

noncomputable def limitingExteriorPairCoefficient (p x y : ℕ) : ℝ :=
  if x + y = p + 1 then
    ((x : ℝ) - (y : ℝ)) * Real.sqrt
      ((p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ)))
  else 0

lemma orbitalDiagonalFactor_nonneg (Q x : ℕ) : 0 ≤ orbitalDiagonalFactor Q x :=
  Real.sqrt_nonneg _

lemma orbitalDiagonalFactor_pos {Q x : ℕ} (hQ : 0 < Q) (hx : x ≤ Q) :
    0 < orbitalDiagonalFactor Q x := by
  apply Real.sqrt_pos_of_pos
  have : (0 : ℝ) < (Q.descFactorial x : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hx
  positivity

lemma orbitalDiagonalFactor_le_one (Q x : ℕ) : orbitalDiagonalFactor Q x ≤ 1 := by
  rw [orbitalDiagonalFactor, Real.sqrt_le_one]
  by_cases hQ : (Q : ℝ)^x = 0
  · simp [hQ]
  · rw [div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hQ))]
    exact_mod_cast Nat.descFactorial_le_pow Q x

lemma pairRescalingFactor_nonneg (Q p : ℕ) : 0 ≤ pairRescalingFactor Q p :=
  Real.sqrt_nonneg _

lemma one_le_pairRescalingFactor {Q p : ℕ} (hp : p ≤ 2*Q-2) :
    1 ≤ pairRescalingFactor Q p := by
  rw [pairRescalingFactor, Real.one_le_sqrt]
  have hd : (0 : ℝ) < ((2*Q-2).descFactorial p : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hp
  rw [le_div_iff₀ hd, one_mul]
  exact_mod_cast (Nat.descFactorial_le_pow (2*Q-2) p).trans
    (Nat.pow_le_pow_left (by omega : 2*Q-2 ≤ 2*Q) p)

theorem sphericalExteriorPairCoefficient_factor {Q p : ℕ} (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : ℕ) :
    sphericalExteriorPairCoefficient Q p x y =
      pairRescalingFactor Q p * orbitalDiagonalFactor Q x * orbitalDiagonalFactor Q y *
        limitingExteriorPairCoefficient p x y := by
  by_cases hxy : x + y = p + 1
  · have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    have hD0 : ((2*Q-2).descFactorial p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hp))
    have hx0 : (x.factorial : ℝ) ≠ 0 := by exact_mod_cast x.factorial_ne_zero
    have hy0 : (y.factorial : ℝ) ≠ 0 := by exact_mod_cast y.factorial_ne_zero
    have hpow : (Q : ℝ)^x * (Q : ℝ)^y = (Q : ℝ)^p * Q := by
      rw [← pow_add, hxy, pow_succ]
    have hr : Real.sqrt
        ((Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * (p.factorial : ℝ) /
          ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.factorial : ℝ) * (y.factorial : ℝ))) =
        pairRescalingFactor Q p * orbitalDiagonalFactor Q x * orbitalDiagonalFactor Q y *
          Real.sqrt ((p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ))) := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by
        unfold pairRescalingFactor orbitalDiagonalFactor; positivity)).mp
      simp only [pairRescalingFactor, orbitalDiagonalFactor, mul_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ (Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * (p.factorial : ℝ) /
          ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.factorial : ℝ) * (y.factorial : ℝ)) from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (2:ℝ)^p * (Q : ℝ)^p / ((2*Q-2).descFactorial p : ℝ) from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (Q.descFactorial x : ℝ) / (Q : ℝ)^x from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (Q.descFactorial y : ℝ) / (Q : ℝ)^y from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ)) from by positivity)]
      field_simp
      calc
        _ = (Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * ((Q:ℝ)^x * (Q:ℝ)^y) := by ring
        _ = _ := by rw [hpow]; ring
    simp only [sphericalExteriorPairCoefficient, limitingExteriorPairCoefficient, ite_eq_left hxy]
    rw [hr]
    ring
  · simp [sphericalExteriorPairCoefficient, limitingExteriorPairCoefficient, hxy]

lemma normalizedFallingFactorial_eq_prod (Q x : ℕ) :
    (Q.descFactorial x : ℝ) / (Q : ℝ)^x =
      ∏ k ∈ Finset.range x, ((Q - k : ℕ) : ℝ) / (Q : ℝ) := by
  simp [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]

lemma normalizedFallingFactor_tendsto (k : ℕ) :
    Tendsto (fun Q : ℕ => ((Q - k : ℕ) : ℝ) / (Q : ℝ)) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k+1)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [Nat.cast_sub (by omega : k ≤ Q)]
  field_simp

theorem orbitalDiagonalFactor_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => orbitalDiagonalFactor Q x) atTop (𝓝 1) := by
  have h := tendsto_finsetProd (Finset.range x) (fun k _ => normalizedFallingFactor_tendsto k)
  simp only [Finset.prod_const_one, ← normalizedFallingFactorial_eq_prod] at h
  simpa only [Real.sqrt_one, orbitalDiagonalFactor, Function.comp_def] using Real.continuous_sqrt.tendsto 1 |>.comp h

lemma pairRescalingFactor_sq_eq_prod (Q p : ℕ) :
    (2 * (Q : ℝ))^p / ((2*Q-2).descFactorial p : ℝ) =
      ∏ k ∈ Finset.range p, (2*(Q : ℝ)) / ((2*Q-2-k : ℕ) : ℝ) := by
  simp [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]

lemma rescalingFactor_tendsto (k : ℕ) :
    Tendsto (fun Q : ℕ => (2*(Q : ℝ)) / ((2*Q-2-k : ℕ) : ℝ)) atTop (𝓝 1) := by
  have ht : Tendsto (fun Q : ℕ => (2 : ℝ) / (2 - ((k : ℝ)+2)/Q)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ)+2))) (by norm_num : (2 : ℝ)-0 ≠ 0)
    simpa only [Pi.div_def, sub_zero, div_self (by norm_num : (2:ℝ) ≠ 0)] using h
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k+3)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [Nat.cast_sub (by omega : k ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  ring

theorem pairRescalingFactor_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairRescalingFactor Q p) atTop (𝓝 1) := by
  have h := tendsto_finsetProd (Finset.range p) (fun k _ => rescalingFactor_tendsto k)
  simp only [Finset.prod_const_one, ← pairRescalingFactor_sq_eq_prod] at h
  simpa only [Real.sqrt_one, pairRescalingFactor, Function.comp_def] using Real.continuous_sqrt.tendsto 1 |>.comp h

theorem sphericalExteriorPairCoefficient_tendsto (p x y : ℕ) :
    Tendsto (fun Q : ℕ => sphericalExteriorPairCoefficient Q p x y) atTop
      (𝓝 (limitingExteriorPairCoefficient p x y)) := by
  have h := (((pairRescalingFactor_tendsto p).mul (orbitalDiagonalFactor_tendsto x)).mul
    (orbitalDiagonalFactor_tendsto y)).mul_const (limitingExteriorPairCoefficient p x y)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (p+2)] with Q hQ
  exact (sphericalExteriorPairCoefficient_factor (by omega) (by omega) x y).symm

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators Topology
open Filter

noncomputable def diagonalCLM {n : ℕ} (d : Fin n → ℝ) : Hilbert n →L[ℂ] Hilbert n :=
  LinearMap.toContinuousLinearMap (diagonal d)

@[simp] lemma diagonalCLM_apply {n : ℕ} (d : Fin n → ℝ) (x : Hilbert n) :
    diagonalCLM d x = diagonal d x := rfl

lemma diagonalCLM_eq_matrix {n : ℕ} (d : Fin n → ℝ) :
    diagonalCLM d = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Finset (Fin n)) (Matrix.diagonal (fun A => (weight d A : ℂ))) := by
  ext x A
  change (diagonalCLM d x).ofLp A = _
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  rfl

theorem diagonalCLM_tendsto {n : ℕ} {ι : Type*} {l : Filter ι}
    {d : ι → Fin n → ℝ} {e : Fin n → ℝ}
    (hd : ∀ j, Tendsto (fun q => d q j) l (𝓝 (e j))) :
    Tendsto (fun q => diagonalCLM (d q)) l (𝓝 (diagonalCLM e)) := by
  have hw (A : Finset (Fin n)) : Tendsto (fun q => weight (d q) A) l (𝓝 (weight e A)) :=
    tendsto_finsetProd A (fun j _ => hd j)
  have hM : Tendsto (fun q => Matrix.diagonal (fun A => (weight (d q) A : ℂ))) l
      (𝓝 (Matrix.diagonal (fun A => (weight e A : ℂ)))) := by
    apply tendsto_pi_nhds.mpr
    intro A
    apply tendsto_pi_nhds.mpr
    intro B
    by_cases hAB : A = B
    · subst B
      simpa only [Matrix.diagonal_apply_eq, Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp (hw A)
    · simpa [Matrix.diagonal, hAB] using (tendsto_const_nhds (x := (0 : ℂ)))
  have hc : Continuous (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Finset (Fin n))) :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Finset (Fin n))).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  simp_rw [diagonalCLM_eq_matrix]
  exact hc.continuousAt.tendsto.comp hM

@[simp] lemma diagonalCLM_one {n : ℕ} : diagonalCLM (fun _ : Fin n => (1 : ℝ)) = 1 := by
  ext x A
  simp [diagonalCLM_apply, diagonal_one]

theorem diagonalCLM_inv_tendsto_one {n : ℕ} {ι : Type*} {l : Filter ι}
    {d : ι → Fin n → ℝ} (hd : ∀ j, Tendsto (fun q => d q j) l (𝓝 1)) :
    Tendsto (fun q => diagonalCLM (fun j => (d q j)⁻¹)) l (𝓝 1) := by
  have hi (j : Fin n) : Tendsto (fun q => (d q j)⁻¹) l (𝓝 1) := by
    simpa using (hd j).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa using diagonalCLM_tendsto hi

end LaughlinGap.Occupation

end

end OAI
