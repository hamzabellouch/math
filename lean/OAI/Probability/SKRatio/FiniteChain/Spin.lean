import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter

namespace SKRatio

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def coupling {n : ℕ} (g : Disorder n) (i j : Fin n) : ℝ :=
  if h : i < j then g ⟨(i, j), h⟩ else
    if h : j < i then g ⟨(j, i), h⟩ else 0

def hamiltonian {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, spinValue (x i) * coupling g i j * spinValue (x j) +
    ∑ i, h i * spinValue (x i)

def weight {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian g h x)

def partition {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) : ℝ :=
  ∑ x, weight g h x

def mass {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  weight g h x / partition g h

def flip {n : ℕ} (i : Fin n) (x : Spin n) : Spin n :=
  Function.update x i (!(x i))

def disorderLaw (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 (Real.toNNReal (β ^ 2 / n)))

def siteKernel {n : ℕ} (g : Disorder n) (i : Fin n) :
    Matrix (Spin n) (Spin n) ℝ := fun x y =>
  (if y = x then mass g 0 x / (mass g 0 x + mass g 0 (flip i x)) else 0) +
  (if y = flip i x then
    mass g 0 (flip i x) / (mass g 0 x + mass g 0 (flip i x)) else 0)

def transition {n : ℕ} (g : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  if n = 0 then 1 else fun x y => (∑ i, siteKernel g i x y) / (n : ℝ)

def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |p y - q y|

def discreteDistance {n : ℕ} (g : Disorder n) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x : Spin n => totalVariation ((transition g ^ k) x) (mass g 0))

def mixingTime {n : ℕ} (g : Disorder n) (ε : ℝ) : ℕ :=
  sInf {k : ℕ | discreteDistance g k ≤ ε}

section ElementaryGibbs
variable {n : ℕ}

@[simp] theorem coupling_diag (g : Disorder n) (i : Fin n) : coupling g i i = 0 := by
  simp [coupling]

theorem coupling_symm (g : Disorder n) (i j : Fin n) : coupling g i j = coupling g j i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [coupling, hij, not_lt_of_gt hij]
  · rfl
  · simp [coupling, hji, not_lt_of_gt hji]

@[simp] theorem flip_same (i : Fin n) (x : Spin n) : flip i x i = !(x i) := by
  simp [flip]

@[simp] theorem flip_other (i j : Fin n) (x : Spin n) (h : j ≠ i) : flip i x j = x j := by
  simp [flip, h]

@[simp] theorem flip_flip (i : Fin n) (x : Spin n) : flip i (flip i x) = x := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [flip_other, h]

@[simp] theorem flip_ne (i : Fin n) (x : Spin n) : flip i x ≠ x := by
  intro h
  have hi := congrFun h i
  simp at hi

theorem weight_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < weight g h x := Real.exp_pos _

theorem partition_pos (g : Disorder n) (h : Fin n → ℝ) : 0 < partition g h := by
  exact Finset.sum_pos (fun x _ => weight_pos g h x) Finset.univ_nonempty

theorem mass_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < mass g h x := div_pos (weight_pos g h x) (partition_pos g h)

theorem mass_nonneg (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 ≤ mass g h x := (mass_pos g h x).le

@[simp] theorem sum_mass (g : Disorder n) (h : Fin n → ℝ) : ∑ x, mass g h x = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos g h))

theorem mass_le_one (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    mass g h x ≤ 1 := by
  calc
    mass g h x ≤ ∑ y, mass g h y :=
      Finset.single_le_sum (fun y _ => mass_nonneg g h y) (Finset.mem_univ x)
    _ = 1 := sum_mass g h

instance disorderLaw_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by
  unfold disorderLaw
  infer_instance

end ElementaryGibbs

section HeatBath
variable {n : ℕ}

theorem siteKernel_nonneg (g : Disorder n) (i : Fin n) (x y : Spin n) :
    0 ≤ siteKernel g i x y := by
  unfold siteKernel
  have hx := mass_nonneg g 0 x
  have hf := mass_nonneg g 0 (flip i x)
  positivity

@[simp] theorem sum_siteKernel (g : Disorder n) (i : Fin n) (x : Spin n) :
    ∑ y, siteKernel g i x y = 1 := by
  have hd : mass g 0 x + mass g 0 (flip i x) ≠ 0 :=
    ne_of_gt (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x)))
  simp only [siteKernel, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rw [← add_div, div_self hd]

theorem siteKernel_balance (g : Disorder n) (i : Fin n) (x y : Spin n) :
    mass g 0 x * siteKernel g i x y = mass g 0 y * siteKernel g i y x := by
  by_cases hxy : y = x
  · subst y; rfl
  by_cases hflip : y = flip i x
  · subst y
    simp only [siteKernel, flip_ne, Ne.symm (flip_ne i x), ↓reduceIte, flip_flip,
      zero_add]
    rw [add_comm (mass g 0 (flip i x)) (mass g 0 x)]
    ring
  · have hyx : x ≠ y := Ne.symm hxy
    have hflip' : x ≠ flip i y := by
      intro h
      apply hflip
      rw [h, flip_flip]
    simp [siteKernel, hxy, hflip, hyx, hflip']

theorem siteKernel_stationary (g : Disorder n) (i : Fin n) (y : Spin n) :
    ∑ x, mass g 0 x * siteKernel g i x y = mass g 0 y := by
  simp_rw [siteKernel_balance g i _ y]
  rw [← Finset.mul_sum, sum_siteKernel, mul_one]

theorem transition_stochastic (g : Disorder n) :
    transition g ∈ Matrix.rowStochastic ℝ (Spin n) := by
  by_cases hn : n = 0
  · simp only [transition, hn, ↓reduceIte]
    exact (Matrix.rowStochastic ℝ (Spin n)).one_mem
  · rw [Matrix.mem_rowStochastic_iff_sum]
    simp only [transition, hn, ↓reduceIte]
    constructor
    · intro x y
      exact div_nonneg (Finset.sum_nonneg (fun i _ => siteKernel_nonneg g i x y))
        (Nat.cast_nonneg n)
    · intro x
      rw [← Finset.sum_div, Finset.sum_comm]
      simp [Nat.cast_ne_zero.mpr hn]

theorem transition_nonneg (g : Disorder n) (x y : Spin n) :
    0 ≤ transition g x y := (transition_stochastic g).1 x y

theorem transition_stationary (g : Disorder n) :
    (mass g 0) ᵥ* transition g = mass g 0 := by
  by_cases hn : n = 0
  · simp [transition, hn]
  · ext y
    simp only [Matrix.vecMul, dotProduct, transition, hn, ↓reduceIte,
      mul_div, ← Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [siteKernel_stationary, Nat.cast_ne_zero.mpr hn]

theorem transition_pow_stochastic (g : Disorder n) (k : ℕ) :
    transition g ^ k ∈ Matrix.rowStochastic ℝ (Spin n) :=
  (Matrix.rowStochastic ℝ (Spin n)).pow_mem (transition_stochastic g) k

theorem transition_pow_stationary (g : Disorder n) (k : ℕ) :
    (mass g 0) ᵥ* (transition g ^ k) = mass g 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, transition_stationary]

theorem siteKernel_update_pos (g : Disorder n) (i : Fin n) (x : Spin n) (b : Bool) :
    0 < siteKernel g i x (Function.update x i b) := by
  by_cases hb : b = x i
  · subst b
    simp only [Function.update_eq_self, siteKernel, Ne.symm (flip_ne i x),
      ↓reduceIte, add_zero]
    exact div_pos (mass_pos g 0 x) (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x)))
  · have hb' : b = !(x i) := by cases b <;> cases h : x i <;> simp_all
    subst b
    change 0 < siteKernel g i x (flip i x)
    simp only [siteKernel, flip_ne, ↓reduceIte, zero_add]
    exact div_pos (mass_pos g 0 (flip i x))
      (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x)))

theorem transition_update_pos (g : Disorder n) (i : Fin n) (x : Spin n) (b : Bool) :
    0 < transition g x (Function.update x i b) := by
  have hn : n ≠ 0 := ne_of_gt (Nat.zero_lt_of_lt i.isLt)
  simp only [transition, hn, ↓reduceIte]
  apply div_pos _ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  exact (siteKernel_update_pos g i x b).trans_le
    (Finset.single_le_sum (fun j _ => siteKernel_nonneg g j x _) (Finset.mem_univ i))

def updatePath (x y : Spin n) (k : ℕ) : Spin n :=
  fun i => if (i : ℕ) < k then y i else x i

@[simp] theorem updatePath_zero (x y : Spin n) : updatePath x y 0 = x := by
  ext i; simp [updatePath]

@[simp] theorem updatePath_end (x y : Spin n) : updatePath x y n = y := by
  ext i; simp [updatePath]

theorem updatePath_succ (x y : Spin n) (k : ℕ) (hk : k < n) :
    updatePath x y (k + 1) =
      Function.update (updatePath x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  ext i
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    simp [updatePath]
  · have hval : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
    have hlt : (i : ℕ) < k + 1 ↔ (i : ℕ) < k := by omega
    simp [Function.update_of_ne hi, updatePath, hlt]

theorem transition_n_pos (g : Disorder n) (x y : Spin n) :
    0 < (transition g ^ n) x y := by
  have path_pos (k : ℕ) (hk : k ≤ n) :
      0 < (transition g ^ k) x (updatePath x y k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k < n := by omega
      have hprev := ih (by omega)
      rw [pow_succ, Matrix.mul_apply]
      have hlast : 0 < transition g (updatePath x y k) (updatePath x y (k + 1)) := by
        rw [updatePath_succ x y k hkn]
        exact transition_update_pos g ⟨k, hkn⟩ _ _
      exact (mul_pos hprev hlast).trans_le
        (Finset.single_le_sum
          (fun z _ => mul_nonneg ((transition_pow_stochastic g k).1 x z)
            (transition_nonneg g z _)) (Finset.mem_univ _))
  simpa using path_pos n le_rfl

end HeatBath

section FiniteTV
variable {α : Type*} [Fintype α]

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  positivity

theorem totalVariation_le_one (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    totalVariation p q ≤ 1 := by
  calc
    totalVariation p q ≤ (1 / 2 : ℝ) * ∑ x, (p x + q x) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => ?_)) (by norm_num)
      simpa [abs_of_nonneg (hp x), abs_of_nonneg (hq x)] using abs_sub (p x) (q x)
    _ = 1 := by rw [Finset.sum_add_distrib, hp1, hq1]; norm_num

variable [DecidableEq α]

theorem totalVariation_dirac (q : α → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) (x : α) :
    totalVariation ((1 : Matrix α α ℝ) x) q = 1 - q x := by
  have hqx : q x ≤ 1 := by
    rw [← hq1]
    exact Finset.single_le_sum (fun y _ => hq y) (Finset.mem_univ x)
  have summand (y : α) :
      |(1 : Matrix α α ℝ) x y - q y| = q y + if y = x then 1 - 2 * q x else 0 := by
    by_cases h : y = x
    · subst y
      simp only [Matrix.one_apply_eq, ↓reduceIte, abs_of_nonneg (sub_nonneg.mpr hqx)]
      ring
    · simp [Matrix.one_apply_ne (Ne.symm h), h, abs_of_nonneg (hq y)]
  simp only [totalVariation, summand, Finset.sum_add_distrib, hq1,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

theorem totalVariation_minorization (A : Matrix α α ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ α) (p q : α → ℝ)
    (hpq : ∑ x, p x = ∑ x, q x) (c : ℝ) (hc : ∀ x y, c ≤ A x y) :
    totalVariation (p ᵥ* A) (q ᵥ* A) ≤
      (1 - (Fintype.card α : ℝ) * c) * totalVariation p q := by
  have hdiff (y : α) : (p ᵥ* A) y - (q ᵥ* A) y =
      ∑ x, (p x - q x) * (A x y - c) := by
    simp only [Matrix.vecMul, dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hpq]
    ring
  have hrow (x : α) : ∑ y, (A x y - c) = 1 - (Fintype.card α : ℝ) * c := by
    simp only [Finset.sum_sub_distrib, Matrix.sum_row_of_mem_rowStochastic hA,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have habs (y : α) : |(p ᵥ* A) y - (q ᵥ* A) y| ≤
      ∑ x, |p x - q x| * (A x y - c) := by
    rw [hdiff]
    calc
      |∑ x, (p x - q x) * (A x y - c)| ≤ ∑ x, |(p x - q x) * (A x y - c)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_congr rfl (fun x _ => by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hc x y))])
  calc
    totalVariation (p ᵥ* A) (q ᵥ* A) ≤
        (1 / 2 : ℝ) * ∑ y, ∑ x, |p x - q x| * (A x y - c) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => habs y)) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ x,
        |p x - q x| * (1 - (Fintype.card α : ℝ) * c) := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hrow]
    _ = (1 - (Fintype.card α : ℝ) * c) * totalVariation p q := by
      rw [← Finset.sum_mul]
      unfold totalVariation
      ring

theorem totalVariation_contract (A : Matrix α α ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ α) (p q : α → ℝ)
    (hpq : ∑ x, p x = ∑ x, q x) :
    totalVariation (p ᵥ* A) (q ᵥ* A) ≤ totalVariation p q := by
  simpa using totalVariation_minorization A hA p q hpq 0 hA.1

theorem exists_geometric_block_bound [Nonempty α] (A : Matrix α α ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ α) (π : α → ℝ)
    (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (m : ℕ) (hm : ∀ x y, 0 < (A ^ m) x y) (hstation : π ᵥ* (A ^ m) = π) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ k : ℕ, ∀ x, totalVariation ((A ^ (m * k)) x) π ≤ r ^ k := by
  classical
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun xy : α × α => (A ^ m) xy.1 xy.2)
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr (fun xy _ => hm xy.1 xy.2)
  have hcA (x y : α) : c ≤ (A ^ m) x y :=
    Finset.inf'_le _ (Finset.mem_univ (x, y))
  have hAm := (Matrix.rowStochastic ℝ α).pow_mem hA m
  let r : ℝ := 1 - (Fintype.card α : ℝ) * c
  have hr0 : 0 ≤ r := by
    have H : (Fintype.card α : ℝ) * c ≤ 1 := by
      calc
        (Fintype.card α : ℝ) * c = ∑ _y : α, c := by simp
        _ ≤ ∑ y, (A ^ m) (Classical.arbitrary α) y := Finset.sum_le_sum (fun y _ => hcA _ y)
        _ = 1 := Matrix.sum_row_of_mem_rowStochastic hAm _
    exact sub_nonneg.mpr H
  have hr1 : r < 1 := by
    have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    dsimp [r]
    linarith [mul_pos hcard hc]
  refine ⟨r, hr0, hr1, ?_⟩
  intro k
  induction k with
  | zero =>
    intro x
    simp only [Nat.mul_zero, pow_zero]
    have hI := (Matrix.rowStochastic ℝ α).one_mem
    exact totalVariation_le_one _ _ (hI.1 x) hπ
      (Matrix.sum_row_of_mem_rowStochastic hI x) hπ1
  | succ k ih =>
    intro x
    rw [Nat.mul_succ, pow_add, Matrix.mul_apply_eq_vecMul]
    have hAk := (Matrix.rowStochastic ℝ α).pow_mem hA (m * k)
    have hequal : (∑ y, (A ^ (m * k)) x y) = ∑ y, π y := by
      rw [Matrix.sum_row_of_mem_rowStochastic hAk, hπ1]
    calc
      totalVariation ((A ^ (m * k)) x ᵥ* (A ^ m)) π =
          totalVariation ((A ^ (m * k)) x ᵥ* (A ^ m)) (π ᵥ* (A ^ m)) := by rw [hstation]
      _ ≤ r * totalVariation ((A ^ (m * k)) x) π :=
        totalVariation_minorization (A ^ m) hAm _ _ hequal c hcA
      _ ≤ r * r ^ k := mul_le_mul_of_nonneg_left (ih x) hr0
      _ = r ^ (k + 1) := by rw [pow_succ, mul_comm]

end FiniteTV

section MixingTime
variable {n : ℕ}

theorem tv_le_discreteDistance (g : Disorder n) (k : ℕ) (x : Spin n) :
    totalVariation ((transition g ^ k) x) (mass g 0) ≤ discreteDistance g k := by
  unfold discreteDistance
  exact Finset.le_sup' (fun z : Spin n => totalVariation ((transition g ^ k) z) (mass g 0))
    (Finset.mem_univ x)

end MixingTime
end SKRatio
end
end

end OAI
