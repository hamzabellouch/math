import OAI.Analysis.MarkovType.RenormingBasic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def cutSign {n : ℕ} (r j : Fin n) : ℝ := if j < r then 1 else -1

def cutSum {n : ℕ} (x : Fin n → X) (r : Fin n) : X :=
  ∑ j, cutSign r j • x j

@[simp] theorem abs_cutSign {n : ℕ} (r j : Fin n) : |cutSign r j| = 1 := by
  unfold cutSign
  split <;> norm_num

@[simp] theorem norm_cutSign {n : ℕ} (r j : Fin n) : ‖cutSign r j‖ = 1 := by
  simpa only [Real.norm_eq_abs] using abs_cutSign r j

theorem map_cutSum {n : ℕ} (T : X →ₗ[ℝ] Y) (x : Fin n → X) (r : Fin n) :
    T (cutSum x r) = cutSum (fun j => T (x j)) r := by
  simp only [cutSum, map_sum, map_smul]

theorem cutSum_smul {n : ℕ} (a : ℝ) (x : Fin n → X) (r : Fin n) :
    cutSum (fun j => a • x j) r = a • cutSum x r := by
  unfold cutSum
  calc
    ∑ j, cutSign r j • (a • x j) = ∑ j, a • (cutSign r j • x j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact smul_comm _ _ _
    _ = a • ∑ j, cutSign r j • x j := by rw [Finset.smul_sum]

@[simp] theorem cutSum_two_zero (x : Fin 2 → X) :
    cutSum x (0 : Fin 2) = -(x 0 + x 1) := by
  simp [cutSum, Fin.sum_univ_two, cutSign]

@[simp] theorem cutSum_two_one (x : Fin 2 → X) :
    cutSum x (1 : Fin 2) = x 0 - x 1 := by
  simp [cutSum, Fin.sum_univ_two, cutSign, sub_eq_add_neg]

def JConvexWitness (p : Seminorm ℝ X) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ x : Fin n → X, (∀ j, p (x j) ≤ 1) →
    ∃ r : Fin n, p (cutSum x r) ≤ (n : ℝ) * (1 - δ)

def JConvex (p : Seminorm ℝ X) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ JConvexWitness p n δ

def UniformlyNonsquare (p : Seminorm ℝ X) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ x y : X, p x ≤ 1 → p y ≤ 1 →
      p (x + y) ≤ 2 * (1 - δ) ∨ p (x - y) ≤ 2 * (1 - δ)

def AmbientJConvex (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  JConvex (normSeminorm ℝ X)

theorem JConvexWitness.shrink_delta {p : Seminorm ℝ X} {n : ℕ} {δ ε : ℝ}
    (h : JConvexWitness p n δ) (hεδ : ε ≤ δ) : JConvexWitness p n ε := by
  intro x hx
  obtain ⟨r, hr⟩ := h x hx
  refine ⟨r, hr.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hεδ 1) (Nat.cast_nonneg n)

theorem JConvexWitness.comp {p : Seminorm ℝ Y} {n : ℕ} {δ : ℝ}
    (h : JConvexWitness p n δ) (T : X →ₗ[ℝ] Y) :
    JConvexWitness (p.comp T) n δ := by
  intro x hx
  obtain ⟨r, hr⟩ := h (fun j => T (x j)) hx
  refine ⟨r, ?_⟩
  simpa only [Seminorm.comp_apply, map_cutSum] using hr

theorem JConvex.comp {p : Seminorm ℝ Y} (h : JConvex p) (T : X →ₗ[ℝ] Y) :
    JConvex (p.comp T) := by
  obtain ⟨n, hn, δ, hδ, hδ1, hw⟩ := h
  exact ⟨n, hn, δ, hδ, hδ1, hw.comp T⟩

theorem JConvexWitness.transport {p : Seminorm ℝ X} {q : Seminorm ℝ Y}
    {n : ℕ} {δ ε c : ℝ} (h : JConvexWitness q n δ)
    (T : X →ₗ[ℝ] Y) (hc : 0 ≤ c)
    (hforward : ∀ x, q (T x) ≤ p x)
    (hbackward : ∀ x, p x ≤ c * q (T x))
    (hgap : c * (1 - δ) ≤ 1 - ε) : JConvexWitness p n ε := by
  intro x hx
  have hTx : ∀ j, q (T (x j)) ≤ 1 := fun j => (hforward _).trans (hx j)
  obtain ⟨r, hr⟩ := h (fun j => T (x j)) hTx
  refine ⟨r, ?_⟩
  calc
    p (cutSum x r) ≤ c * q (T (cutSum x r)) := hbackward _
    _ = c * q (cutSum (fun j => T (x j)) r) := by rw [map_cutSum]
    _ ≤ c * ((n : ℝ) * (1 - δ)) := mul_le_mul_of_nonneg_left hr hc
    _ = (n : ℝ) * (c * (1 - δ)) := by ring
    _ ≤ (n : ℝ) * (1 - ε) := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n)

theorem jConvexWitness_two_iff (p : Seminorm ℝ X) (δ : ℝ) :
    JConvexWitness p 2 δ ↔
      ∀ x y : X, p x ≤ 1 → p y ≤ 1 →
        p (x + y) ≤ 2 * (1 - δ) ∨ p (x - y) ≤ 2 * (1 - δ) := by
  constructor
  · intro h x y hx hy
    let z : Fin 2 → X := fun j => if j = 0 then x else y
    have hz : ∀ j, p (z j) ≤ 1 := by
      intro j
      fin_cases j
      · simpa [z] using hx
      · simpa [z] using hy
    obtain ⟨r, hr⟩ := h z hz
    fin_cases r
    · change p (cutSum z (0 : Fin 2)) ≤ (2 : ℝ) * (1 - δ) at hr
      rw [cutSum_two_zero, map_neg_eq_map] at hr
      exact Or.inl (by simpa [z] using hr)
    · exact Or.inr (by simpa [z] using hr)
  · intro h x hx
    rcases h (x 0) (x 1) (hx 0) (hx 1) with hsum | hdiff
    · exact ⟨0, by simpa only [cutSum_two_zero, map_neg_eq_map, Nat.cast_ofNat] using hsum⟩
    · exact ⟨1, by simpa only [cutSum_two_one, Nat.cast_ofNat] using hdiff⟩

theorem UniformlyNonsquare.jConvex {p : Seminorm ℝ X} (h : UniformlyNonsquare p) :
    JConvex p := by
  obtain ⟨δ, hδ, hδ1, hw⟩ := h
  exact ⟨2, by decide, δ, hδ, hδ1, (jConvexWitness_two_iff p δ).mpr hw⟩

theorem UniformConvex.uniformlyNonsquare {p : Seminorm ℝ X} (h : UniformConvex p) :
    UniformlyNonsquare p := by
  obtain ⟨η, hη, hdrop⟩ := h 1 (by norm_num) (by norm_num)
  let δ : ℝ := min η (1 / 2)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  refine ⟨δ, hδ, lt_of_le_of_lt hδhalf (by norm_num), ?_⟩
  intro x y hx hy
  by_cases hsep : 1 ≤ p (x - y)
  · left
    have hm := hdrop x y hx hy hsep
    have hmid : p ((1 / 2 : ℝ) • (x + y)) = (1 / 2 : ℝ) * p (x + y) := by
      rw [map_smul_eq_mul]
      norm_num
    rw [hmid] at hm
    linarith
  · right
    have hlt : p (x - y) < 1 := lt_of_not_ge hsep
    linarith

theorem UniformConvex.jConvex {p : Seminorm ℝ X} (h : UniformConvex p) : JConvex p :=
  h.uniformlyNonsquare.jConvex

theorem jConvex_of_subsingleton [Subsingleton X] (p : Seminorm ℝ X) : JConvex p :=
  (uniformConvex_of_subsingleton p).jConvex

end MarkovSuperreflexivity

end OAI
