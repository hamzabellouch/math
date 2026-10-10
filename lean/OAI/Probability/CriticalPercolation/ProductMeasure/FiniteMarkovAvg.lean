import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteMarkov
variable {X : Type*} [Fintype X]

noncomputable def avg (μ : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, μ x * f x

noncomputable def step (K : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ := avg (K x) f

lemma avg_const (μ : X → ℝ) (c : ℝ) : avg μ (fun _ => c) = (∑ x, μ x) * c := by
  classical
  exact (Finset.sum_mul _ _ _).symm

lemma avg_mono {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) {f g : X → ℝ}
    (h : ∀ x, f x ≤ g x) : avg μ f ≤ avg μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x)

lemma avg_stationary (K : X → X → ℝ) (μ : X → ℝ)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) :
    avg μ (step K f) = avg μ f := by
  classical
  simp only [step, avg]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hstat]

lemma avg_iterate (K : X → X → ℝ) (μ : X → ℝ)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) (n : ℕ) :
    avg μ ((step K)^[n] f) = avg μ f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', avg_stationary K μ hstat, ih]

noncomputable def remainder (K : X → X → ℝ) (a : ℝ) (z x y : X) : ℝ := by
  classical
  exact K x y - if y = z then a else 0

omit [Fintype X] in
lemma remainder_nonneg {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    {a : ℝ} {z : X} (haK : ∀ x, a ≤ K x z) (x y : X) :
    0 ≤ remainder K a z x y := by
  classical
  unfold remainder
  split_ifs with h
  · subst y
    exact sub_nonneg.mpr (haK x)
  · simpa using hK x y

lemma remainder_mass (K : X → X → ℝ) (hK : ∀ x, ∑ y, K x y = 1)
    (a : ℝ) (z x : X) : ∑ y, remainder K a z x y = 1 - a := by
  classical
  simp [remainder, Finset.sum_sub_distrib, hK]

lemma step_remainder (K : X → X → ℝ) (a : ℝ) (z : X) (f : X → ℝ) (x : X) :
    step K f x = a * f z + avg (remainder K a z x) f := by
  classical
  simp [step, avg, remainder, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma step_bounds {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) {f : X → ℝ} {l u : ℝ}
    (hf : ∀ x, l ≤ f x ∧ f x ≤ u) (x : X) :
    a * f z + (1 - a) * l ≤ step K f x ∧
      step K f x ≤ a * f z + (1 - a) * u := by
  rw [step_remainder K a z]
  have hlo := avg_mono (remainder_nonneg hK haK x) (fun x => (hf x).1)
  have hup := avg_mono (remainder_nonneg hK haK x) (fun x => (hf x).2)
  rw [avg_const, remainder_mass K hmass] at hlo
  rw [avg_const, remainder_mass K hmass] at hup
  constructor <;> linarith

lemma iterate_bounds {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) {f : X → ℝ} {l u : ℝ}
    (hf : ∀ x, l ≤ f x ∧ f x ≤ u) (n : ℕ) :
    ∃ l' u', (∀ x, l' ≤ (step K)^[n] f x ∧ (step K)^[n] f x ≤ u') ∧
      u' - l' = (1 - a)^n * (u-l) := by
  induction n with
  | zero => exact ⟨l, u, hf, by simp⟩
  | succ n ih =>
      obtain ⟨l', u', hb, hd⟩ := ih
      refine ⟨a * (step K)^[n] f z + (1-a)*l',
        a * (step K)^[n] f z + (1-a)*u', ?_, ?_⟩
      · intro x
        simpa only [Function.iterate_succ_apply'] using step_bounds hK hmass haK hb x
      · calc
          _ = (1-a) * (u'-l') := by ring
          _ = _ := by rw [hd, pow_succ]; ring

lemma iterate_distance {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) (μ : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y)
    {f : X → ℝ} {l u : ℝ} (hf : ∀ x, l ≤ f x ∧ f x ≤ u)
    (n : ℕ) (x : X) :
    |(step K)^[n] f x - avg μ f| ≤ (1-a)^n * (u-l) := by
  obtain ⟨l', u', hb, hd⟩ := iterate_bounds hK hmass haK hf n
  have hlo := avg_mono hμ (fun x => (hb x).1)
  have hup := avg_mono hμ (fun x => (hb x).2)
  rw [avg_const, hμmass, one_mul, avg_iterate K μ hstat] at hlo
  rw [avg_const, hμmass, one_mul, avg_iterate K μ hstat] at hup
  rw [← hd, abs_le]
  have := hb x
  constructor <;> linarith

lemma tendsto_iterate {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (ha : 0 < a) (ha_one : a ≤ 1) (haK : ∀ x, a ≤ K x z)
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) (x : X) :
    Filter.Tendsto (fun n => (step K)^[n] f x) Filter.atTop (nhds (avg μ f)) := by
  classical
  let : Nonempty X := ⟨z⟩
  let l := Finset.univ.inf' Finset.univ_nonempty f
  let u := Finset.univ.sup' Finset.univ_nonempty f
  have hb : ∀ y, l ≤ f y ∧ f y ≤ u := by
    intro y
    exact ⟨Finset.inf'_le _ (Finset.mem_univ y), Finset.le_sup' _ (Finset.mem_univ y)⟩
  have hpow : Filter.Tendsto (fun n : ℕ => (1-a)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ha_one) (by linarith)
  have hlim := hpow.mul_const (u-l)
  simp only [zero_mul] at hlim
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := (Metric.tendsto_atTop.mp hlim) ε hε
  obtain ⟨N, hN⟩ := he
  refine ⟨N, fun n hn => ?_⟩
  have hlt := hN n hn
  rw [Real.dist_eq, sub_zero] at hlt
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (iterate_distance hK hmass haK μ hμ hμmass hstat hb n x)
    (lt_of_le_of_lt (le_abs_self _) hlt)

end CriticalPercolation.FiniteMarkov

end
end

end OAI
