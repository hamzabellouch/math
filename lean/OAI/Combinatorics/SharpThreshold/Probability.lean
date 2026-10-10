import OAI.Combinatorics.SharpThreshold.Model

namespace OAI

noncomputable section
namespace Problem313

@[simp] theorem boolReal_nonneg (b : Bool) : 0 ≤ boolReal b := by
  cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_le_one (b : Bool) : boolReal b ≤ 1 := by
  cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sq (b : Bool) : boolReal b ^ 2 = boolReal b := by
  cases b <;> norm_num [boolReal]

theorem graphWeight_sum {n : ℕ} (p : ℝ) :
    (∑ x : GraphConfig n, graphWeight p x) = 1 := by
  classical
  unfold graphWeight
  rw [← Fintype.prod_sum (fun (_ : GraphEdge n) (b : Bool) => if b = true then p else 1 - p)]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  simp

theorem graphWeight_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : GraphConfig n) : 0 ≤ graphWeight p x := by
  classical
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

theorem graphWeight_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x : GraphConfig n) : 0 < graphWeight p x := by
  classical
  apply Finset.prod_pos
  intro e he
  split_ifs <;> linarith

theorem graphMean_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : 0 ≤ graphMean p f := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (graphWeight_nonneg hp hp1 x) (boolReal_nonneg (f x))

theorem graphMean_le_one {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : graphMean p f ≤ 1 := by
  classical
  calc
    graphMean p f ≤ ∑ x : GraphConfig n, graphWeight p x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_of_le_one_right (graphWeight_nonneg hp hp1 x) (boolReal_le_one (f x))
    _ = 1 := graphWeight_sum p

theorem graphMean_mem_Icc {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : graphMean p f ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨graphMean_nonneg hp hp1 f, graphMean_le_one hp hp1 f⟩

theorem graphVariance_eq_mean_mul {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphVariance p f = graphMean p f * (1 - graphMean p f) := by
  classical
  let m := graphMean p f
  change (∑ x : GraphConfig n, graphWeight p x * (boolReal (f x) - m) ^ 2) = m * (1 - m)
  calc
    (∑ x : GraphConfig n, graphWeight p x * (boolReal (f x) - m) ^ 2) =
        ∑ x : GraphConfig n,
          ((1 - 2 * m) * (graphWeight p x * boolReal (f x)) + m ^ 2 * graphWeight p x) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [sub_sq, mul_add, mul_sub, boolReal_sq]
      ring
    _ = (1 - 2 * m) * m + m ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, graphWeight_sum, mul_one]
      rfl
    _ = m * (1 - m) := by ring

@[simp] theorem boolReal_not (b : Bool) : boolReal (!b) = 1 - boolReal b := by
  cases b <;> norm_num [boolReal]

theorem graphMean_not {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphMean p (fun x => !(f x)) = 1 - graphMean p f := by
  classical
  simp only [graphMean, boolReal_not, mul_sub, mul_one, Finset.sum_sub_distrib,
    graphWeight_sum]

theorem graphMean_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : ∃ x, f x = true) : 0 < graphMean p f := by
  classical
  obtain ⟨x, hx⟩ := hf
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (graphWeight_nonneg hp.le hp1.le y) (boolReal_nonneg (f y))
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simpa [hx, boolReal] using graphWeight_pos hp hp1 x

theorem graphMean_lt_one {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : ∃ x, f x = false) : graphMean p f < 1 := by
  obtain ⟨x, hx⟩ := hf
  have ht : ∃ x, (!(f x)) = true := ⟨x, by simp [hx]⟩
  have h := graphMean_pos hp hp1 ht
  rw [graphMean_not] at h
  linarith

theorem graphMean_mem_Ioo {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : NontrivialGraphProperty f) :
    graphMean p f ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨graphMean_pos hp hp1 hf.1, graphMean_lt_one hp hp1 hf.2⟩

theorem graphVariance_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : 0 ≤ graphVariance p f := by
  rw [graphVariance_eq_mean_mul]
  exact mul_nonneg (graphMean_nonneg hp hp1 f) (sub_nonneg.mpr (graphMean_le_one hp hp1 f))

theorem graphVariance_le_quarter {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphVariance p f ≤ 1 / 4 := by
  rw [graphVariance_eq_mean_mul]
  nlinarith [sq_nonneg (graphMean p f - 1 / 2)]

theorem edgeInfluence_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) (e : GraphEdge n) : 0 ≤ edgeInfluence p f e := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact graphWeight_nonneg hp hp1 x
  · exact le_rfl

theorem totalInfluence_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : 0 ≤ totalInfluence p f := by
  classical
  apply Finset.sum_nonneg
  intro e he
  exact edgeInfluence_nonneg hp hp1 f e

end Problem313

end

end OAI
