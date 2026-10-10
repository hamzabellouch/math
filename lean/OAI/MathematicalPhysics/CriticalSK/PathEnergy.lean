import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

namespace CriticalSK

def edgeCoeff (n i : ℕ) : ℝ := Real.sqrt (1 - (i + 1 : ℝ) / (n + 1))

def pathEnergy (n : ℕ) (u : ℕ → ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1), u i ^ 2 -
    2 * ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i + 1)

lemma path_energy_identity (n : ℕ) (c u : ℕ → ℝ) (hc : c n = 0) :
    2 * (∑ i ∈ Finset.range (n + 1), u i ^ 2) -
      2 * (∑ i ∈ Finset.range n, c i * u i * u (i + 1)) =
    (∑ i ∈ Finset.range n, c i * (u (i + 1) - u i) ^ 2) +
      ∑ i ∈ Finset.range (n + 1),
        (2 - c i - if i = 0 then 0 else c (i - 1)) * u i ^ 2 := by
  have hl : (∑ i ∈ Finset.range (n + 1),
      (if i = 0 then (0 : ℝ) else c (i - 1)) * u i ^ 2) =
      ∑ i ∈ Finset.range n, c i * u (i + 1) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp
  have hr : (∑ i ∈ Finset.range (n + 1), c i * u i ^ 2) =
      ∑ i ∈ Finset.range n, c i * u i ^ 2 := by
    rw [Finset.sum_range_succ, hc, zero_mul, add_zero]
  have hg : (∑ i ∈ Finset.range n, c i * (u (i + 1) - u i) ^ 2) =
      (∑ i ∈ Finset.range n, c i * u i ^ 2) +
      (∑ i ∈ Finset.range n, c i * u (i + 1) ^ 2) -
      2 * ∑ i ∈ Finset.range n, c i * u i * u (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hl, hr, hg]
  ring

lemma edgeCoeff_nonneg (n i : ℕ) : 0 ≤ edgeCoeff n i := Real.sqrt_nonneg _

lemma edgeCoeff_last (n : ℕ) : edgeCoeff n n = 0 := by
  simp [edgeCoeff, show (n + 1 : ℝ) ≠ 0 by positivity]

lemma edgeCoeff_upper (n i : ℕ) (hi : i ≤ n) :
    edgeCoeff n i ≤ 1 - (i + 1 : ℝ) / (2 * (n + 1)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hit : (i + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hi
  have ht : 0 ≤ (i + 1 : ℝ) / (n + 1) := by positivity
  have ht1 : (i + 1 : ℝ) / (n + 1) ≤ 1 := (div_le_one hn).mpr hit
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - (i + 1 : ℝ) / (n + 1))
  have hd : (i + 1 : ℝ) / (2 * (n + 1)) = ((i + 1 : ℝ) / (n + 1)) / 2 := by rw [div_div]; ring
  dsimp [edgeCoeff]
  rw [hd]
  nlinarith [Real.sqrt_nonneg (1 - (i + 1 : ℝ) / (n + 1)),
    sq_nonneg ((i + 1 : ℝ) / (n + 1))]

lemma edgeCoeff_le_one (n i : ℕ) (hi : i ≤ n) : edgeCoeff n i ≤ 1 :=
  (edgeCoeff_upper n i hi).trans (sub_le_self _ (by positivity))

lemma edge_deficit (n i : ℕ) (hi : i ≤ n) :
    (i + 1 : ℝ) / (2 * (n + 1)) ≤
      2 - edgeCoeff n i - if i = 0 then 0 else edgeCoeff n (i - 1) := by
  have h := edgeCoeff_upper n i hi
  split_ifs with hi0
  · linarith
  · have hprev := edgeCoeff_le_one n (i - 1) (by omega)
    linarith

lemma pathEnergy_expansion (n : ℕ) (u : ℕ → ℝ) :
    pathEnergy n u =
      (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      ∑ i ∈ Finset.range (n + 1),
        (2 - edgeCoeff n i - if i = 0 then 0 else edgeCoeff n (i - 1)) * u i ^ 2 :=
  path_energy_identity n (edgeCoeff n) u (edgeCoeff_last n)

lemma pathEnergy_controls (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2) ≤
      pathEnergy n u := by
  rw [pathEnergy_expansion]
  gcongr with i hi
  exact edge_deficit n i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma pathEnergy_nonneg (n : ℕ) (u : ℕ → ℝ) : 0 ≤ pathEnergy n u :=
  (by
    unfold edgeCoeff
    positivity : 0 ≤
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2)).trans
        (pathEnergy_controls n u)

lemma pathEnergy_weighted_mass (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2) ≤
      2 * pathEnergy n u := by
  have h := pathEnergy_controls n u
  have hg : 0 ≤ ∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2 := by
    unfold edgeCoeff
    positivity
  have hs : (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2) =
      2 * ∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [hs]
  linarith

lemma pathEnergy_weighted_gradient (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) ≤
      pathEnergy n u := by
  have h := pathEnergy_controls n u
  have hp : 0 ≤ ∑ i ∈ Finset.range (n + 1),
      (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2 := by positivity
  linarith

lemma pathEnergy_tail (n : ℕ) (u : ℕ → ℝ) (s : Finset ℕ)
    (hs : s ⊆ Finset.range (n + 1)) (r : ℝ)
    (hr : ∀ i ∈ s, r ≤ (i + 1 : ℝ) / (n + 1)) :
    r * (∑ i ∈ s, u i ^ 2) ≤ 2 * pathEnergy n u := by
  calc
    _ = ∑ i ∈ s, r * u i ^ 2 := Finset.mul_sum ..
    _ ≤ ∑ i ∈ s, (i + 1 : ℝ) / (n + 1) * u i ^ 2 := by
      gcongr with i hi
      exact hr i hi
    _ ≤ ∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intros
      positivity
    _ ≤ _ := pathEnergy_weighted_mass n u

lemma edgeCoeff_lower_half (n i : ℕ) (hi : 2 * (i + 1) ≤ n + 1) :
    1 / 2 ≤ edgeCoeff n i := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hi' : 2 * (i + 1 : ℝ) ≤ n + 1 := by exact_mod_cast hi
  have ht : (i + 1 : ℝ) / (n + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - (i + 1 : ℝ) / (n + 1))
  have hp := edgeCoeff_nonneg n i
  dsimp [edgeCoeff] at *
  nlinarith

lemma edge_gradient_control (n i : ℕ) (u : ℕ → ℝ) :
    (u (i + 1) - u i) ^ 2 ≤
      2 * edgeCoeff n i * (u (i + 1) - u i) ^ 2 +
      4 * ((i + 1 : ℝ) / (n + 1) * u i ^ 2 +
        (i + 2 : ℝ) / (n + 1) * u (i + 1) ^ 2) := by
  by_cases hi : 2 * (i + 1) ≤ n + 1
  · have hc := edgeCoeff_lower_half n i hi
    have hm : 0 ≤ (i + 1 : ℝ) / (n + 1) * u i ^ 2 +
        (i + 2 : ℝ) / (n + 1) * u (i + 1) ^ 2 := by positivity
    nlinarith [sq_nonneg (u (i + 1) - u i)]
  · have hi' : (n + 1 : ℝ) ≤ 2 * (i + 1) := by exact_mod_cast (by omega : n + 1 ≤ 2 * (i + 1))
    have hn : (0 : ℝ) < n + 1 := by positivity
    have h1 : 1 / 2 ≤ (i + 1 : ℝ) / (n + 1) := by
      apply (le_div_iff₀ hn).mpr
      linarith
    have h2 : 1 / 2 ≤ (i + 2 : ℝ) / (n + 1) := by
      apply (le_div_iff₀ hn).mpr
      linarith
    have hm1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (u i))
    have hm2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (u (i + 1)))
    have hg : 0 ≤ edgeCoeff n i * (u (i + 1) - u i) ^ 2 :=
      mul_nonneg (edgeCoeff_nonneg n i) (sq_nonneg _)
    nlinarith [sq_nonneg (u i + u (i + 1))]

lemma pathEnergy_gradient (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (u (i + 1) - u i) ^ 2) ≤ 18 * pathEnergy n u := by
  let mass : ℕ → ℝ := fun i => (i + 1 : ℝ) / (n + 1) * u i ^ 2
  have hm0 : ∀ i, 0 ≤ mass i := by intro i; dsimp [mass]; positivity
  have hm1 : (∑ i ∈ Finset.range n, mass i) ≤ ∑ i ∈ Finset.range (n + 1), mass i := by
    rw [Finset.sum_range_succ]
    linarith [hm0 n]
  have hm2 : (∑ i ∈ Finset.range n, mass (i + 1)) ≤ ∑ i ∈ Finset.range (n + 1), mass i := by
    rw [Finset.sum_range_succ']
    linarith [hm0 0]
  have hm := pathEnergy_weighted_mass n u
  change (∑ i ∈ Finset.range (n + 1), mass i) ≤ _ at hm
  have hg := pathEnergy_weighted_gradient n u
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (2 * edgeCoeff n i * (u (i + 1) - u i) ^ 2 + 4 * (mass i + mass (i + 1))) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [mass, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using edge_gradient_control n i u
    _ = 2 * (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
        4 * ((∑ i ∈ Finset.range n, mass i) + (∑ i ∈ Finset.range n, mass (i + 1))) := by
      simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by linarith

lemma square_weight_variation (s : Finset ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ s, |u (i + 1) ^ 2 - u i ^ 2|) ^ 2 ≤
      (∑ i ∈ s, (u (i + 1) - u i) ^ 2) *
        (2 * ∑ i ∈ s, (u i ^ 2 + u (i + 1) ^ 2)) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => |u (i + 1) ^ 2 - u i ^ 2|)
    (f := fun i => (u (i + 1) - u i) ^ 2)
    (g := fun i => 2 * (u i ^ 2 + u (i + 1) ^ 2))
    (fun _ _ => sq_nonneg _) (by intros; positivity) ?_
  · simpa only [← Finset.mul_sum] using h
  · intro i _
    rw [sq_abs]
    have h := sq_nonneg (u (i + 1) - u i)
    nlinarith [sq_nonneg ((u (i + 1) - u i) ^ 2)]

lemma product_weight_variation (s : Finset ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ s, |u (i + 1) * u (i + 2) - u i * u (i + 1)|) ^ 2 ≤
      (2 * ∑ i ∈ s, ((u (i + 1) - u i) ^ 2 + (u (i + 2) - u (i + 1)) ^ 2)) *
        (∑ i ∈ s, u (i + 1) ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => |u (i + 1) * u (i + 2) - u i * u (i + 1)|)
    (f := fun i => 2 * ((u (i + 1) - u i) ^ 2 + (u (i + 2) - u (i + 1)) ^ 2))
    (g := fun i => u (i + 1) ^ 2)
    (by intros; positivity) (fun _ _ => sq_nonneg _) ?_
  · simpa only [← Finset.mul_sum] using h
  · intro i _
    rw [sq_abs]
    have he : (u (i + 1) * u (i + 2) - u i * u (i + 1)) ^ 2 =
        (u (i + 2) - u i) ^ 2 * u (i + 1) ^ 2 := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [sq_nonneg (u (i + 2) - 2 * u (i + 1) + u i)]

lemma pathEnergy_le_four_mass (n : ℕ) (u : ℕ → ℝ) :
    pathEnergy n u ≤ 4 * ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
  have hm1 : (∑ i ∈ Finset.range n, u i ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
    rw [Finset.sum_range_succ]
    linarith [sq_nonneg (u n)]
  have hm2 : (∑ i ∈ Finset.range n, u (i + 1) ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
    rw [Finset.sum_range_succ']
    linarith [sq_nonneg (u 0)]
  have he : -2 * (∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i + 1)) ≤
      (∑ i ∈ Finset.range n, u i ^ 2) + (∑ i ∈ Finset.range n, u (i + 1) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hci := edgeCoeff_le_one n i (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hcn := edgeCoeff_nonneg n i
    have hprod : -2 * u i * u (i + 1) ≤ u i ^ 2 + u (i + 1) ^ 2 := by
      nlinarith [sq_nonneg (u i + u (i + 1))]
    have hmul := mul_le_mul_of_nonneg_left hprod hcn
    have hmass := mul_le_mul_of_nonneg_right hci
      (add_nonneg (sq_nonneg (u i)) (sq_nonneg (u (i + 1))))
    nlinarith
  unfold pathEnergy
  linarith

end CriticalSK

end

end OAI
