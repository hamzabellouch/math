import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Rounding convention: half-integers are rounded upwards. -/
def nearestInteger (t : ℝ) : ℤ := ⌊t + 1 / 2⌋

lemma nearestInteger_mono : Monotone nearestInteger := by
  intro a b hab
  exact Int.floor_mono (by linarith)

lemma nearestInteger_error (t : ℝ) : |(nearestInteger t : ℝ) - t| ≤ 1 / 2 := by
  have h₁ := Int.floor_le (t + 1 / 2)
  have h₂ := Int.lt_floor_add_one (t + 1 / 2)
  unfold nearestInteger
  rw [abs_le]
  constructor <;> linarith

/-- An integer version of the monotone fixed-point argument. The bounded drift
with slope strictly less than one supplies both end barriers. -/
lemma integer_fixed_point_of_bounded_drift (F : ℤ → ℤ) (hF : Monotone F)
    (q B : ℝ) (hq : q < 1) (hB : ∀ i : ℤ, |(F i : ℝ) - q * i| ≤ B) :
    ∃ i : ℤ, F i = i := by
  have hq' : 0 < 1 - q := sub_pos.mpr hq
  obtain ⟨lo, hlo⟩ := exists_int_le (-B / (1 - q))
  obtain ⟨hi, hhi⟩ := exists_int_ge (B / (1 - q))
  have hbound : ∀ i : ℤ, F i ≤ i → lo ≤ i := by
    intro i hi
    have hb := (abs_le.mp (hB i)).1
    have hi' : (F i : ℝ) ≤ i := by exact_mod_cast hi
    have hreal : -B / (1 - q) ≤ (i : ℝ) := by
      apply (div_le_iff₀ hq').2
      nlinarith
    exact_mod_cast hlo.trans hreal
  have hhi' : F hi ≤ hi := by
    have hb := (abs_le.mp (hB hi)).2
    have ht := (div_le_iff₀ hq').1 hhi
    have : (F hi : ℝ) ≤ hi := by nlinarith
    exact_mod_cast this
  obtain ⟨i, hi, hmin⟩ := Int.exists_least_of_bdd ⟨lo, hbound⟩ ⟨hi, hhi'⟩
  exact ⟨i, le_antisymm hi (hmin (F i) (hF hi))⟩

/-- A useful strengthening of the lattice estimates: only the product
conditions are needed; either off-diagonal entry may be arbitrarily large. -/
theorem asymmetric_lattice_cover (alpha beta : ℝ)
    (hprod : 0 ≤ alpha * beta) (hprod' : alpha * beta < 1) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + alpha * j)| ≤ 1 / 2 ∧
      |u₂ - (beta * i + (j : ℝ))| ≤ 1 / 2 := by
  let F : ℤ → ℤ := fun i => nearestInteger
    (u₁ - alpha * (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ))
  have hmono : Monotone F := by
    intro i j hij
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    rcases mul_nonneg_iff.mp hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hinner : nearestInteger (u₂ - beta * (j : ℝ)) ≤
          nearestInteger (u₂ - beta * (i : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
    · have hinner : nearestInteger (u₂ - beta * (i : ℝ)) ≤
          nearestInteger (u₂ - beta * (j : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
  have hdrift : ∀ i : ℤ,
      |(F i : ℝ) - (alpha * beta) * i| ≤
        1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
    intro i
    let j := nearestInteger (u₂ - beta * (i : ℝ))
    have h₁ := nearestInteger_error (u₁ - alpha * (j : ℝ))
    have h₂ := nearestInteger_error (u₂ - beta * (i : ℝ))
    have hdecomp : (F i : ℝ) - (alpha * beta) * i =
        ((F i : ℝ) - (u₁ - alpha * j)) -
        alpha * ((j : ℝ) - (u₂ - beta * i)) + (u₁ - alpha * u₂) := by ring
    rw [hdecomp]
    calc
      _ ≤ |(F i : ℝ) - (u₁ - alpha * j)| +
          |alpha * ((j : ℝ) - (u₂ - beta * i))| + |u₁ - alpha * u₂| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
        rw [abs_mul]
        exact add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _))) le_rfl
  obtain ⟨i, hi⟩ := integer_fixed_point_of_bounded_drift F hmono
    (alpha * beta) _ hprod' hdrift
  let j := nearestInteger (u₂ - beta * (i : ℝ))
  refine ⟨i, j, ?_, ?_⟩
  · have h := nearestInteger_error (u₁ - alpha * (j : ℝ))
    change |(F i : ℝ) - (u₁ - alpha * (j : ℝ))| ≤ 1 / 2 at h
    rw [hi] at h
    convert h using 1
    rw [← abs_neg]
    congr 1
    ring
  · have h := nearestInteger_error (u₂ - beta * (i : ℝ))
    change |(j : ℝ) - (u₂ - beta * (i : ℝ))| ≤ 1 / 2 at h
    convert h using 1
    rw [← abs_neg]
    congr 1
    ring

lemma symmetric_lattice_distance (a x y : ℝ) (ha : |a| < 1)
    (hx : |x + a * y| ≤ 1 / 2) (hy : |y + a * x| ≤ 1 / 2) :
    max |x| |y| ≤ 1 / (2 * (1 - |a|)) := by
  have hax : |x| ≤ 1 / 2 + |a| * |y| := by
    calc
      |x| = |(x + a * y) - a * y| := by congr 1; ring
      _ ≤ |x + a * y| + |a * y| := abs_sub _ _
      _ ≤ 1 / 2 + |a| * |y| := by rw [abs_mul]; exact add_le_add hx le_rfl
  have hay : |y| ≤ 1 / 2 + |a| * |x| := by
    calc
      |y| = |(y + a * x) - a * x| := by congr 1; ring
      _ ≤ |y + a * x| + |a * x| := abs_sub _ _
      _ ≤ 1 / 2 + |a| * |x| := by rw [abs_mul]; exact add_le_add hy le_rfl
  have hm : max |x| |y| ≤ 1 / 2 + |a| * max |x| |y| := by
    apply max_le
    · exact hax.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_max_right _ _) (abs_nonneg a)))
    · exact hay.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_max_left _ _) (abs_nonneg a)))
  apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - |a|))).2
  nlinarith

/-- Lattice covering with a uniform distance estimate. -/
theorem lattice_covering (a : ℝ) (ha : |a| < 1) (z₁ z₂ : ℝ) :
    ∃ i j : ℤ,
      |(z₁ - i) + a * (z₂ - j)| ≤ 1 / 2 ∧
      |(z₂ - j) + a * (z₁ - i)| ≤ 1 / 2 ∧
      max |z₁ - i| |z₂ - j| ≤ 1 / (2 * (1 - |a|)) := by
  have haa : a * a < 1 := by nlinarith [sq_abs a, abs_nonneg a]
  obtain ⟨i, j, hi, hj⟩ := asymmetric_lattice_cover a a (mul_self_nonneg a)
    haa (z₁ + a * z₂) (z₂ + a * z₁)
  have hi' : |(z₁ - i) + a * (z₂ - j)| ≤ 1 / 2 := by
    convert hi using 1
    congr 1
    ring
  have hj' : |(z₂ - j) + a * (z₁ - i)| ≤ 1 / 2 := by
    convert hj using 1
    congr 1
    ring
  exact ⟨i, j, hi', hj', symmetric_lattice_distance a _ _ ha hi' hj'⟩

/-- Sliding rows have no shear bound. This is the local nilpotent model. -/
theorem sliding_rows_cover (d : ℝ) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + d * j)| ≤ 1 / 2 ∧
      |u₂ - (j : ℝ)| ≤ 1 / 2 := by
  simpa using asymmetric_lattice_cover d 0 (by simp) (by simp) u₁ u₂

end RuledApproximation

end

end OAI
