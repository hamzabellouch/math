import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights

namespace OAI

/-! Exact conversion of a pressure-coordinate minimum to its selected-field CGF. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma pressureCoordinate_minimum_rescale {M L : ℝ → ℝ} {N a w s c : ℝ}
    (hN : 0 ≤ N) (ha : 0 < a) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (hlo : 1 ≤ w - s) (hhi : w + s ≤ 2)
    (hmean : ∀ v ∈ Set.Icc (1 : ℝ) 2, L (a * v) = N * (M v - M 0))
    (hmin : ∀ v ∈ Set.Icc (1 : ℝ) 2,
      -M w + c * (w - 3 / 2) ^ 2 ≤ -M v + c * (v - 3 / 2) ^ 2) :
    ∀ t ∈ Set.Icc (a * w - a * s) (a * w + a * s),
      -L (a * w) + (N * c / a ^ 2) * (a * w - a * (3 / 2)) ^ 2 ≤
      -L t + (N * c / a ^ 2) * (t - a * (3 / 2)) ^ 2 := by
  intro t ht
  have htv : t / a ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ ha).mpr
      nlinarith [ht.1]
    · apply (div_le_iff₀ ha).mpr
      nlinarith [ht.2]
  have hm := hmean (t / a) htv
  rw [mul_div_cancel₀ _ ha.ne'] at hm
  rw [hm, hmean w hw]
  have hc := mul_le_mul_of_nonneg_left (hmin (t / a) htv) hN
  have he1 : (N * c / a ^ 2) * (a * w - a * (3 / 2)) ^ 2 =
      N * (c * (w - 3 / 2) ^ 2) := by field_simp
  have he2 : (N * c / a ^ 2) * (t - a * (3 / 2)) ^ 2 =
      N * (c * (t / a - 3 / 2) ^ 2) := by field_simp
  rw [he1, he2]
  linarith

/-- Comparing a Gaussian-coordinate minimum with its centered choice
puts it in the interior, using the Gaussian variance cap of the frozen field. -/
lemma gaussianCoordinate_minimum_penalty {N : ℕ} (hN : 0 < N) (j : Fin N)
    (M : ℝ → ℝ) (u : ℝ) (hu : |u| ≤ 2)
    (hcost : 0 ≤ M (3 / 2) - M 0 ∧ M u - M 0 ≤ (perturbationAmplitude N j * u) ^ 2 / (2 * N))
    (hmin : -M u + perturbationWeight j * (u - 3 / 2) ^ 2 ≤
      -M (3 / 2) + perturbationWeight j * (3 / 2 - 3 / 2) ^ 2) :
    (u - 3 / 2) ^ 2 ≤ 2 * perturbationScale N ^ 2 * perturbationWeight j := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := perturbationWeight_pos j
  have ha := perturbationAmplitude_sq N j
  have hu2 : u ^ 2 ≤ 4 := by
    have hb := abs_le.mp hu
    nlinarith [sq_nonneg (u + 2), sq_nonneg (u - 2)]
  have hanu : (perturbationAmplitude N j * u) ^ 2 / (2 * N) ≤
      2 * perturbationScale N ^ 2 * perturbationWeight j ^ 2 := by
    apply (div_le_iff₀ (show 0 < 2 * (N : ℝ) by positivity)).mpr
    rw [mul_pow, ha]
    nlinarith [mul_le_mul_of_nonneg_left hu2
      (show 0 ≤ (N : ℝ) * perturbationScale N ^ 2 * perturbationWeight j ^ 2 by positivity)]
  have hm : perturbationWeight j * (u - 3 / 2) ^ 2 ≤
      perturbationWeight j * (2 * perturbationScale N ^ 2 * perturbationWeight j) := by
    nlinarith [hcost.1, hcost.2]
  exact (mul_le_mul_iff_right₀ hw).mp hm

lemma gaussianCoordinate_minimum_interior {N : ℕ} (j : Fin N) {u s : ℝ}
    (hpen : (u - 3 / 2) ^ 2 ≤ 2 * perturbationScale N ^ 2 * perturbationWeight j)
    (he : perturbationScale N ≤ 1 / 8) (hs : s ≤ 1 / 4) :
    1 ≤ u - s ∧ u + s ≤ 2 := by
  have he0 := perturbationScale_nonneg N
  have hw := perturbationWeight_le_one j
  have hbnd : (u - 3 / 2) ^ 2 ≤ 1 / 32 := by
    have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * perturbationScale N ^ 2 by positivity)
    nlinarith [sq_nonneg (perturbationScale N - 1 / 8)]
  constructor <;> nlinarith [sq_nonneg (u - 3 / 2 - 1 / 4), sq_nonneg (u - 3 / 2 + 1 / 4)]

lemma diagonalCoordinate_minimum_penalty {M : ℝ → ℝ} {w e : ℝ}
    (hcost : 0 ≤ M (3 / 2) - M 0 ∧ M w - M 0 ≤ 2 * e)
    (hmin : -M w + (w - 3 / 2) ^ 2 ≤ -M (3 / 2) + (3 / 2 - 3 / 2) ^ 2) :
    (w - 3 / 2) ^ 2 ≤ 2 * e := by
  nlinarith [hcost.1, hcost.2]

lemma diagonalCoordinate_minimum_interior {w e s : ℝ}
    (hpen : (w - 3 / 2) ^ 2 ≤ 2 * e) (he : e ≤ 1 / 32) (hs : s ≤ 1 / 4) :
    1 ≤ w - s ∧ w + s ≤ 2 := by
  constructor <;> nlinarith [sq_nonneg (w - 3 / 2 - 1 / 4), sq_nonneg (w - 3 / 2 + 1 / 4)]

end InvariantIsing

end

end OAI
