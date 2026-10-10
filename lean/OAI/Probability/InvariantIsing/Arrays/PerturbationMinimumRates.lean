import OAI.Probability.InvariantIsing.Pressure.PressureCoordinateMinimum

namespace OAI

/-! Vanishing rates for diagonal perturbation energies at parameter minima. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def diagonalContactRate (N : ℕ) (L : ℝ) : ℝ :=
  let a := N * perturbationScale N
  let c := N / a ^ 2
  let θ := 1 / (Real.sqrt N * perturbationScale N)
  let δ := 2 * N * Real.sqrt (L / N)
  (2 * c + θ ^ 2) / (2 * θ) + c * (a * contactStep N) + 4 * δ / (a * contactStep N)

lemma diagonalContactRate_eq {N : ℕ} (hN : 0 < N) (L : ℝ) :
    diagonalContactRate N L = (3 / 2) * (N : ℝ) ^ (-7 / 16 : ℝ) +
      (1 + 8 * Real.sqrt L) * (N : ℝ) ^ (-3 / 16 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have he : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have h1 : 1 / (Real.sqrt N * perturbationScale N) = (N : ℝ) ^ (-7 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, perturbationScale, ← Real.rpow_add hn,
      one_div, ← Real.rpow_neg hn.le]
    congr 1
    norm_num
  have h2 : contactStep N / perturbationScale N = (N : ℝ) ^ (-3 / 16 : ℝ) := by
    rw [contactStep, perturbationScale, ← Real.rpow_sub hn]
    congr 1
    norm_num
  have h3 : 1 / (Real.sqrt N * perturbationScale N * contactStep N) =
      (N : ℝ) ^ (-3 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, perturbationScale, contactStep,
      ← Real.rpow_add hn, ← Real.rpow_add hn, one_div, ← Real.rpow_neg hn.le]
    congr 1
    norm_num
  calc
    _ = (3 / 2) * (1 / (Real.sqrt N * perturbationScale N)) +
        contactStep N / perturbationScale N +
        8 * Real.sqrt L * (1 / (Real.sqrt N * perturbationScale N * contactStep N)) := by
      unfold diagonalContactRate
      rw [Real.sqrt_div' L hn.le]
      have hn' : (N : ℝ) = (Real.sqrt N) ^ 2 := (Real.sq_sqrt hn.le).symm
      conv_lhs => rw [hn']
      simp only [Real.sqrt_sq hr.le]
      field_simp
      ring
    _ = _ := by rw [h1, h2, h3]; ring

lemma diagonalContactRate_tendsto (L : ℝ) :
    Tendsto (fun N => diagonalContactRate N L) atTop (nhds 0) := by
  have h1 := (tendsto_nat_rpow_neg (c := 7 / 16) (by norm_num)).const_mul (3 / 2 : ℝ)
  have h2 := (tendsto_nat_rpow_neg (c := 3 / 16) (by norm_num)).const_mul (1 + 8 * Real.sqrt L)
  apply Tendsto.congr' _ (show Tendsto _ _ (nhds (0 : ℝ)) from by simpa using h1.add h2)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [neg_div] using (diagonalContactRate_eq hN L).symm

end InvariantIsing

end

end OAI
