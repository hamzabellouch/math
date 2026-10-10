import OAI.MeasureTheory.Falconer.Slicing.GaussianPairBand

namespace OAI

/-! # Independent Gaussian rows used for the random-subspace estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianRows (d h : ℕ) : Measure (Fin h → Space d) :=
  Measure.pi (fun _ => stdGaussian (Space d))

instance gaussianRows_probability : IsProbabilityMeasure (gaussianRows d h) := by
  unfold gaussianRows
  infer_instance

theorem gaussianRows_one_band {w : Space d} (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    gaussianRows d h {A | ∀ i, |inner ℝ w (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianBandConstant*r)^h) := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ w (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ w x| ≤ r}) := by ext A; simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal (gaussianBandConstant*r) :=
      Finset.prod_le_prod (fun _ _ => gaussian_unit_inner_band hw hr)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ← ENNReal.ofReal_pow (mul_nonneg gaussianBandConstant_pos.le hr)]

theorem gaussianRows_two_orthogonal_bands {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    gaussianRows d h {A | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ s} ≤
      ENNReal.ofReal ((gaussianBandConstant^2*r*s)^h) := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ s} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ s}) := by
    ext A
    simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal (gaussianBandConstant^2*r*s) :=
      Finset.prod_le_prod (fun _ _ => gaussian_orthogonal_pair_band hu hv huv hr hs)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ← ENNReal.ofReal_pow (mul_nonneg (mul_nonneg (sq_nonneg _) hr) hs)]

theorem gaussianRows_rotation (e : Space d ≃ₗᵢ[ℝ] Space d) :
    Measure.map (fun A : Fin h → Space d => fun i => e (A i)) (gaussianRows d h) = gaussianRows d h := by
  unfold gaussianRows
  rw [Measure.pi_map_pi (fun _ => e.continuous.measurable.aemeasurable)]
  simp only [stdGaussian_map]

theorem gaussianRows_pair_band_chart {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : 0 ≤ inner ℝ u v)
    {r : ℝ} (hr : 0 < r) :
    gaussianRows d h {A | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant*r^2/(dist u v+r))^h) := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r}) := by
    ext A
    simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal (2*gaussianPairBandConstant*r^2/(dist u v+r)) :=
      Finset.prod_le_prod (fun _ _ => gaussian_two_band_projective_chart hu hv huv hr)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) gaussianPairBandConstant_pos.le)
        (sq_nonneg _)) (by positivity)

end Falconer

end OAI
