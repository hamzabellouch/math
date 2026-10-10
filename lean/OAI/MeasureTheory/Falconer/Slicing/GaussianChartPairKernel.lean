import OAI.MeasureTheory.Falconer.Slicing.GaussianChartPairAverage
import OAI.MeasureTheory.Falconer.Angular.GnomonicPairGram

namespace OAI

/-! # The normalized pair kernel in the bounded gnomonic chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

 theorem gaussian_chart_pair_kernel {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    gaussianChartPairWeight h r p q ≤
      ENNReal.ofReal ((4*gaussianPairBandConstant)^h) *
        ENNReal.ofReal ((1/(dist p q+r))^(h:ℝ)) := by
  have hC0 := gaussianPairBandConstant_pos
  let u : Space (n+1) := (gnomonicChart p : Space (n+1))
  let v : Space (n+1) := (gnomonicChart q : Space (n+1))
  have hu : ‖u‖ = 1 := sphere_norm (gnomonicChart p)
  have hv : ‖v‖ = 1 := sphere_norm (gnomonicChart q)
  have hsep : dist p q ≤ 4*‖perpendicularPart u v‖ := by
    simpa only [dist_eq_norm,norm_sub_rev,u,v] using gnomonic_pair_separation hp hq
  have hsingle : stdGaussian (Space (n+1)) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (4*gaussianPairBandConstant*r^2/(dist p q+r)) := by
    apply (gaussian_two_band hu hv hr).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hC : 0 ≤ gaussianPairBandConstant*r^2 := by positivity
    calc
      _ ≤ (gaussianPairBandConstant*r^2)*(4*(‖perpendicularPart u v‖+r)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith
      _ = _ := by ring
  have hrows : gaussianRows (n+1) h
      {A | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} ≤
      ENNReal.ofReal ((4*gaussianPairBandConstant*r^2/(dist p q+r))^h) := by
    have he : {A : Fin h → Space (n+1) | ∀ i,
        |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} =
        Set.pi univ (fun _ => {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r}) := by ext A; simp
    rw [gaussianRows,he,Measure.pi_pi]
    calc
      _ ≤ ∏ _ : Fin h, ENNReal.ofReal (4*gaussianPairBandConstant*r^2/(dist p q+r)) :=
        Finset.prod_le_prod (fun _ _ => hsingle)
      _ = _ := by
        rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity)]
  apply (mul_le_mul' le_rfl hrows).trans_eq
  have he : (4*gaussianPairBandConstant*r^2/(dist p q+r))^h =
      ((4*gaussianPairBandConstant)*r^2)^h*(1/(dist p q+r))^(h:ℝ) := by
    rw [Real.rpow_natCast,div_pow,one_div,inv_pow,div_eq_mul_inv]
  rw [he,ENNReal.ofReal_mul (by positivity),← mul_assoc,
    gaussian_squared_band_normalization hr (by positivity)]

end Falconer

end OAI
