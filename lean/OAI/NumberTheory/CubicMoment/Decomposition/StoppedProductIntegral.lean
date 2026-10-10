import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductGaussMellin

namespace OAI

/-! Norm transfer through the entire product Mellin line. The central
polynomial bound, derived Gauss complement and elementary model tail are
kept separate in this finite integral inequality. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma centered_mellin_integral_bound
    (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hP : ∀ a ∈ P, primary a) (hB : ∀ b ∈ B, primary b)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {X S Mc Mg Mm : ℝ}
    (hX : 0 < X) (hS : 0 < S) (hMc : 0 ≤ Mc) (hMm : 0 ≤ Mm) (u : ℝ)
    (hcentral : ∀ τ : ℝ, |τ| ≤ (4/3)*S →
      ‖centeredProductPolynomial P B α β 0 (u-τ)‖ ≤ Mc)
    (hmodel : ∀ t : ℝ, ‖squarefreeProductModel P B α β t‖ ≤ Mm)
    (hgauss : ‖∫ τ : ℝ, (1-(heightPartitionBump (τ/S):ℂ))*zeroLineMellinWeight V X τ*
      ∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist (u-τ) (a*b)‖ ≤ Mg) :
    ‖centeredProductSmoothed P B α β 0 V X u‖ ≤
      zeroLineMellinMass V*Mc+Mg+
        cStar*(Mm/S)*(∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖) := by
  let w := zeroLineMellinWeight V X
  let c := fun τ => centeredProductPolynomial P B α β 0 (u-τ)
  let m := fun τ => squarefreeProductModel P B α β (u-τ)
  let g := fun τ => ∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist (u-τ) (a*b)
  let χ := fun τ => (1:ℂ)-(heightPartitionBump (τ/S):ℂ)
  have hw : Integrable w := zeroLineMellinWeight_integrable V hV hpos hsm hX
  have hc : Integrable (fun τ => w τ*c τ) :=
    centered_product_mellin_integrable P B α β 0 V hV hpos hsm hX u
  have hm : Integrable (fun τ => w τ*m τ) := by
    apply hw.mul_bdd (c := Mm)
    · have hcont : Continuous m := by
        convert (continuous_squarefreeProductModel P B α β 0).comp
          ((continuous_const : Continuous (fun _ : ℝ => u)).sub continuous_id) using 1
        funext τ
        simp only [m,Function.comp_def,Pi.sub_apply,id_eq,add_zero]
      exact hcont.aestronglyMeasurable
    · filter_upwards with τ
      exact hmodel (u-τ)
  have hχ : Continuous χ := continuous_const.sub
    (Complex.continuous_ofReal.comp (heightPartitionBump.continuous.comp (continuous_id.div_const S)))
  have hcχ : Integrable (fun τ => χ τ*(w τ*c τ)) :=
    hc.bdd_mul hχ.aestronglyMeasurable (Filter.Eventually.of_forall (height_bump_complement_norm S))
  have hmχ : Integrable (fun τ => χ τ*(w τ*m τ)) :=
    hm.bdd_mul hχ.aestronglyMeasurable (Filter.Eventually.of_forall (height_bump_complement_norm S))
  have hge : (fun τ => χ τ*w τ*g τ) =
      fun τ => χ τ*(w τ*c τ)+(cStar:ℂ)*(χ τ*(w τ*m τ)) := by
    funext τ
    have he := centered_product_eq_gauss_sub_model P B α β (u-τ)
    dsimp only [c,g,m]
    rw [he]
    ring
  have hgχ : Integrable (fun τ => χ τ*w τ*g τ) := by
    rw [hge]
    exact hcχ.add (hmχ.const_mul _)
  have htail : (∫ τ : ℝ, χ τ*(w τ*c τ)) =
      (∫ τ : ℝ, χ τ*w τ*g τ)-(cStar:ℂ)*(∫ τ : ℝ, χ τ*w τ*m τ) := by
    rw [hge,integral_add hcχ (hmχ.const_mul _),integral_const_mul]
    have hem : (fun τ => χ τ*w τ*m τ) = (fun τ => χ τ*(w τ*m τ)) := by
      funext τ; ring
    rw [hem]
    ring
  have hmodeltail := smooth_mellin_model_tail_bound w m 1
    (zeroLineMellinWeight_moment_integrable V hV hpos hsm hX 1) hS hMm
    (fun τ => hmodel (u-τ))
  have hmoment : (∫ τ : ℝ, |τ| * ‖w τ‖) =
      ∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖ := by
    apply integral_congr_ae
    filter_upwards with τ
    rw [zeroLineMellinWeight_norm V hX,
      zeroLineMellinWeight_norm V (by norm_num : (0:ℝ) < 1)]
  simp only [pow_one] at hmodeltail
  rw [hmoment] at hmodeltail
  have hcenter := smooth_mellin_central_bound w c hw hS hMc hcentral
  rw [zeroLineMellinWeight_mass V hX] at hcenter
  simp_rw [mul_assoc] at hcenter
  have htailbound : ‖∫ τ : ℝ, χ τ*(w τ*c τ)‖ ≤
      Mg+cStar*(Mm/S)*(∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖) := by
    rw [htail]
    apply (norm_sub_le _ _).trans
    apply add_le_add hgauss
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg cStar_pos.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmodeltail cStar_pos.le
  rw [centered_product_mellin P B α β hP hB 0 V hV hpos hsm hX u,
    smooth_height_integral_split _ hc S]
  exact (norm_add_le _ _).trans ((add_le_add hcenter htailbound).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
