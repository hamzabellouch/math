import OAI.Analysis.BernoulliCone.RadialShapeTest

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Shape
variable {d : ℕ}

lemma small_parameter_bounds {φ : Space d → ℝ} {C : ℝ≥0}
    (hφ : ContDiff ℝ ∞ φ) (hLip : LipschitzWith C φ)
    (e : Space d) {t : ℝ} (ht : |t| < (4*((C:ℝ)*‖e‖+1))⁻¹) :
    ‖t‖₊*C*‖e‖₊ < 1 ∧ ∀ x, (1:ℝ)/2 ≤ 1+t*fderiv ℝ φ x e := by
  have hC : 0 ≤ (C:ℝ)*‖e‖ := mul_nonneg C.coe_nonneg (norm_nonneg _)
  have hp : 0 < 4*((C:ℝ)*‖e‖+1) := by positivity
  have hh : |t| *(4*((C:ℝ)*‖e‖+1)) < 1 := (lt_div_iff₀ hp).mp (by simpa only [one_div] using ht)
  have hprod : |t| *(C:ℝ)*‖e‖ < (1:ℝ)/4 := by nlinarith [abs_nonneg t]
  constructor
  · change ‖t‖*(C:ℝ)*‖e‖ < 1
    rw [Real.norm_eq_abs]
    linarith
  · intro x
    have hb := (fderiv ℝ φ x).le_opNorm e
    have hn := ((hφ.differentiable (by simp)) x).hasFDerivAt.le_of_lipschitz hLip
    have hb' : |fderiv ℝ φ x e| ≤ (C:ℝ)*‖e‖ := by
      rw [← Real.norm_eq_abs]
      exact hb.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    have hh' : |t*fderiv ℝ φ x e| < (1:ℝ)/4 := by
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hb' (abs_nonneg _)) (by simpa only [mul_assoc] using hprod)
    have hneg := neg_abs_le (t*fderiv ℝ φ x e)
    linarith

/-- Domain comparisons for the *actual* Bernoulli energy force the unit slope
of a minimizing halfspace. No boundary condition is assumed. -/
theorem positiveLinear_minimizer_unit {e : Space d} (he : e ≠ 0)
    (hm : GlobalMinimizer (positiveLinear e)) : ‖e‖=1 := by
  let φ : Space d → ℝ := HarmonicKernel.potential
  have hφ : Test (ball (0:Space d) 2) φ := potential_test
  obtain ⟨C,hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  let I : ℝ := ∫ x in ball (0:Space d) 2, firstTerm φ e x
  have hI : I ≠ 0 := firstTerm_potential_integral_ne_zero he
  let B : ℝ := (2*‖e‖^4*(C:ℝ)^2)*(volume (ball (0:Space d) 2)).toReal
  have hε : 0 < (4*((C:ℝ)*‖e‖+1))⁻¹ := by positivity
  have hz : (1-‖e‖^2)*I/2 = 0 := by
    apply linear_coefficient_eq_zero _ B hε
    intro t ht
    obtain ⟨hK,hdet⟩ := small_parameter_bounds hφ.1 hLip e ht
    let hf := displacement_lipschitz hLip e t
    let g : Space d ≃ₜ Space d := perturbationHomeomorph hf hK
    have hg : ∀ x, g x=deform φ e t x := fun _ => rfl
    let v := fun y => positiveLinear e (g.symm y)
    have hvLip := (positiveLinear_lipschitz e).comp (perturbationHomeomorph_symm_lipschitz hf hK)
    have hsup : tsupport (fun x => v x-positiveLinear e x) ⊆ tsupport φ :=
      pullback_diff_support (u:=positiveLinear e) e t g hg
    have hc : HasCompactSupport (fun x => v x-positiveLinear e x) :=
      hφ.2.1.of_isClosed_subset (isClosed_tsupport _) hsup
    have hcB := hsup.trans hφ.2.2
    have hcomp := hm.compare_lipschitz (positiveLinear_lipschitz e) hvLip 0 (by norm_num : 0 < (2:ℝ))
      (Eventually.of_forall (fun _ => le_max_right _ _)) hc hcB
    have hupper := energy_pullback_upper hφ.1 hLip he t hdet g hg 0 2 (by
      intro x hx
      by_contra hh
      exact hx (hφ.2.2 (subset_tsupport φ hh)))
    change energy (ball (0:Space d) 2) v (gradient v) ≤ _ at hupper
    have hboth := hcomp.trans hupper
    dsimp [B,I]
    nlinarith
  have hz' : (1-‖e‖^2)*I=0 := (div_eq_zero_iff).mp hz |>.resolve_right (by norm_num)
  have hn : 1-‖e‖^2=0 := (mul_eq_zero.mp hz').resolve_right hI
  nlinarith [norm_nonneg e]
end Bernoulli.Shape

end
end

end OAI
