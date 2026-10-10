import OAI.Geometry.RCD.Sobolev.LocalGradientLipschitz

namespace OAI

/-! # Local gradient bounds from a bounded Lipschitz representative -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Compact localization makes a local Lipschitz representative an actual
Sobolev comparison function. The extra amplitude term is quantitative. -/
theorem localGamma_le_of_lipschitz_representative
    (f : SobolevSpace μ hQ) (v : X → ℝ) (L A : ℝ≥0) (hv : LipschitzWith L v)
    (p : X) (r : ℝ) (hr : 0 < r)
    (he : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict (ball p (2*r))] v)
    (hA : ∀ᵐ x ∂μ.restrict (ball p (2*r)), |SobolevSpace.toLp μ hQ f x| ≤ A) :
    ∀ᵐ x ∂μ.restrict (ball p r), localGamma μ hQ f f x ≤ ((L:ℝ)+(A:ℝ)/r)^2 := by
  let χ := radialCutoff p r
  let w := fun x => χ x*clipReal A (v x)
  let M : ℝ≥0 := ⟨(L:ℝ)+(A:ℝ)/r,by positivity⟩
  have hχ := radialCutoff_lipschitz p hr
  have hvclip : LipschitzWith L (fun x => clipReal A (v x)) := by
    simpa only [one_mul,Function.comp_apply] using! (clipReal_lipschitz A).comp hv
  have hw : LipschitzWith M w := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hdv := hvclip.dist_le_mul x y
    have hdc := hχ.dist_le_mul x y
    rw [Real.dist_eq] at hdv hdc
    have hc : |χ x| ≤ 1 := by
      rw [abs_of_nonneg (radialCutoff_bounds p r x).1]
      exact (radialCutoff_bounds p r x).2
    have hc' : |clipReal A (v y)| ≤ (A:ℝ) := clipReal_abs_le A (v y)
    rw [Real.dist_eq]
    change |χ x*clipReal A (v x)-χ y*clipReal A (v y)| ≤ _
    calc
      _ = |χ x*(clipReal A (v x)-clipReal A (v y))+(χ x-χ y)*clipReal A (v y)| := by congr 1; ring
      _ ≤ |χ x| *|clipReal A (v x)-clipReal A (v y)|+|χ x-χ y| *|clipReal A (v y)| := by
        simpa only [abs_mul] using abs_add_le (χ x*(clipReal A (v x)-clipReal A (v y)))
          ((χ x-χ y)*clipReal A (v y))
      _ ≤ 1*((L:ℝ)*dist x y)+(r⁻¹*dist x y)*(A:ℝ) :=
        add_le_add (mul_le_mul hc hdv (abs_nonneg _) (by norm_num))
          (mul_le_mul hdc hc' (abs_nonneg _) (by positivity))
      _ = M*dist x y := by
        change _ = ((L:ℝ)+(A:ℝ)/r)*dist x y
        ring
  have hs : HasCompactSupport w :=
    (radialCutoff_hasCompactSupport p hr).mul_right
  let z := SobolevSpace.ofLipschitzCompact μ hQ hw hs
  have hz : SobolevSpace.toLp μ hQ z =ᵐ[μ] w :=
    SobolevSpace.ofLipschitzCompact_coe μ hQ hw hs
  have hsub : ball p r ⊆ ball p (2*r) := ball_subset_ball (by linarith)
  have hfz : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict (ball p r)] SobolevSpace.toLp μ hQ z := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub he,
      ae_restrict_of_ae_restrict_of_subset hsub hA,ae_restrict_of_ae hz,
      ae_restrict_mem measurableSet_ball] with x he ha hz hx
    have hχx : χ x = 1 := radialCutoff_eq_one p hr (by rw [dist_comm]; exact le_of_lt hx)
    rw [hz]
    change _ = χ x*clipReal A (v x)
    rw [hχx,one_mul,← he,clipReal_eq_self A ha]
  filter_upwards [hfz,ae_restrict_of_ae (localGamma_eq_on_eq μ hQ f z f),
    ae_restrict_of_ae (localGamma_eq_on_eq μ hQ f z z),
    ae_restrict_of_ae (localGamma_comm μ hQ z f),ae_restrict_of_ae (localGamma_self μ hQ z),
    ae_restrict_of_ae (SobolevSpace.minimalSlope_le_lipschitz μ hQ z hw hz),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ z))]
    with x he h1 h2 hcomm hself hgrad hnonneg
  rw [h1 he,hcomm,h2 he,hself]
  exact pow_le_pow_left₀ hnonneg hgrad 2

end RegularPointCoordinates

end

end OAI
