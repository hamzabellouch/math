import OAI.Probability.PosteriorReplicas.Measures.EuclideanLabels
import OAI.Probability.PosteriorReplicas.Measures.GaussianConstant

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

lemma ae_gaussianDensityVersion {d k : ℕ} (hk : 1 ≤ k) (hk' : k+2 ≤ d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞)
    (hfL : ∀ x, f x ≤ L) {A : Rows d k} (hA : LinearIndependent ℝ A) :
    projectedDensity base f A =ᵐ[volume]
      gaussianDensityVersion ((base.measure d).withDensity f) A := by
  let : NeZero d := ⟨by omega⟩
  let : NeZero k := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  have he0 := (measurable_projectedDensity (d := d) (k := k) base hf).comp
    (show Measurable (fun y : Vec k => (A,WithLp.ofLp y)) from
      measurable_const.prodMk (WithLp.measurable_ofLp 2 (Labels k)))
  simp only [Function.comp_def] at he0
  have he : Measurable (fun y : Vec k => projectedDensity base f A (WithLp.ofLp y)) := he0
  have hμ := euclideanLabelLaw_density hA (by omega : k < d) base hf
  have hd := ae_ball_differentiation (E := Vec k) he hμ
  have hde := (PiLp.volume_preserving_toLp (Fin k)).quasiMeasurePreserving.ae hd
  filter_upwards [hde] with y hy
  have hM := fun v : Vec k => projectedDensity_uniform_bound hk' base hfL A (WithLp.ofLp v)
  have H := tendsto_scaledRadial_at_ball_point he hμ
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLt) hM hy
  have heq : ∀ n, (∫⁻ x, scaledRadial n (WithLp.toLp 2 y) x
      ∂euclideanLabelLaw ((base.measure d).withDensity f) A) =
      ∫⁻ x, ENNReal.ofReal ((2*Real.pi*((n+1:ℝ)⁻¹)^2)^(-(k:ℝ)/2) *
        Real.exp (-(labelNorm (labels A x-y))^2/(2*((n+1:ℝ)⁻¹)^2)))
        ∂(base.measure d).withDensity f := by
    intro n
    rw [euclideanLabelLaw, lintegral_map (show Measurable (scaledRadial n (WithLp.toLp 2 y)) by
      unfold scaledRadial; fun_prop) (by fun_prop)]
    simp only [scaledRadial_eq, labelNorm, WithLp.toLp_sub]
  simp_rw [heq] at H
  exact H.liminf_eq.symm

theorem equalLabelVersions : EqualLabelVersions := by
  intro d k m hk hm hdim base f hf hL
  obtain ⟨L,hLt,hfL⟩ := hL
  have hd : k+m+2 ≤ d := by omega
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  dsimp only
  let ν := (base.measure d).withDensity f
  have hp := measurable_projectedDensity (d := d) (k := k) base hf
  have hb := measurable_ballDensityVersion (d := d) (k := k) ν
  have hg := measurable_gaussianDensityVersion (d := d) (k := k) ν
  have hball : ∀ A : Rows d k, LinearIndependent ℝ A →
      projectedDensity base f A =ᵐ[volume] ballDensityVersion ν A :=
    fun A hA => ae_ballDensityVersion hk (by omega : k < d) base hf hLt hfL hA
  have hgauss : ∀ A : Rows d k, LinearIndependent ℝ A →
      projectedDensity base f A =ᵐ[volume] gaussianDensityVersion ν A :=
    fun A hA => ae_gaussianDensityVersion hk (by omega : k+2 ≤ d) base hf hLt hfL hA
  refine ⟨hp, hb, hg, ?_, ?_⟩
  · intro A hA
    exact ⟨projected_measure hA (by omega) base hf, hball A hA, hgauss A hA⟩
  · have hbt := equal_label_transfer_prop hd hk hm base hf hLt hfL
      (P := fun A y => projectedDensity base f A y = ballDensityVersion ν A y)
      (measurableSet_eq_fun hp hb) (fun A hA => by
        filter_upwards [hball A hA] with y hy
        exact fun _ => hy)
    have hgt := equal_label_transfer_prop hd hk hm base hf hLt hfL
      (P := fun A y => projectedDensity base f A y = gaussianDensityVersion ν A y)
      (measurableSet_eq_fun hp hg) (fun A hA => by
        filter_upwards [hgauss A hA] with y hy
        exact fun _ => hy)
    filter_upwards [ae_constrained_support hd hk hm base hf hLt hfL, hbt, hgt] with u hu hb hg
    refine ⟨hu.1, ?_⟩
    filter_upwards [hu.2, hb, hg] with A hA hba hga
    exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, hba, hga⟩

end PosteriorReplicas
end

end OAI
