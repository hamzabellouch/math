import OAI.Analysis.LpDimension.GlobalCutoff

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE uV

namespace SubpolynomialLp

lemma weighted_gradient_measure_samples {E : Type uE} {V : Type uV}
    [Fintype E] [Fintype V] [Nonempty E]
    (A : Matrix E V ℝ) (p K b ε : ℝ) (hp : 0 < p) (hK : 0 ≤ K) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ μ : Measure (E → ℝ), IsProbabilityMeasure μ ∧
        (∀ᵐ z ∂μ, ∃ x, A.mulVec x=z) ∧ (∀ᵐ z ∂μ, ∀ e, |z e| ≤ K) ∧
        (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤ ε)
    (d : ℕ) (hd : 0 < d)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1) :
    ∃ z : Fin d → V → ℝ, ∀ e,
      |(∑ a, |A.mulVec (z a) e|^p)/(d:ℝ)-b| < 3*ε := by
  classical
  let S : Set (E → ℝ) := {m | ∃ z : V → ℝ,
    (∀ e, |A.mulVec z e| ≤ K) ∧ ∀ e, m e = |A.mulVec z e|^p}
  have hS : ∀ m ∈ S, ∀ e, m e ∈ Set.Icc 0 (K^p) := by
    rintro m ⟨z,hz,rflz⟩ e
    rw [rflz e]
    exact ⟨Real.rpow_nonneg (abs_nonneg _) _,Real.rpow_le_rpow (abs_nonneg _) (hz e) hp.le⟩
  have hw' : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ m ∈ closedConvexHull ℝ S, (∑ e, w e*|m e-b|) ≤ ε := by
    intro w hw0 hws
    obtain ⟨μ,hμ,hR,hB,hErr⟩ := hw w hw0 hws
    let : IsProbabilityMeasure μ := hμ
    let F : (E → ℝ) → E → ℝ := fun z e => |z e|^p
    have hi (e : E) : Integrable (fun z => F z e) μ :=
      bounded_coordinate_power_integrable μ e p K hp.le (hB.mono (fun z hz => hz e))
    have hIV : Integrable F μ := integrable_pi_iff.mpr hi
    have hFS : ∀ᵐ z ∂μ, F z ∈ S := by
      filter_upwards [hR,hB] with z hz hBz
      obtain ⟨x,hx⟩ := hz
      exact ⟨x,by simpa only [hx] using hBz,fun e => by dsimp [F]; rw [hx]⟩
    have hh := convex_closedConvexHull.integral_mem (isClosed_closedConvexHull (𝕜 := ℝ) (s := S))
      (hFS.mono (fun z hz => subset_closedConvexHull hz)) hIV
    have he : (∫ z, F z ∂μ)=fun e => ∫ z, |z e|^p ∂μ := by
      ext e
      exact ((ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).integral_comp_comm hIV).symm
    rw [he] at hh
    exact ⟨_,hh,hErr⟩
  obtain ⟨m,hm,hme⟩ := weighted_moments_samples (S := S) (K^p)
    (Real.rpow_nonneg hK _) hS b ε hε hw' d hd hprob
  choose z hz hmz using hm
  refine ⟨z,fun e => ?_⟩
  simpa only [hmz] using hme e

variable {E : Type uE} [Fintype E]

def globalCutLaw (μ : Measure (E → ℝ)) (T : ℝ) : Measure (E → ℝ) := μ.map (globalCut T)

instance globalCutLaw_probability (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (T : ℝ) :
    IsProbabilityMeasure (globalCutLaw μ T) := by
  unfold globalCutLaw
  infer_instance

lemma globalCutLaw_moment (μ : Measure (E → ℝ)) (T p : ℝ) (e : E) :
    (∫ z, |z e|^p ∂globalCutLaw μ T)=∫ z, |globalCut T z e|^p ∂μ :=
  integral_map (measurable_globalCut T).aemeasurable (show Measurable (fun z : E → ℝ => |z e|^p) by fun_prop).aestronglyMeasurable

lemma globalCutLaw_bound (μ : Measure (E → ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ z ∂globalCutLaw μ T, ∀ e, |z e| ≤ T := by
  apply ae_all_iff.mpr
  intro e
  apply (ae_map_iff (measurable_globalCut T).aemeasurable (measurableSet_le (by fun_prop) measurable_const)).mpr
  exact ae_of_all _ (fun z => globalCut_bound T hT z e)

lemma globalCutLaw_submodule (μ : Measure (E → ℝ)) (T : ℝ) (V : Submodule ℝ (E → ℝ))
    (hV : ∀ᵐ z ∂μ, z ∈ V) : ∀ᵐ z ∂globalCutLaw μ T, z ∈ V := by
  apply (ae_map_iff (measurable_globalCut T).aemeasurable V.closed_of_finiteDimensional.measurableSet).mpr
  exact hV.mono (fun z hz => globalCut_submodule T z V hz)

omit [Fintype E] in
lemma convolutionPower_coordinate_integrable (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (B p : ℝ) (hp : 0 ≤ p) (hB : ∀ᵐ z ∂μ, ∀ e, |z e| ≤ B) (N : ℕ) (e : E) :
    Integrable (fun z => |z e|^p) (convolutionPower μ N) := by
  have hb : ∀ᵐ x ∂coordinateLaw μ e, |x| ≤ B :=
    (coordinateLaw_ae μ e _ (measurableSet_le (by fun_prop) measurable_const)).mpr (hB.mono (fun z hz => hz e))
  have hi := bounded_abs_moment_integrable (convolutionPower (coordinateLaw μ e) N) ((N:ℝ)*B) p
    (convolutionPower_bounded _ _ hb N) hp
  rw [← coordinateLaw_convolutionPower,coordinateLaw_integrable _ _ _ (by fun_prop)] at hi
  exact hi

end SubpolynomialLp

end

end OAI
