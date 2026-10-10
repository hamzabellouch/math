import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalC2
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolarL2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! # Classical angular projections of the actual physical realization

Only square integrability of the angular test is needed. Harmonicity and
the angular eigenvalue are deliberately absent from this calculus lemma.
-/

open MeasureTheory Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem integrable_sphere_pairing (h G : PhysicalUnitSphere → ℂ)
    (hh : Integrable h physicalSphereMeasure) (hG : Continuous G) :
    Integrable (fun ω => inner ℂ (h ω) (G ω)) physicalSphereMeasure := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  apply (hh.norm.const_mul (max B 0)).mono'
    (hh.aestronglyMeasurable.inner hG.aestronglyMeasurable)
  filter_upwards [] with ω
  exact (norm_inner_le_norm _ _).trans (by
    calc
      ‖h ω‖ * ‖G ω‖ ≤ ‖h ω‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hB ω (mem_univ _)).trans (le_max_left B 0))
          (norm_nonneg (h ω))
      _ = max B 0 * ‖h ω‖ := mul_comm _ _)

private theorem continuous_sphere_pairing (h : PhysicalUnitSphere → ℂ)
    (hh : Integrable h physicalSphereMeasure) (G : ℝ → PhysicalUnitSphere → ℂ)
    (hG : Continuous (Function.uncurry G)) :
    Continuous (fun r => ∫ ω, inner ℂ (h ω) (G r ω) ∂physicalSphereMeasure) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn
    (hG.continuousOn : ContinuousOn (Function.uncurry G) (Icc (r - 1) (r + 1) ×ˢ univ))
  apply continuousAt_of_dominated
    (bound := fun ω => max B 0 * ‖h ω‖)
    (Eventually.of_forall (fun t => hh.aestronglyMeasurable.inner
      (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ?_ (hh.norm.const_mul _) ?_
  · filter_upwards [Ioo_mem_nhds (by linarith : r - 1 < r) (by linarith : r < r + 1)] with t ht
    filter_upwards [] with ω
    exact (norm_inner_le_norm _ _).trans (by
      calc
        ‖h ω‖ * ‖G t ω‖ ≤ ‖h ω‖ * max B 0 :=
          mul_le_mul_of_nonneg_left
            ((hB (t, ω) ⟨⟨ht.1.le, ht.2.le⟩, mem_univ _⟩).trans (le_max_left B 0))
            (norm_nonneg (h ω))
        _ = max B 0 * ‖h ω‖ := mul_comm _ _)
  · exact Eventually.of_forall (fun ω => continuousAt_const.inner
      (hG.comp (continuous_id.prodMk continuous_const)).continuousAt)

private theorem hasDerivAt_sphere_pairing (h : PhysicalUnitSphere → ℂ)
    (hh : Integrable h physicalSphereMeasure) (G Gd : ℝ → PhysicalUnitSphere → ℂ)
    (hG : Continuous (Function.uncurry G)) (hGd : Continuous (Function.uncurry Gd))
    (hd : ∀ r ω, HasDerivAt (fun t => G t ω) (Gd r ω) r) (r : ℝ) :
    HasDerivAt (fun t => ∫ ω, inner ℂ (h ω) (G t ω) ∂physicalSphereMeasure)
      (∫ ω, inner ℂ (h ω) (Gd r ω) ∂physicalSphereMeasure) r := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn
    (hGd.continuousOn : ContinuousOn (Function.uncurry Gd) (Icc (r - 1) (r + 1) ×ˢ univ))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t ω => inner ℂ (h ω) (G t ω))
    (F' := fun t ω => inner ℂ (h ω) (Gd t ω))
    (bound := fun ω => max B 0 * ‖h ω‖)
    (Ioo_mem_nhds (by linarith : r - 1 < r) (by linarith : r < r + 1))
    (Eventually.of_forall (fun t => hh.aestronglyMeasurable.inner
      (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    (integrable_sphere_pairing h (G r) hh (hG.comp (continuous_const.prodMk continuous_id)))
    (hh.aestronglyMeasurable.inner
      (hGd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (fun ω t ht => (norm_inner_le_norm _ _).trans (by
      calc
        ‖h ω‖ * ‖Gd t ω‖ ≤ ‖h ω‖ * max B 0 :=
          mul_le_mul_of_nonneg_left
            ((hB (t, ω) ⟨⟨ht.1.le, ht.2.le⟩, mem_univ _⟩).trans (le_max_left B 0))
            (norm_nonneg (h ω))
        _ = max B 0 * ‖h ω‖ := mul_comm _ _)))
    (hh.norm.const_mul _) (Eventually.of_forall (fun ω t _ =>
      ((innerSL ℂ (h ω)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hd t ω)))).2

noncomputable def homogeneousAngularProjection (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (h : PhysicalUnitSphere → ℂ) (u : HomogeneousY a k) (r : ℝ) : ℂ :=
  ∫ ω, inner ℂ (h ω) (homogeneousPhysicalCLM a k ha ha1 hk u (r • ω.1)) ∂physicalSphereMeasure

/-- The first derivative of the angular component is the angular component
of the directional radial derivative. -/
theorem hasDerivAt_homogeneousAngularProjection (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a k) (r : ℝ) :
    HasDerivAt (homogeneousAngularProjection a k ha ha1 hk h u)
      (∫ ω, inner ℂ (h ω)
        (fderiv ℝ (homogeneousPhysicalCLM a k ha ha1 hk u) (r • ω.1) ω.1)
        ∂physicalSphereMeasure) r := by
  let f : E → ℂ := homogeneousPhysicalCLM a k ha ha1 hk u
  have hf : ContDiff ℝ 2 f := contDiff_homogeneousPhysical a k ha ha1 hk u
  have hfd : Continuous (fderiv ℝ f) :=
    ((contDiff_one_iff_fderiv.mp (hf.of_le (by norm_num))).2)
  apply hasDerivAt_sphere_pairing h (hh.integrable (by norm_num))
    (fun r ω => f (r • ω.1)) (fun r ω => fderiv ℝ f (r • ω.1) ω.1)
  · exact hf.continuous.comp (continuous_fst.smul continuous_snd.subtype_val)
  · exact (hfd.comp (continuous_fst.smul continuous_snd.subtype_val)).clm_apply continuous_snd.subtype_val
  · intro t ω
    have hline : HasDerivAt (fun s : ℝ => s • ω.1) ω.1 t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const ω.1
    simpa only [Function.comp_def] using
      (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hline

/-- Every angular coefficient of an actual Y vector is C² in the radius.
No spherical harmonic equation is needed for this regularity. -/
theorem contDiff_homogeneousAngularProjection (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a k) :
    ContDiff ℝ 2 (homogeneousAngularProjection a k ha ha1 hk h u) := by
  let f : E → ℂ := homogeneousPhysicalCLM a k ha ha1 hk u
  let G₁ : ℝ → PhysicalUnitSphere → ℂ := fun r ω => fderiv ℝ f (r • ω.1) ω.1
  let G₂ : ℝ → PhysicalUnitSphere → ℂ := fun r ω =>
    fderiv ℝ (fderiv ℝ f) (r • ω.1) ω.1 ω.1
  have hf : ContDiff ℝ 2 f := contDiff_homogeneousPhysical a k ha ha1 hk u
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  have hffd : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (contDiff_one_iff_fderiv.mp hfd).2
  have hG₁ : Continuous (Function.uncurry G₁) :=
    (hfd.continuous.comp (continuous_fst.smul continuous_snd.subtype_val)).clm_apply
      continuous_snd.subtype_val
  have hG₂ : Continuous (Function.uncurry G₂) :=
    ((hffd.comp (continuous_fst.smul continuous_snd.subtype_val)).clm_apply
      continuous_snd.subtype_val).clm_apply continuous_snd.subtype_val
  have hd (r : ℝ) := hasDerivAt_homogeneousAngularProjection a k ha ha1 hk h hh u r
  have hd₁ (r : ℝ) : HasDerivAt
      (fun t => ∫ ω, inner ℂ (h ω) (G₁ t ω) ∂physicalSphereMeasure)
      (∫ ω, inner ℂ (h ω) (G₂ r ω) ∂physicalSphereMeasure) r := by
    apply hasDerivAt_sphere_pairing h (hh.integrable (by norm_num)) G₁ G₂ hG₁ hG₂
    intro t ω
    have hline : HasDerivAt (fun s : ℝ => s • ω.1) ω.1 t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const ω.1
    have he : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • ω.1))
        (fderiv ℝ (fderiv ℝ f) (t • ω.1) ω.1) t := by
      simpa only [Function.comp_def] using
        (hfd.differentiable (by norm_num) (t • ω.1)).hasFDerivAt.comp_hasDerivAt t hline
    change HasDerivAt (fun s : ℝ => (fderiv ℝ f (s • ω.1)) ω.1)
      ((fderiv ℝ (fderiv ℝ f) (t • ω.1) ω.1) ω.1) t
    exact (ContinuousLinearMap.apply ℝ ℂ ω.1).hasFDerivAt.comp_hasDerivAt t he
  have hderiv : deriv (homogeneousAngularProjection a k ha ha1 hk h u) =
      fun t => ∫ ω, inner ℂ (h ω) (G₁ t ω) ∂physicalSphereMeasure :=
    funext (fun r => (hd r).deriv)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun r => (hd r).differentiableAt, by simp, ?_⟩
  rw [hderiv, contDiff_one_iff_deriv]
  refine ⟨fun r => (hd₁ r).differentiableAt, ?_⟩
  have he : deriv (fun t => ∫ ω, inner ℂ (h ω) (G₁ t ω) ∂physicalSphereMeasure) =
      fun t => ∫ ω, inner ℂ (h ω) (G₂ t ω) ∂physicalSphereMeasure :=
    funext (fun r => (hd₁ r).deriv)
  rw [he]
  exact continuous_sphere_pairing h (hh.integrable (by norm_num)) G₂ hG₂

end DefocusingNLS

end OAI
