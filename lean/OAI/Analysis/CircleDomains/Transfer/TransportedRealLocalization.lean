import OAI.Analysis.CircleDomains.Selection.RealStageEstimates

namespace OAI

/-! Energy transport on retained source subsets and away from a prescribed core set. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_real_energy_on_source_set
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (w : (ℝ × ℝ) → ℝ) (hw : ContDiffOn ℝ ∞ w (realChartDomain U))
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain U, (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain U))
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsU : s ⊆ realChartDomain U) :
    IntegrableOn (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      (Complex.equivRealProdCLM ⁻¹' (sphereRealMap f '' s)) ∧
    (∫ z in Complex.equivRealProdCLM ⁻¹' (sphereRealMap f '' s),
      euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) =
      ∫ x in s, gradientEnergy w g x := by
  have hO := isOpen_realChartDomain hU
  obtain ⟨hW, hv, _⟩ := transported_real_coordinate heq hV hUinf hfix hO (Subset.refl _) w hw
  have himage : MeasurableSet (sphereRealMap f '' s) :=
    hs.image_of_continuousOn_injOn
      (fun x hx => (heq.real_smooth hUinf hfix (hsU hx)).continuousAt.continuousWithinAt)
      ((heq.real_bijOn hUinf hfix).injOn.mono hsU)
  have htarget := (integrable_transported_real_coordinate_iff heq hV hUinf hfix
    hO (Subset.refl _) w hw hs hsU hf (fun x hx => hg x (hsU hx))).mpr (hi.mono_set hsU)
  obtain ⟨hc, he⟩ := real_gradient_energy_in_complex_coordinates hW himage (image_mono hsU)
    (hv.of_le (by norm_num)) htarget
  rw [← transported_sphereRealFunction_eq] at hc he
  exact ⟨hc, he.trans (integral_transported_real_coordinate heq hV hUinf hfix
    hO (Subset.refl _) w hw hs hsU hf (fun x hx => hg x (hsU hx)))⟩

namespace FiniteTransfer.RealTransferStage

variable {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {u : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}
  (M : RealTransferStage G π σ u a b Flag O K₀ ε)

/-- The finite target energy away from a retained source set is charged to
original source energy away from that same set, plus the transfer error. -/
theorem transported_energy_away_lt (l : Fin n)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEc : E ⊆ M.core)
    {W : Set ℂ} (hW : W ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap M.forward '' (realChartDomain (openCompletedRegion M.terminals.H) \ E))) :
    IntegrableOn (euclideanGradientEnergy
      ((sphereRealFunction (M.functions l) ∘ M.inverse) ∘ ((↑) : ℂ → Sphere))) W ∧
    (∫ z in W, euclideanGradientEnergy
      ((sphereRealFunction (M.functions l) ∘ M.inverse) ∘ ((↑) : ℂ → Sphere)) z) <
      (∫ x in realChartDomain G \ E,
        gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) x) + ε := by
  let _ : Fintype M.indices := M.finite_indices.fintype
  let A := realChartDomain (openCompletedRegion M.terminals.H)
  have hA : IsOpen A := isOpen_realChartDomain (isOpen_openCompletedRegion M.terminals.H)
  obtain ⟨hi, he⟩ := transported_real_energy_on_source_set M.equivalence
    (isOpen_openCompletedRegion M.terminals.H) M.circle_domain.1 M.source_infty M.principal.1
    (M.functions l) (M.functions_smooth_source l) M.metric_conformal
    (fun x _ => M.metric_pos x) (M.functions_integrable_source l)
    (hA.measurableSet.diff hE) sdiff_subset
  refine ⟨hi.mono_set hW, lt_of_le_of_lt ?_ (M.source_energy l E hE hEc)⟩
  apply le_trans (setIntegral_mono_set hi
    (ae_of_all _ (fun z => euclideanGradientEnergy_nonneg _ z))
    (Eventually.of_forall fun _ hz => hW hz))
  rw [he]
  exact setIntegral_mono_set ((M.integrable l).mono_set sdiff_subset)
    (ae_of_all _ (fun x => gradientEnergy_nonneg _ M.metric_pos x))
    (Eventually.of_forall fun _ hx =>
      ⟨openCompletedRegion_subset_completedRegion M.terminals.H hx.1, hx.2⟩)

end FiniteTransfer.RealTransferStage

end CircleDomainRigidity

end

end OAI
