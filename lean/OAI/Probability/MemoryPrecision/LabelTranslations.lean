import Mathlib
import OAI.Probability.GaussianRegression.Main

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
section Translation
variable {Ω Y : Type*}
  [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [R1Space Ω]
  [NormedAddCommGroup Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  (γ : Measure Ω) [SFinite γ] (τ : Measure Y) [SFinite τ] [τ.IsAddRightInvariant]

def labelTranslate (u : Y) : C(Ω × Y, Ω × Y) :=
  ⟨fun x => (x.1, x.2 + u), by fun_prop⟩

omit [BorelSpace Ω] [R1Space Ω] [SecondCountableTopology Y] in
lemma measurePreserving_labelTranslate (u : Y) :
    MeasurePreserving (labelTranslate u) (γ.prod τ) (γ.prod τ) := by
  exact (MeasurePreserving.id γ).prod (measurePreserving_add_right τ u)

omit [MeasurableSpace Ω] [BorelSpace Ω] [R1Space Ω]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
lemma continuous_labelTranslate : Continuous (labelTranslate (Ω := Ω) (Y := Y)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : Y × (Ω × Y) => (z.2.1, z.2.2 + z.1))
  fun_prop

variable [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)]

lemma tendsto_eLpNorm_labelTranslate_sub {F : Ω × Y → ℝ} (hF : MemLp F 1 (γ.prod τ)) :
    Tendsto (fun u : Y => eLpNorm (fun x => F (x.1, x.2 + u) - F x) 1 (γ.prod τ))
      (𝓝 0) (𝓝 0) := by
  let f := hF.toLp F
  let g := fun u => Lp.compMeasurePreserving (labelTranslate u)
    (measurePreserving_labelTranslate γ τ u) f
  have hc : Continuous g := continuous_const.compMeasurePreservingLp continuous_labelTranslate
    (measurePreserving_labelTranslate γ τ) (by simp)
  have hg0 : g 0 = f := by
    have he : (labelTranslate (Ω := Ω) (0:Y) : Ω × Y → Ω × Y) = id := by
      ext x <;> simp [labelTranslate]
    dsimp only [g]
    simp only [he, Lp.compMeasurePreserving_id_apply]
  have ht : Tendsto g (𝓝 0) (𝓝 (hF.toLp F)) := by
    simpa only [hg0] using hc.tendsto 0
  have hl := (Lp.tendsto_Lp_iff_tendsto_eLpNorm g F hF).mp ht
  apply hl.congr'
  apply Eventually.of_forall
  intro u
  apply eLpNorm_congr_ae
  have he := (Lp.coeFn_compMeasurePreserving f (measurePreserving_labelTranslate γ τ u)).trans
    ((measurePreserving_labelTranslate γ τ u).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp)
  filter_upwards [he] with x hx
  exact congrArg (fun t => t - F x) hx

omit [BorelSpace Ω] [R1Space Ω] [SecondCountableTopology Y]
  [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)] in
lemma eLpNorm_labelTranslate_sub_le {F : Ω × Y → ℝ} (hF : MemLp F 1 (γ.prod τ)) (u : Y) :
    eLpNorm (fun x => F (x.1,x.2+u) - F x) 1 (γ.prod τ) ≤
      eLpNorm F 1 (γ.prod τ) + eLpNorm F 1 (γ.prod τ) := by
  have hp := measurePreserving_labelTranslate γ τ u
  have he := eLpNorm_comp_measurePreserving (p := (1:ℝ≥0∞)) hF.aestronglyMeasurable hp
  exact (eLpNorm_sub_le le_rfl).trans_eq
    (congrArg (fun t => t + eLpNorm F 1 (γ.prod τ)) he)
variable [NormedSpace ℝ Y]

def averageTranslate (κ : Measure Y) (δ : ℝ) (F : Ω × Y → ℝ) (x : Ω × Y) : ℝ :=
  ∫ u, F (x.1, x.2 + δ • u) ∂κ

omit [BorelSpace Ω] [R1Space Ω]
  [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)] in
lemma integrable_translate_product (κ : Measure Y) [IsProbabilityMeasure κ]
    {F : Ω × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 1 (γ.prod τ)) (δ : ℝ) :
    Integrable (fun z : Y × (Ω × Y) => F (z.2.1,z.2.2 + δ • z.1))
      (κ.prod (γ.prod τ)) := by
  refine ⟨(by fun_prop : Measurable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ (by fun_prop)]
  have he (u : Y) : (∫⁻ x, ‖F (x.1,x.2 + δ • u)‖ₑ ∂γ.prod τ) =
      eLpNorm F 1 (γ.prod τ) := by
    rw [← eLpNorm_one_eq_lintegral_enorm
      ((show Measurable (fun point : Ω × Y => F (point.1, point.2 + δ • u))
        from by fun_prop).aestronglyMeasurable)]
    exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable
      (measurePreserving_labelTranslate γ τ (δ • u))
  simp_rw [he]
  simpa using hF.eLpNorm_lt_top

omit [BorelSpace Ω] [R1Space Ω]
  [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)] in
lemma eLpNorm_averageTranslate_sub_le (κ : Measure Y) [IsProbabilityMeasure κ]
    {F : Ω × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 1 (γ.prod τ)) (δ : ℝ) :
    eLpNorm (fun x => averageTranslate κ δ F x - F x) 1 (γ.prod τ) ≤
      ∫⁻ u, eLpNorm (fun x => F (x.1,x.2 + δ • u) - F x) 1 (γ.prod τ) ∂κ := by
  have haverage : StronglyMeasurable (averageTranslate κ δ F) :=
    ((show Measurable (fun pair : (Ω × Y) × Y =>
      F (pair.1.1, pair.1.2 + δ • pair.2)) from by fun_prop).stronglyMeasurable).integral_prod_right'
  rw [eLpNorm_one_eq_lintegral_enorm
    (f := fun point => averageTranslate κ δ F point - F point)
    (haverage.aestronglyMeasurable.sub hF.aestronglyMeasurable)]
  have hi := (integrable_translate_product γ τ κ hFm hF δ).prod_left_ae
  calc
    _ ≤ ∫⁻ x, ∫⁻ u, ‖F (x.1,x.2 + δ • u) - F x‖ₑ ∂κ ∂γ.prod τ := by
      apply lintegral_mono_ae
      filter_upwards [hi] with x hx
      have he : averageTranslate κ δ F x - F x =
          ∫ u, F (x.1,x.2 + δ • u) - F x ∂κ := by
        rw [integral_sub hx (integrable_const (F x)), integral_const]
        simp [averageTranslate]
      rw [he]
      exact enorm_integral_le_lintegral_enorm _
    _ = _ := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      congr 1
      funext u
      exact (eLpNorm_one_eq_lintegral_enorm (by fun_prop)).symm

lemma tendsto_eLpNorm_averageTranslate_sub (κ : Measure Y) [IsProbabilityMeasure κ]
    {F : Ω × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 1 (γ.prod τ)) :
    Tendsto (fun δ : ℝ => eLpNorm (fun x => averageTranslate κ δ F x - F x)
      1 (γ.prod τ)) (𝓝 0) (𝓝 0) := by
  have ht : Tendsto (fun δ : ℝ => ∫⁻ u, eLpNorm
      (fun x => F (x.1,x.2 + δ • u) - F x) 1 (γ.prod τ) ∂κ)
      (𝓝 0) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence
      (μ := κ) (l := 𝓝 (0:ℝ)) (f := fun _ => 0)
      (fun _ => eLpNorm F 1 (γ.prod τ) + eLpNorm F 1 (γ.prod τ))
      (Eventually.of_forall (fun δ => ?_))
      (Eventually.of_forall (fun δ => Eventually.of_forall (fun u =>
        eLpNorm_labelTranslate_sub_le γ τ hF (δ • u))))
      (by simpa using ENNReal.add_ne_top.mpr ⟨hF.eLpNorm_lt_top.ne, hF.eLpNorm_lt_top.ne⟩)
      (Eventually.of_forall (fun u => ?_))
    · simpa using h
    · have hnorm (translation : Y) :
          eLpNorm (fun point => F (point.1, point.2 + δ • translation) - F point)
            1 (γ.prod τ) =
          ∫⁻ point, ‖F (point.1, point.2 + δ • translation) - F point‖ₑ ∂γ.prod τ :=
        eLpNorm_one_eq_lintegral_enorm (by fun_prop)
      simp_rw [hnorm]
      exact Measurable.lintegral_prod_right (by fun_prop)
    · exact (tendsto_eLpNorm_labelTranslate_sub γ τ hF).comp
        (by
          have hc : Continuous (fun δ : ℝ => δ • u) := by fun_prop
          simpa using hc.tendsto (0:ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (eLpNorm_averageTranslate_sub_le γ τ κ hFm hF)
end Translation
end MemoryPrecision


end

end OAI
