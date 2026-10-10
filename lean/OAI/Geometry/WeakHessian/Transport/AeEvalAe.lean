import Mathlib
import OAI.Geometry.WeakHessian.Measure.InlinedFile0

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma IsTestPlan.ae_eval_of_ae {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {p : X → Prop} (hp : ∀ᵐ x ∂m, p x) (t : Time) :
    ∀ᵐ γ ∂π, p (γ t) := by
  obtain ⟨C, hC⟩ := hπ.2.1
  exact ae_of_ae_map (continuous_eval_const t).measurable.aemeasurable
    ((Measure.absolutelyContinuous_of_le_smul (hC t)).ae_le hp)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_clampTime : Continuous clampTime := by
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuous_evalReal : Continuous (fun p : Curve X × ℝ => evalReal p.1 p.2) := by
  exact continuous_eval.comp (continuous_fst.prodMk (continuous_clampTime.comp continuous_snd))

lemma IsTestPlan.ae_ae_eval_of_ae {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {p : X → Prop} (hp : ∀ᵐ x ∂m, p x) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), p (evalReal γ t) := by
  let S := toMeasurable m {x | ¬ p x}
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hSzero : m S = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hp
  have hSae : ∀ᵐ x ∂m, x ∉ S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hSzero
  let : IsProbabilityMeasure π := hπ.1
  have hpath : ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      evalReal γ t ∉ S := by
    apply (Measure.ae_ae_comm (p := fun γ t => evalReal γ t ∉ S)
      (hSm.compl.preimage continuous_evalReal.measurable)).mpr
    exact ae_of_all _ fun t => hπ.ae_eval_of_ae hSae (clampTime t)
  filter_upwards [hpath] with γ hγ
  filter_upwards [hγ] with t ht
  by_contra hn
  exact ht (subset_toMeasurable m {x | ¬ p x} hn)

omit [BorelSpace X] in
lemma LocallyL2.ae_eq {f g : X → ℝ} (hf : LocallyL2 m f) (hfg : f =ᵐ[m] g) :
    LocallyL2 m g := by
  intro o R hR
  exact (hf o R hR).ae_eq (ae_restrict_of_ae hfg)

lemma IsLocalWeakUpperGradient.congr_ae {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hfg : f =ᵐ[m] g) (hDE : D =ᵐ[m] E) :
    IsLocalWeakUpperGradient m g E := by
  refine ⟨hD.1.ae_eq hDE, ?_, ?_⟩
  · filter_upwards [hD.2.1, hDE] with x hx hxe
    rwa [← hxe]
  · intro π hπ hb
    have hend : (fun γ : Curve X => ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)|)
        =ᵐ[π] (fun γ : Curve X => ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)|) := by
      filter_upwards [hπ.ae_eval_of_ae hfg timeOne, hπ.ae_eval_of_ae hfg timeZero]
        with γ h1 h0
      rw [h1, h0]
    have hpath : (fun γ : Curve X => ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t)
        =ᵐ[π] (fun γ : Curve X => ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t) := by
      filter_upwards [hπ.ae_ae_eval_of_ae hDE] with γ hγ
      apply lintegral_congr_ae
      filter_upwards [hγ] with t ht
      rw [ht]
    rw [← lintegral_congr_ae hend, ← lintegral_congr_ae hpath]
    exact hD.2.2 π hπ hb

lemma IsMinimalLocalWeakUpperGradient.congr_ae {f g D E : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) (hfg : f =ᵐ[m] g)
    (hDE : D =ᵐ[m] E) : IsMinimalLocalWeakUpperGradient m g E := by
  refine ⟨hD.1.congr_ae hfg hDE, ?_⟩
  intro E' hE'
  have hmin := hD.2 _ (hE'.congr_ae hfg.symm Filter.EventuallyEq.rfl)
  filter_upwards [hmin, hDE] with x hx he
  rwa [← he]

lemma exists_isMinimal_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    (∃ D, IsMinimalLocalWeakUpperGradient m f D) ↔
      ∃ D, IsMinimalLocalWeakUpperGradient m g D := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨D, hD.congr_ae hfg Filter.EventuallyEq.rfl⟩
  · rintro ⟨D, hD⟩
    exact ⟨D, hD.congr_ae hfg.symm Filter.EventuallyEq.rfl⟩

lemma weakGradient_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    weakGradient m f =ᵐ[m] weakGradient m g := by
  by_cases hf : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact (weakGradient_isMinimal hf).ae_eq
      ((weakGradient_isMinimal ((exists_isMinimal_congr_ae hfg).mp hf)).congr_ae
        hfg.symm Filter.EventuallyEq.rfl)
  · have hg := mt (exists_isMinimal_congr_ae hfg).mpr hf
    simp only [weakGradient, dite_eq_right hf, dite_eq_right hg]
    exact Filter.EventuallyEq.rfl

lemma localSobolev_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    LocalSobolev m f ↔ LocalSobolev m g :=
  ⟨fun h => ⟨h.1.ae_eq hfg, (exists_isMinimal_congr_ae hfg).mp h.2⟩,
    fun h => ⟨h.1.ae_eq hfg.symm, (exists_isMinimal_congr_ae hfg).mpr h.2⟩⟩

lemma sobolev_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    Sobolev m f ↔ Sobolev m g := by
  constructor
  · intro h
    exact ⟨h.1.ae_eq hfg, (localSobolev_congr_ae hfg).mp h.2.1,
      h.2.2.ae_eq (weakGradient_congr_ae hfg)⟩
  · intro h
    exact ⟨h.1.ae_eq hfg.symm, (localSobolev_congr_ae hfg).mpr h.2.1,
      h.2.2.ae_eq (weakGradient_congr_ae hfg).symm⟩

lemma gamma_congr_ae {f f' g g' : X → ℝ} (hff : f =ᵐ[m] f')
    (hgg : g =ᵐ[m] g') : gamma m f g =ᵐ[m] gamma m f' g' := by
  filter_upwards [weakGradient_congr_ae (hff.add hgg),
    weakGradient_congr_ae (hff.sub hgg)] with x hp hm
  change weakGradient m (fun y => f y + g y) x =
    weakGradient m (fun y => f' y + g' y) x at hp
  change weakGradient m (fun y => f y - g y) x =
    weakGradient m (fun y => f' y - g' y) x at hm
  simp only [gamma, hp, hm]

end WeakHessian

end
end InlinedFile0

end OAI
