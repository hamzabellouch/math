import OAI.Analysis.KadisonKastler.ModularActionCocycle
import OAI.Analysis.KadisonKastler.RegularCoreSpatialTransport

namespace OAI

/-! # Concrete core isomorphisms from unitary cocycles -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)}

namespace ModularActionCocycle

variable (c : ModularActionCocycle M U V)

def gauge : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularUnitaryField volume c.regularField c.regularField_measurable c.regularField_star_measurable

theorem gauge_apply_ae (f : RegularCoreHilbert H) :
    (c.gauge : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t => (c.regularField t : H →L[ℂ] H) (f t) :=
  regularUnitaryField_apply_ae volume _ _ _ f

theorem gauge_symm_eq_star : c.symm.gauge = star c.gauge := by
  have h : c.symm.gauge * c.gauge = 1 := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [c.symm.gauge_apply_ae ((c.gauge :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f), c.gauge_apply_ae f] with t hs hc
    change ((c.symm.gauge : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((c.gauge : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t = f t
    rw [hs, hc]
    change (star (c.regularField t : H →L[ℂ] H)) ((c.regularField t : H →L[ℂ] H) (f t)) = f t
    exact congrArg (fun a : H →L[ℂ] H => a (f t))
      (Unitary.star_mul_self_of_mem (c.regularField t).property)
  exact eq_inv_of_mul_eq_one_left h

private theorem conj_of_intertwines (g : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (a b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (h : (g : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * a = b * g) :
    unitaryConj g a = b := by
  change ((g : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * a) * star (g :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) = b
  rw [h, mul_assoc, Unitary.mul_star_self_of_mem g.property, mul_one]

variable
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gauge_embedding (a : H →L[ℂ] H) (ha : a ∈ M) :
    unitaryConj c.gauge (regularCoreEmbedding U hU a) = regularCoreEmbedding V hV a := by
  apply conj_of_intertwines
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [c.gauge_apply_ae (regularCoreEmbedding U hU a f),
    regularCoreEmbedding_apply_ae U hU a f,
    regularCoreEmbedding_apply_ae V hV a ((c.gauge :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f), c.gauge_apply_ae f]
    with t hg hu hv hf
  change ((c.gauge : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularCoreEmbedding U hU a f)) t =
    (regularCoreEmbedding V hV a ((c.gauge :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t
  rw [hg, hu, hv, hf]
  have he := congrArg (fun b : H →L[ℂ] H => b (f t)) (c.regularField_embedding t a ha)
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp] using he

theorem gauge_translation (s : Multiplicative ℝ) :
    unitaryConj c.gauge (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
    regularCoreEmbedding V hV (star (c.value s⁻¹ : H →L[ℂ] H)) *
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply conj_of_intertwines
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [c.gauge_apply_ae ((regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f,
    regularCoreEmbedding_apply_ae V hV (star (c.value s⁻¹ : H →L[ℂ] H))
      ((regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((c.gauge : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    regularRightTranslation_apply_ae s ((c.gauge :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (c.gauge_apply_ae f)] with t hg hρ hπ hρg hgshift
  simp only [Function.comp_def] at hgshift
  change ((c.gauge : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t =
    (regularCoreEmbedding V hV (star (c.value s⁻¹ : H →L[ℂ] H))
      ((regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((c.gauge : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))) t
  rw [hg, hρ, hπ, hρg, hgshift]
  have he := congrArg (fun b : H →L[ℂ] H => b (f (t + s.toAdd)))
    (c.regularField_translation s.toAdd t)
  have hs : Multiplicative.ofAdd (-s.toAdd) = s⁻¹ := by simp
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp, hs] using he

theorem gauge_core_le :
    spatialTransportAlgebra (Unitary.linearIsometryEquiv c.gauge) (regularCoreAlgebra U hU M) ≤
      regularCoreAlgebra V hV M := by
  unfold regularCoreAlgebra
  rw [spatialTransport_generated, StarAlgHom.map_adjoin]
  apply generatedVonNeumannAlgebra_le_of_le
  apply StarAlgebra.adjoin_le
  rintro _ ⟨a, (⟨b, hb, rfl⟩ | ⟨s, rfl⟩), rfl⟩
  · change unitaryConj c.gauge (regularCoreEmbedding U hU b) ∈ regularCoreAlgebra V hV M
    rw [c.gauge_embedding hU hV b hb]
    exact regularCoreEmbedding_mem_core V hV M hb
  · change unitaryConj c.gauge (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈ regularCoreAlgebra V hV M
    rw [c.gauge_translation hV s]
    exact mul_mem (regularCoreEmbedding_mem_core V hV M (star_mem (c.mem s⁻¹)))
      (regularTranslation_mem_core V hV M s)

theorem gauge_conjugates_core :
    Conjugates c.gauge (regularCoreAlgebra U hU M) (regularCoreAlgebra V hV M) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact c.gauge_core_le hU hV ⟨b, hb, rfl⟩
  · intro ha
    have hm : unitaryConj c.symm.gauge a ∈ regularCoreAlgebra U hU M :=
      c.symm.gauge_core_le hV hU ⟨a, ha, rfl⟩
    rw [c.gauge_symm_eq_star] at hm
    refine ⟨unitaryConj (star c.gauge) a, hm, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj (star c.gauge) a

include c in
theorem core_equiv :
    Nonempty (Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra V hV M)) := by
  have h : spatialTransportAlgebra (Unitary.linearIsometryEquiv c.gauge)
      (regularCoreAlgebra U hU M) = regularCoreAlgebra V hV M :=
    SetLike.coe_injective (c.gauge_conjugates_core hU hV)
  have e := spatialTransportEquiv (Unitary.linearIsometryEquiv c.gauge) (regularCoreAlgebra U hU M)
  rw [h] at e
  exact ⟨e⟩

end ModularActionCocycle

end

end KadisonKastler

end OAI
