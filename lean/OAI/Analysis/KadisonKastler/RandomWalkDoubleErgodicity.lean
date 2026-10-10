import OAI.Analysis.KadisonKastler.BilateralTwistedErgodicity

namespace OAI

/-! The exact unitary double-ergodicity property of the constructed boundary.

This is the bounded unitary-coefficient specialization of the Poisson-boundary
result cited in `PublishedBoundary`, proved by the bilateral independent-block
argument of manuscript Section 4.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem randomWalkUnitaryDoubleErgodic : UnitaryDoubleErgodic (randomWalkBoundaryAction G) := by
  intro K _ _ _ _ σ f hf hbound heq
  borelize K
  let F₀ : BilateralWalkPath G → K := f ∘ bilateralBoundaryPair G
  have hp := bilateralBoundaryPair_measurePreserving G
  have hm : AEStronglyMeasurable F₀ (bilateralWalkLaw G) := hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  obtain ⟨C, hC⟩ := hbound
  have hmem : MemLp F₀ 2 (bilateralWalkLaw G) := MemLp.of_bound hm C (hp.quasiMeasurePreserving.ae hC)
  let F : Lp K 2 (bilateralWalkLaw G) := hmem.toLp F₀
  have hF : (F : BilateralWalkPath G → K) =ᵐ[bilateralWalkLaw G] F₀ := hmem.coeFn_toLp
  have ht₀ := bilateral_equivariant_function_transport σ hf heq
  have ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      F (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (F ω) := by
    have hs := (bilateralTranslate_measurePreserving G 1).quasiMeasurePreserving.ae hF
    filter_upwards [hF, hs, ht₀] with ω hx hs ht
    exact hs.trans (ht.trans (congrArg (σ (ω 0)⁻¹ : K →L[ℂ] K) hx.symm))
  let v := ∫ ω, F ω ∂bilateralWalkLaw G
  have hconst := bilateral_twisted_invariant_constant σ F ht
  have hFv : (F : BilateralWalkPath G → K) =ᵐ[bilateralWalkLaw G] fun _ => v := by
    have he : (F : BilateralWalkPath G → K) = (hilbertConstantL2 (bilateralWalkLaw G) v : BilateralWalkPath G → K) :=
      congrArg (fun h : Lp K 2 (bilateralWalkLaw G) => (h : BilateralWalkPath G → K)) hconst
    exact (Filter.EventuallyEq.of_eq he).trans (hilbertConstantL2_ae v)
  have hfv : f =ᵐ[(randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)] fun _ => v := by
    have hraw : F₀ =ᵐ[bilateralWalkLaw G] fun _ => v := hF.symm.trans hFv
    have hbad : NullMeasurableSet {z | f z ≠ v}
        ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)) :=
      (nullMeasurableSet_eq_fun hf.aemeasurable (aemeasurable_const (b := v))).compl
    rw [Filter.EventuallyEq, ae_iff, ← hp.measure_preimage hbad]
    exact ae_iff.mp hraw
  exact ⟨v, (randomWalkBoundaryAction G).diagonal.fixed_of_ae_constant
    (fun g x => (σ g : K →L[ℂ] K) x) f v hfv heq, hfv⟩

end

end KadisonKastler

end OAI
