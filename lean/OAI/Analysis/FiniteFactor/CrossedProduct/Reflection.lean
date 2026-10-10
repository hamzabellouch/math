import OAI.Analysis.FiniteFactor.CrossedProduct.Transport

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

/-- The reflection for the source regular representation. -/
def sourceReflectionIndex (θ : SourceCoordinate → ℝ)
    (z : (SourceCoordinate → ℝ) × ℤ) : (SourceCoordinate → ℝ) × ℤ :=
  (coordinateRotate θ z.2 z.1, -z.2)

theorem sourceReflectionIndex_preserving (θ : SourceCoordinate → ℝ) :
    MeasurePreserving (sourceReflectionIndex θ)
      (sourceMeasure SourceCoordinate) (sourceMeasure SourceCoordinate) := by
  have hn : MeasurePreserving (fun n : ℤ => -n) Measure.count Measure.count := by
    refine ⟨measurable_of_countable _, ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_of_countable _) hS,
      Measure.count_apply (hS.preimage (measurable_of_countable _)), Measure.count_apply hS,
      ← neg_injective.encard_image, Set.image_preimage_eq S neg_surjective]
  have hm : Measurable (Function.uncurry (fun (n : ℤ) (x : SourceCoordinate → ℝ) => coordinateRotate θ n x)) := by
    apply Measurable.of_eval
    intro i
    unfold coordinateRotate
    fun_prop
  have hp := hn.skew_product hm (Eventually.of_forall (fun n => (coordinateRotate_preserving θ n).map_eq))
  exact Measure.measurePreserving_swap.comp (hp.comp Measure.measurePreserving_swap)

def sourceReflectionLinear (θ : SourceCoordinate → ℝ) :
    SourceHilbert SourceCoordinate →ₗᵢ[ℂ] SourceHilbert SourceCoordinate :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceReflectionIndex θ) (sourceReflectionIndex_preserving θ)

/-- Explicit conjugate-linear isometry; no modular or tracial property assumed. -/
def sourceConjugation (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    SourceHilbert SourceCoordinate := star (sourceReflectionLinear θ f)

theorem sourceConjugation_apply_ae (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    sourceConjugation θ f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => star (f (sourceReflectionIndex θ z)) := by
  filter_upwards [Lp.coeFn_star (sourceReflectionLinear θ f),
    Lp.coeFn_compMeasurePreserving f (sourceReflectionIndex_preserving θ)] with z hs hr
  change (star (sourceReflectionLinear θ f)) z = _
  rw [hs]
  change star ((sourceReflectionLinear θ f) z) = _
  change (sourceReflectionLinear θ f) z = f (sourceReflectionIndex θ z) at hr
  rw [hr]

theorem sourceConjugation_involutive (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    sourceConjugation θ (sourceConjugation θ f) = f := by
  apply Lp.ext
  have ht := (sourceReflectionIndex_preserving θ).quasiMeasurePreserving.ae (sourceConjugation_apply_ae θ f)
  filter_upwards [sourceConjugation_apply_ae θ (sourceConjugation θ f), ht, sourceHilbert_cube] with z h1 h2 hc
  rw [h1,h2,star_star]
  congr 1
  apply Prod.ext
  · change coordinateRotate θ (-z.2) (coordinateRotate θ z.2 z.1) = z.1
    rw [coordinateRotate_add, add_neg_cancel]
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  · simp [sourceReflectionIndex]

theorem sourceL2_star_inner (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (star f) (star g) = star (inner ℂ f g) := by
  rw [L2.inner_def, L2.inner_def]
  change _ = conj (∫ z, inner ℂ (f z) (g z) ∂sourceMeasure SourceCoordinate)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with z hf hg
  rw [hf,hg]
  simp [RCLike.inner_apply, mul_comm]

theorem sourceConjugation_inner (θ : SourceCoordinate → ℝ) (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (sourceConjugation θ f) (sourceConjugation θ g) = star (inner ℂ f g) := by
  rw [sourceConjugation, sourceConjugation, sourceL2_star_inner,
    (sourceReflectionLinear θ).inner_map_map]

theorem sourceConjugation_inner_symm (θ : SourceCoordinate → ℝ) (f g : SourceHilbert SourceCoordinate) :
    inner ℂ f (sourceConjugation θ g) = inner ℂ g (sourceConjugation θ f) := by
  have hh := sourceConjugation_inner θ (sourceConjugation θ f) g
  rw [sourceConjugation_involutive] at hh
  rw [hh]
  exact inner_conj_symm _ _

end
end FiniteFactor

end OAI
