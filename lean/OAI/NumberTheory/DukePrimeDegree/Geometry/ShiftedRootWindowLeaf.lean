import OAI.NumberTheory.DukePrimeDegree.Geometry.NestedRectangleRestriction
import OAI.NumberTheory.DukePrimeDegree.Geometry.ShiftedRealWindow

namespace OAI

/-! # The actual root leaf supplied by an independent physical window -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]

omit [StandardBorelSpace B] [Nonempty B] in
lemma factorChart_shifted_ae_original {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (A : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (σ : Measure (S × (B × ℝ))) [IsFiniteMeasure σ]
    (e : S × B → RootSlice i j k) (he : MeasurableEmbedding e)
    (τ : S × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2+τ z.1)))
    {P : RootSlice i j k × ℝ → Prop} (hP : ∀ᵐ z ∂A.coordinateMeasure μ, P z) :
    ∀ᵐ z ∂σ, P (e (z.1,z.2.1),z.2.2+τ (z.1,z.2.1)) := by
  rw [hcoord] at hP
  have hm := (he.measurable.comp measurable_fst).prodMk
    (measurable_snd.add (hτ.comp measurable_fst))
  have H := ae_of_ae_map hm.aemeasurable hP
  exact ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable H

omit [StandardBorelSpace B] [Nonempty B] in
lemma factorChart_shifted_conditionals_at_sample {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (A : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (σ : Measure (S × (B × ℝ))) [IsFiniteMeasure σ]
    (e : S × B → RootSlice i j k) (he : MeasurableEmbedding e)
    (τ : S × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2+τ z.1))) :
    ∀ᵐ z ∂σ, A.conditionalKernel μ (e (z.1,z.2.1)) =
      ((σ.map MeasurableEquiv.prodAssoc.symm).condKernel (z.1,z.2.1)).map
        (Homeomorph.addRight (τ (z.1,z.2.1))) := by
  let η := σ.map MeasurableEquiv.prodAssoc.symm
  have H := conditional_map_fibers_embedding η e he
    (fun z => z.2+τ z.1) (measurable_snd.add (hτ.comp measurable_fst))
  have H' : ∀ᵐ a ∂η.fst, A.conditionalKernel μ (e a) =
      (η.condKernel a).map (Homeomorph.addRight (τ a)) := by
    filter_upwards [H] with a ha
    have ha' : (η.map (fun z => (e z.1,z.2+τ z.1))).condKernel (e a) =
        (η.condKernel a).map (Homeomorph.addRight (τ a)) := ha
    simpa only [η,←hcoord,RootBox.conditionalKernel] using ha'
  have H'' := ae_of_ae_map measurable_fst.aemeasurable H'
  exact ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable H''

theorem shifted_independent_window_root_leaf {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (A : RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ, rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (σ : Measure (S × (B × ℝ))) [IsFiniteMeasure σ]
    (e : S × B → RootSlice i j k) (he : MeasurableEmbedding e)
    (τ : S × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2+τ z.1)))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ a, (Homeomorph.addRight (τ a)) '' J ⊆ A.time) :
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    ∀ᵐ z ∂ρ, ((ρ.condKernel z.1).snd).map (Homeomorph.addRight (-z.2.2)) =
      (anchorNormalize
        (intrinsicRootLeaf hij μ (rootQuotientParametrization hij
          (e (z.1,z.2.1),z.2.2+τ (z.1,z.2.1))))
        (Homeomorph.addRight (-z.2.2) '' J)).restrict (Homeomorph.addRight (-z.2.2) '' J) := by
  intro ρ hp
  let P := fun z : RootSlice i j k × ℝ =>
    A.IsNormalizedRootLeaf R μ z.1 (A.leafMeasure R μ z.1) ∧
    0 < A.leafMeasure R μ z.1 (Metric.ball z.2 1) ∧
    intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) =
      basedRealMeasure (A.leafMeasure R μ z.1) z.2
  have hP : ∀ᵐ z ∂A.coordinateMeasure μ, P z := by
    have H := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
    filter_upwards [H,A.ae_leafMeasure_ball_pos R hAR μ hfree,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree] with z hz hb hi
    exact ⟨hz,hb 1 zero_lt_one,hi⟩
  have hρ : ρ ≪ σ := Measure.absolutelyContinuous_restrict
  have hgood := hρ.ae_le (factorChart_shifted_ae_original hij A μ σ e he τ hτ hcoord hP)
  have hcond := hρ.ae_le (factorChart_shifted_conditionals_at_sample hij A μ σ e he τ hτ hcoord)
  filter_upwards [hgood,hcond,independent_restrict_real_marginal σ J hJ hp] with z hz hc hr
  let ν := A.leafMeasure R μ (e (z.1,z.2.1))
  let a := τ (z.1,z.2.1)
  let t := z.2.2
  let : IsLocallyFiniteMeasure ν := hz.1.1
  have hκ : ((σ.map MeasurableEquiv.prodAssoc.symm).condKernel (z.1,z.2.1)).map
      (Homeomorph.addRight a) = ν.restrict A.time := hc.symm.trans hz.1.2.2.1.symm
  have ht : 0 < (ν.map (Homeomorph.addRight (-a))) (Metric.ball t 1) := by
    have H := translatedRealMeasure_ball ν (t+a) (-a) 1
    rw [show t+a+-a=t by ring] at H
    rw [H]
    exact hz.2.1
  rw [hr.2]
  have H := shifted_real_window_rebase ν _ A.time J hJ a t (hwindow _) hκ ht
  simpa only [hz.2.2] using H

end DukePrimeDegree

end

end OAI
