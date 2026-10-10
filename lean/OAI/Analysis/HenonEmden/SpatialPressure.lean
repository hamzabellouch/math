import OAI.Analysis.HenonEmden.Interaction

namespace OAI

universe uX uY uX2 uY2 uX3 uY3 uX4 uY4 uE

section SpatialPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden.LineComponents

lemma forwardExit_congr_section {X : Type uX} {Y : Type uY} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) :
    forwardExit U x = forwardExit V y := by
  classical
  unfold forwardExit SegmentInside
  simp_rw [he]
lemma backwardExit_congr_section {X : Type uX2} {Y : Type uY2} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) :
    backwardExit U x = backwardExit V y := by
  classical
  unfold backwardExit SegmentInside
  simp_rw [he]
lemma componentInf_congr_section {X : Type uX3} {Y : Type uY3} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} {f : X × ℝ → ℝ} {g : Y × ℝ → ℝ}
    (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) (hv : ∀ s, f (x,s)=g (y,s)) :
    componentInf U f x = componentInf V g y := by
  classical
  unfold componentInf SegmentInside
  simp_rw [he,hv]
lemma componentWeight_congr_section {X : Type uX4} {Y : Type uY4} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} {h d : X × ℝ → ℝ} {h' d' : Y × ℝ → ℝ}
    (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) (hh : ∀ s, h (x,s)=h' (y,s))
    (hd : ∀ s, d (x,s)=d' (y,s)) (δ : ℝ) :
    componentWeight U h d δ x = componentWeight V h' d' δ y := by
  classical
  rw [componentWeight,componentWeight,componentLength,componentLength,
    forwardExit_congr_section he,backwardExit_congr_section he,
    componentInf_congr_section he hh,componentInf_congr_section he hd,he 0]

end HenonLaneEmden.LineComponents
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents LineCoordinates LayerTonelli
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def coordinateLayerEquiv (e : sphere (0:E) 1) : ((transverse e × ℝ) × ℝ) ≃ᵐ (E × ℝ) :=
  MeasurableEquiv.prodCongr (measurableEquiv e) (MeasurableEquiv.refl ℝ)

omit [Nontrivial E] in
lemma measurePreserving_coordinateLayer (e : sphere (0:E) 1) {f : E → ℝ} (hf : Measurable f) :
    MeasurePreserving (coordinateLayerEquiv e)
      (layerMeasure (volume.prod volume) (f ∘ measurableEquiv e)) (layerMeasure volume f) := by
  exact ((measurePreserving e).prod (MeasurePreserving.id volume)).restrict_preimage
    (measurableSet_sourceSubgraph hf)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma coordinate_layer_open (e : sphere (0:E) 1) {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    IsOpen (parameterLayer (f ∘ measurableEquiv e)) := by
  exact hf.preimage (show Continuous (fun z : (transverse e × ℝ) × ℝ =>
    (measurableEquiv e (z.1.1,z.2),z.1.2)) by
      exact ((continuous_measurableEquiv e).comp (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)

lemma coordinate_sourceWeight (e : sphere (0:E) 1) {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (a : (transverse e × ℝ) × ℝ) :
    LayerPressure.sourceWeight (f ∘ measurableEquiv e) (weight volume κ e ∘ measurableEquiv e)
        (d ∘ measurableEquiv e) δ a =
      lineWeight volume f κ δ (e,measurableEquiv e a.1,a.2) := by
  have hhh : Continuous (fun p : (transverse e × ℝ) × ℝ => weight volume κ e (measurableEquiv e (p.1.1,p.2))) :=
    ((continuous_weight volume hκ hκ1 e).comp (continuous_measurableEquiv e)).comp (continuous_fst.fst.prodMk continuous_snd)
  have hdd : Continuous (fun p : (transverse e × ℝ) × ℝ => d (measurableEquiv e (p.1.1,p.2))) :=
    (continuous_d.comp (continuous_measurableEquiv e)).comp (continuous_fst.fst.prodMk continuous_snd)
  unfold LayerPressure.sourceWeight LayerPressure.lineWeight
  have hre := relative_componentWeight_eq (coordinate_layer_open e hf) hhh hdd δ ((a.1.1,a.2),a.1.2)
  dsimp only at hre
  refine (congrArg ENNReal.toReal hre).symm.trans ?_
  unfold lineWeight
  congr 1
  apply componentWeight_congr_section
  · intro s
    simp only [relativeLayer,parameterLayer,lineLayer,mem_ofPred_eq,Function.comp_apply,parallel]
  · intro s
    simp only [parallel]
  · intro s
    simp only [parallel]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma coordinate_sourceLower (e : sphere (0:E) 1) (f : E → ℝ) (a : (transverse e × ℝ) × ℝ) :
    measurableEquiv e (LayerPressure.sourceLower (f ∘ measurableEquiv e) a) =
      lowerPoint f (e,measurableEquiv e a.1,a.2) := by
  have he : backwardExit (relativeLayer (parameterLayer (f ∘ measurableEquiv e))) ((a.1.1,a.2),a.1.2) =
      backwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2) := by
    apply backwardExit_congr_section
    intro s
    simp only [relativeLayer,parameterLayer,lineLayer,mem_ofPred_eq,Function.comp_apply,parallel]
  unfold LayerPressure.sourceLower lowerEndpoint lowerPoint lowerOffset
  rw [he]
  simpa only [sub_eq_add_neg] using parallel e a.1 (-(backwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2)).toReal)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma coordinate_sourceUpper (e : sphere (0:E) 1) (f : E → ℝ) (a : (transverse e × ℝ) × ℝ) :
    measurableEquiv e (LayerPressure.sourceUpper (f ∘ measurableEquiv e) a) =
      upperPoint f (e,measurableEquiv e a.1,a.2) := by
  have he : forwardExit (relativeLayer (parameterLayer (f ∘ measurableEquiv e))) ((a.1.1,a.2),a.1.2) =
      forwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2) := by
    apply forwardExit_congr_section
    intro s
    simp only [relativeLayer,parameterLayer,lineLayer,mem_ofPred_eq,Function.comp_apply,parallel]
  unfold LayerPressure.sourceUpper upperEndpoint upperPoint upperOffset
  rw [he]
  exact parallel e a.1 ((forwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2)).toReal)

end HenonLaneEmden.SpatialComponents
end
end SpatialPressure

end OAI
