import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.Piecewise
import OAI.Geometry.WeakHessian.Sobolev.AddConst
import OAI.Geometry.WeakHessian.LocalBounds.TriangularFold

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakGradient_triangularFold_of_measurable (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) (hfm : Measurable f) {δ : ℝ} (hδ : 0 < δ) :
    weakGradient m (triangularFold δ ∘ f) =ᵐ[m] weakGradient m f := by
  have hF := hf.normalContraction hfinite (triangularFold_lipschitz δ) (triangularFold_zero δ)
  have hFm := (triangularFold_lipschitz δ).continuous.measurable.comp hfm
  have hp (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = f x - δ*(k:ℝ) →
      weakGradient m (triangularFold δ ∘ f) x = weakGradient m f x := by
    have hv := hf.2.1.add_const hfinite (-δ*(k:ℝ))
    have hh := weakGradient_locality hF.2.1 hv
      (measurableSet_eq_fun hFm (hfm.add_const (-δ*(k:ℝ)))) (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,weakGradient_add_const_of_exists hf.2.1.2 (-δ*(k:ℝ))] with x hx he ht
    exact (hx (by simpa only [Function.comp_apply, sub_eq_add_neg, neg_mul] using ht)).trans he
  have hm (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = -(f x - δ*(k:ℝ)) →
      weakGradient m (triangularFold δ ∘ f) x = weakGradient m f x := by
    have hv := (hf.2.1.const_mul (-1)).add_const hfinite (δ*(k:ℝ))
    have hh := weakGradient_locality hF.2.1 hv
      (measurableSet_eq_fun hFm ((hfm.const_mul (-1)).add_const (δ*(k:ℝ))))
      (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,weakGradient_add_const_of_exists (hf.2.1.const_mul (-1)).2 (δ*(k:ℝ)),
      weakGradient_const_mul (m := m) (-1) f] with x hx he hn ht
    have H := hx (by simp only [Function.comp_apply]; linarith [ht])
    simpa only [he, hn, abs_neg, abs_one, one_mul] using H
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hm] with x hp hm
  obtain ⟨k,h|h⟩ := triangularFold_piecewise hδ (f x)
  · exact hp k h
  · exact hm k h

lemma weakGradient_triangularFold (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) {δ : ℝ} (hδ : 0 < δ) :
    weakGradient m (triangularFold δ ∘ f) =ᵐ[m] weakGradient m f := by
  let f' := hf.1.aestronglyMeasurable.mk f
  have he : f =ᵐ[m] f' := hf.1.aestronglyMeasurable.ae_eq_mk
  have hf' : Sobolev m f' := (sobolev_congr_ae he).mp hf
  have H := weakGradient_triangularFold_of_measurable hfinite hf'
    hf.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable hδ
  exact (weakGradient_congr_ae (he.fun_comp (triangularFold δ))).trans
    (H.trans (weakGradient_congr_ae he).symm)

def gradientPairSum (m : Measure X) (f g : X → ℝ) (x : X) : ℝ :=
  weakGradient m (fun y => f y + g y) x ^ 2 +
  weakGradient m (fun y => f y - g y) x ^ 2

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gradientPairSum_symm (f g : X → ℝ) :
    gradientPairSum m f g =ᵐ[m] gradientPairSum m g f := by
  filter_upwards [weakGradient_const_mul (m := m) (-1) (fun x => f x-g x)] with x hx
  have hplus : (fun x => f x+g x) = (fun x => g x+f x) := by funext x; ring
  have hminus : (fun x => -1*(f x-g x)) = (fun x => g x-f x) := by funext x; ring
  simp only [gradientPairSum, hplus, hminus, abs_neg, abs_one, one_mul] at hx ⊢
  rw [hx]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gradientPairSum_neg_left (f g : X → ℝ) :
    gradientPairSum m (fun x => -f x) g =ᵐ[m] gradientPairSum m f g := by
  have hp : (fun x => -1*(f x-g x)) = (fun x => -f x+g x) := by funext x; ring
  have hm : (fun x => -1*(f x+g x)) = (fun x => -f x-g x) := by funext x; ring
  filter_upwards [weakGradient_const_mul (m := m) (-1) (fun x => f x-g x),
      weakGradient_const_mul (m := m) (-1) (fun x => f x+g x)] with x h1 h2
  simp only [hp, hm, abs_neg, abs_one, one_mul] at h1 h2
  unfold gradientPairSum
  rw [h1, h2]
  exact add_comm _ _

lemma gradientPairSum_add_const_left (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    gradientPairSum m (fun x => f x+c) g =ᵐ[m] gradientPairSum m f g := by
  have hp : (fun x => (f x + g x)+c) = (fun x => (f x+c)+g x) := by funext x; ring
  have hm : (fun x => (f x - g x)+c) = (fun x => (f x+c)-g x) := by funext x; ring
  have hn : LocalSobolev m (fun x => -g x) := by simpa using hg.const_mul (-1)
  filter_upwards [weakGradient_add_const_of_exists (hf.add hfinite hg).2 c,
      weakGradient_add_const_of_exists (hf.add hfinite hn).2 c] with x h1 h2
  simp only [← sub_eq_add_neg] at h2
  rw [hp] at h1
  rw [hm] at h2
  simp only [gradientPairSum, h1, h2]

lemma gradientPairSum_locality_left (hfinite : FiniteOnBoundedSets m)
    {f u g : X → ℝ} (hf : LocalSobolev m f) (hu : LocalSobolev m u)
    (hg : LocalSobolev m g) {s : Set X} (hs : MeasurableSet s)
    (he : ∀ᵐ x ∂m, x ∈ s → f x = u x) :
    ∀ᵐ x ∂m, x ∈ s → gradientPairSum m f g x = gradientPairSum m u g x := by
  have hn : LocalSobolev m (fun x => -g x) := by simpa using hg.const_mul (-1)
  have hp := weakGradient_locality (hf.add hfinite hg) (hu.add hfinite hg) hs
    (he.mono fun x hx hm => by rw [hx hm])
  have hm := weakGradient_locality (hf.add hfinite hn) (hu.add hfinite hn) hs
    (he.mono fun x hx hm => by rw [hx hm])
  simp only [← sub_eq_add_neg] at hm
  filter_upwards [hp,hm] with x hp hm hx
  simp only [gradientPairSum, hp hx, hm hx]

lemma gradientPairSum_fold_left_of_measurable (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) (hfm : Measurable f)
    {δ : ℝ} (hδ : 0 < δ) :
    gradientPairSum m (triangularFold δ ∘ f) g =ᵐ[m] gradientPairSum m f g := by
  have hF := hf.normalContraction hfinite (triangularFold_lipschitz δ) (triangularFold_zero δ)
  have hFm := (triangularFold_lipschitz δ).continuous.measurable.comp hfm
  have hp (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = f x - δ*(k:ℝ) →
      gradientPairSum m (triangularFold δ ∘ f) g x = gradientPairSum m f g x := by
    have hv := hf.2.1.add_const hfinite (-δ*(k:ℝ))
    have hh := gradientPairSum_locality_left hfinite hF.2.1 hv hg.2.1
      (measurableSet_eq_fun hFm (hfm.add_const (-δ*(k:ℝ)))) (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,gradientPairSum_add_const_left hfinite hf.2.1 hg.2.1 (-δ*(k:ℝ))]
      with x hx he ht
    exact (hx (by simpa only [Function.comp_apply, sub_eq_add_neg, neg_mul] using ht)).trans he
  have hm (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = -(f x - δ*(k:ℝ)) →
      gradientPairSum m (triangularFold δ ∘ f) g x = gradientPairSum m f g x := by
    have hn : LocalSobolev m (fun x => -f x) := by simpa using hf.2.1.const_mul (-1)
    have hv := hn.add_const hfinite (δ*(k:ℝ))
    have hh := gradientPairSum_locality_left hfinite hF.2.1 hv hg.2.1
      (measurableSet_eq_fun hFm (hfm.neg.add_const (δ*(k:ℝ)))) (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,gradientPairSum_add_const_left hfinite hn hg.2.1 (δ*(k:ℝ)),
      gradientPairSum_neg_left (m := m) f g] with x hx he hn ht
    exact (hx (by
      change triangularFold δ (f x) = -f x + δ*(k : ℝ)
      linarith [ht])).trans (he.trans hn)
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hm] with x hp hm
  obtain ⟨k,h|h⟩ := triangularFold_piecewise hδ (f x)
  · exact hp k h
  · exact hm k h

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gradientPairSum_congr_ae {f f' g g' : X → ℝ} (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') :
    gradientPairSum m f g =ᵐ[m] gradientPairSum m f' g' := by
  filter_upwards [weakGradient_congr_ae (hf.add hg),weakGradient_congr_ae (hf.sub hg)]
    with x h1 h2
  change weakGradient m (fun y => f y+g y) x = weakGradient m (fun y => f' y+g' y) x at h1
  change weakGradient m (fun y => f y-g y) x = weakGradient m (fun y => f' y-g' y) x at h2
  unfold gradientPairSum
  rw [h1,h2]

lemma gradientPairSum_fold_left (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {δ : ℝ} (hδ : 0 < δ) :
    gradientPairSum m (triangularFold δ ∘ f) g =ᵐ[m] gradientPairSum m f g := by
  let f' := hf.1.aestronglyMeasurable.mk f
  have he : f =ᵐ[m] f' := hf.1.aestronglyMeasurable.ae_eq_mk
  have H := gradientPairSum_fold_left_of_measurable hfinite ((sobolev_congr_ae he).mp hf) hg
    hf.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable hδ
  exact (gradientPairSum_congr_ae (he.fun_comp (triangularFold δ)) EventuallyEq.rfl).trans
    (H.trans (gradientPairSum_congr_ae he EventuallyEq.rfl).symm)

lemma gradientPairSum_fold (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {δ : ℝ} (hδ : 0 < δ) :
    gradientPairSum m (triangularFold δ ∘ f) (triangularFold δ ∘ g) =ᵐ[m]
      gradientPairSum m f g := by
  have hG := hg.normalContraction hfinite (triangularFold_lipschitz δ) (triangularFold_zero δ)
  exact (gradientPairSum_fold_left hfinite hf hG hδ).trans
    ((gradientPairSum_symm f (triangularFold δ ∘ g)).trans
    ((gradientPairSum_fold_left hfinite hg hf hδ).trans (gradientPairSum_symm g f)))

end WeakHessian

end
end InlinedFile0

end OAI
