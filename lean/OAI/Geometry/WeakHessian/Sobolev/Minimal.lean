import Mathlib
import OAI.Geometry.WeakHessian.Transport.AeActionData
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLp
import OAI.Geometry.WeakHessian.LocalBounds.MulBounded
import OAI.Geometry.WeakHessian.Measure.AeMinimumDominated

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.exists_minimal {f D₀ : X → ℝ}
    (hD₀ : IsLocalWeakUpperGradient m f D₀) (hf : AEMeasurable f m)
    (hfinite : FiniteOnBoundedSets m) :
    ∃ D, IsMinimalLocalWeakUpperGradient m f D := by
  let B : X → ℝ := fun x => max 0 (D₀ x)
  have hBnon : ∀ x, 0 ≤ B x := fun _ => le_max_left _ _
  have heq : D₀ =ᵐ[m] B := by
    filter_upwards [hD₀.2.1] with x hx
    exact (max_eq_right hx).symm
  have hB : IsLocalWeakUpperGradient m f B :=
    hD₀.congr_ae Filter.EventuallyEq.rfl heq
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hfinite _ Metric.isBounded_ball⟩⟩
  obtain ⟨μ, hμ, hmμ, hμm⟩ := exists_isFiniteMeasure_absolutelyContinuous m
  let : IsFiniteMeasure μ := hμ
  obtain ⟨ν, hμν, hνμ, hBi⟩ := WeakHessianCalculus.exists_equivalent_integrable_measure μ
    (hB.1.aemeasurable.mono_ac hμm)
  have hmν : m ≪ ν := hmμ.trans hμν
  have hνm : ν ≪ m := hνμ.trans hμm
  let S : Set (X → ℝ) := {D | IsLocalWeakUpperGradient m f D ∧ ∀ x, 0 ≤ D x ∧ D x ≤ B x}
  have hS : S.Nonempty := ⟨B,hB, fun x => ⟨hBnon x, le_rfl⟩⟩
  have hSm : ∀ D ∈ S, AEMeasurable D ν :=
    fun _ hD => hD.1.1.aemeasurable.mono_ac hνm
  have hSmin : ∀ D ∈ S, ∀ E ∈ S, (fun x => Min.min (D x) (E x)) ∈ S := by
    intro D hD E hE
    exact ⟨hD.1.min_measurable hE.1 hf, fun x => ⟨le_min (hD.2 x).1 (hE.2 x).1,
      (min_le_left _ _).trans (hD.2 x).2⟩⟩
  have hSclosed : ∀ u : ℕ → X → ℝ, (∀ n, u n ∈ S) → ∀ D : X → ℝ,
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (D x))) → D ∈ S := by
    intro u hu D hlim
    have hDb : ∀ x, 0 ≤ D x ∧ D x ≤ B x := fun x =>
      ⟨ge_of_tendsto (hlim x) (Eventually.of_forall fun n => ((hu n).2 x).1),
        le_of_tendsto (hlim x) (Eventually.of_forall fun n => ((hu n).2 x).2)⟩
    have hDm : AEStronglyMeasurable D m :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (hu n).1.1.aemeasurable.aestronglyMeasurable) (ae_of_all _ hlim)
    have hDL : LocallyL2 m D := by
      intro o R hR
      apply (hB.1 o R hR).mono' hDm.restrict
      exact ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hDb x).1,
          abs_of_nonneg (hBnon x)] using (hDb x).2
    exact ⟨IsLocalWeakUpperGradient.of_dominated_ae_tendsto (fun n => (hu n).1) hDL hB.1
      (fun n => ae_of_all _ fun x => ((hu n).2 x).2) (ae_of_all _ hlim), hDb⟩
  obtain ⟨D,hD,hDmin⟩ := WeakHessianCalculus.exists_ae_minimum_dominated ν S B hBi
    hS hSm (fun _ h => h.2) hSmin hSclosed
  refine ⟨D,hD.1,?_⟩
  intro E hE
  let E' : X → ℝ := fun x => max 0 (Min.min (D x) (E x))
  have hEq : (fun x => Min.min (D x) (E x)) =ᵐ[m] E' := by
    filter_upwards [hE.2.1] with x hx
    exact (max_eq_right (le_min (hD.2 x).1 hx)).symm
  have hE' : E' ∈ S := by
    refine ⟨(hD.1.min_measurable hE hf).congr_ae Filter.EventuallyEq.rfl hEq, fun x => ?_⟩
    exact ⟨le_max_left _ _, max_le (hBnon x) ((min_le_left _ _).trans (hD.2 x).2)⟩
  filter_upwards [hmν.ae_le (hDmin E' hE'), hEq] with x hx heq
  exact hx.trans (heq ▸ min_le_right (D x) (E x))

lemma localSobolev_iff_exists_upperGradient (hfinite : FiniteOnBoundedSets m) {f : X → ℝ} :
    LocalSobolev m f ↔ LocallyL2 m f ∧ ∃ D, IsLocalWeakUpperGradient m f D := by
  constructor
  · rintro ⟨hf,D,hD⟩
    exact ⟨hf,D,hD.1⟩
  · rintro ⟨hf,D,hD⟩
    exact ⟨hf,hD.exists_minimal hf.aemeasurable hfinite⟩


lemma LocalSobolev.add (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    LocalSobolev m (fun x => f x + g x) := by
  apply (localSobolev_iff_exists_upperGradient hfinite).mpr
  exact ⟨hf.1.add hg.1, _, (weakGradient_isMinimal hf.2).1.add (weakGradient_isMinimal hg.2).1 hf.1⟩

lemma weakGradient_add_le (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, weakGradient m (fun x => f x + g x) x ≤
      weakGradient m f x + weakGradient m g x :=
  (weakGradient_isMinimal (hf.add hfinite hg).2).2 _
    ((weakGradient_isMinimal hf.2).1.add (weakGradient_isMinimal hg.2).1 hf.1)

lemma Sobolev.of_upperGradient (hfinite : FiniteOnBoundedSets m) {f D : X → ℝ}
    (hf : MemLp f 2 m) (hD : IsLocalWeakUpperGradient m f D) (hD₂ : MemLp D 2 m) :
    Sobolev m f := by
  have hmin := hD.exists_minimal hf.aestronglyMeasurable.aemeasurable hfinite
  refine ⟨hf, ⟨fun o R _ => hf.restrict (Metric.ball o R), hmin⟩, ?_⟩
  have hw := weakGradient_isMinimal hmin
  apply hD₂.mono hw.1.1.aestronglyMeasurable
  filter_upwards [hw.2 _ hD,hw.1.2.1,hD.2.1] with x hx hwx hDx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hwx, abs_of_nonneg hDx] using hx

lemma Sobolev.add (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : Sobolev m f) (hg : Sobolev m g) : Sobolev m (fun x => f x + g x) :=
  Sobolev.of_upperGradient hfinite (hf.1.add hg.1)
    ((weakGradient_isMinimal hf.2.1.2).1.add (weakGradient_isMinimal hg.2.1.2).1 hf.2.1.1)
    (hf.2.2.add hg.2.2)

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalSobolev.const_mul {f : X → ℝ} (hf : LocalSobolev m f) (c : ℝ) :
    LocalSobolev m (fun x => c * f x) :=
by
  refine ⟨hf.1.const_mul c, ?_⟩
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul] using ⟨_, isMinimalLocalWeakUpperGradient_const (m := m) 0⟩
  · exact ⟨_, (weakGradient_isMinimal hf.2).const_mul hc⟩

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma Sobolev.const_mul {f : X → ℝ} (hf : Sobolev m f) (c : ℝ) :
    Sobolev m (fun x => c * f x) :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c,
    (hf.2.2.const_mul |c|).ae_eq (weakGradient_const_mul c f).symm⟩

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma Sobolev.neg {f : X → ℝ} (hf : Sobolev m f) : Sobolev m (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

lemma Sobolev.sub (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : Sobolev m f) (hg : Sobolev m g) : Sobolev m (fun x => f x - g x) :=
  hf.add hfinite hg.neg

lemma Sobolev.mul_bounded (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : Sobolev m f) (hg : LocalSobolev m g)
    {A B : ℝ} (hgB : ∀ᵐ x ∂m, |g x| ≤ A)
    (hEB : ∀ᵐ x ∂m, |weakGradient m g x| ≤ B) :
    Sobolev m (fun x => f x * g x) := by
  apply Sobolev.of_upperGradient hfinite (memLp_mul_bounded hf.1 hg.1.aestronglyMeasurable hgB)
    ((weakGradient_isMinimal hf.2.1.2).1.mul_bounded (weakGradient_isMinimal hg.2).1
      hf.2.1.1 hg.1.aemeasurable hgB hEB)
  have hD : MemLp (fun x => |g x| * weakGradient m f x) 2 m := by
    simpa only [mul_comm, Real.norm_eq_abs] using memLp_mul_bounded hf.2.2 hg.1.aestronglyMeasurable.norm
      (by simpa only [Real.norm_eq_abs,abs_abs] using hgB)
  have hE : MemLp (fun x => |f x| * weakGradient m g x) 2 m :=
    memLp_mul_bounded (by simpa only [Real.norm_eq_abs] using hf.1.norm)
      (weakGradient_isMinimal hg.2).1.1.aestronglyMeasurable hEB
  exact hD.add hE

end WeakHessian

end

end OAI
