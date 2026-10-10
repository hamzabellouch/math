import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.AmbientGram

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma space_finiteDimensional (d : ℕ) : FiniteDimensional ℝ (Space d) := by
  infer_instance

section WeightedImage
variable {X : Type*} [MeasurableSpace X] {d m N : ℕ}

def WeightedBlock (ι : X → Space d) (h : Fin N → X → ℝ≥0∞)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := @WithLp.measurableSpace exponent (Fin d → ℝ) inferInstance
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  @MeasureTheory.lintegral (Fin m → Space d) rowMeasurable
    (@Measure.pi (Fin m) (fun _ => Space d) inferInstance (fun _ => euclideanMeasurable)
      (fun _ => @stdGaussian (Space d)
        (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
        (space_finiteDimensional d) euclideanMeasurable))
    (fun rows => ∑ state, g state (rows, fun index => @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      (ι x) (rows index)) * h state x)

lemma measurable_weightedBlock {ι : X → Space d} (hι : Measurable ι)
    {h : Fin N → X → ℝ≥0∞} (hh : ∀ w, Measurable (h w))
    {g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞}
    (hg : ∀ w, Measurable (g w)) : Measurable (WeightedBlock ι h g) := by
  apply Measurable.lintegral_prod_left
  exact Finset.measurable_sum _ (fun w _ => ((hg w).comp (by fun_prop)).mul ((hh w).comp measurable_snd))

omit [MeasurableSpace X] in
lemma weightedBlock_le_one (ι : X → Space d) {h : Fin N → X → ℝ≥0∞}
    (hh1 : ∀ w x, h w x ≤ 1)
    {g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞}
    (hg1 : ∀ x, ∑ w, g w x ≤ 1) (x : X) : WeightedBlock ι h g x ≤ 1 := by
  unfold WeightedBlock
  calc
    _ ≤ ∫⁻ _A : Fin m → Space d, (1:ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian (Space d)) := by
      apply lintegral_mono
      intro A
      exact (Finset.sum_le_sum (fun w _ => mul_le_of_le_one_right' (hh1 w x))).trans (hg1 _)
    _ = 1 := by simp

lemma weighted_image_finite (μ : Measure X) [IsFiniteMeasure μ] (ι : X → Space d)
    (h : X → ℝ≥0∞) (hh1 : ∀ x, h x ≤ 1) :
    IsFiniteMeasure ((μ.withDensity h).map ι) := by
  let := isFiniteMeasure_withDensity (μ := μ) (ne_of_lt ((lintegral_mono hh1).trans_lt (by simp)))
  infer_instance

lemma weighted_image_ball (μ : Measure X) {ι : X → Space d} (hι : Measurable ι)
    (h : X → ℝ≥0∞) (z : Space d) (r : ℝ) :
    (μ.withDensity h).map ι (Metric.closedBall z r) =
      ∫⁻ x in {x | dist (ι x) z ≤ r}, h x ∂μ := by
  rw [Measure.map_apply hι Metric.isClosed_closedBall.measurableSet,
    withDensity_apply _ (hι Metric.isClosed_closedBall.measurableSet)]
  rfl

lemma projectionLaw_lintegral (ν : Measure (Space d)) [SFinite ν]
    (g : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂projectionLaw ν m) =
      ∫⁻ s, ∫⁻ A, g (A,fun j => ⟪s,A j⟫)
        ∂Measure.pi (fun _ : Fin m => stdGaussian (Space d)) ∂ν := by
  have hobs : Measurable (fun x : (Fin m → Space d) × Space d => g (x.1,fun j => ⟪x.2,x.1 j⟫)) :=
    hg.comp (by fun_prop)
  rw [projectionLaw, lintegral_map hg (by fun_prop)]
  exact lintegral_prod_symm _ hobs.aemeasurable

lemma weightedBlock_mass_identity (μ : Measure X) [IsFiniteMeasure μ]
    {ι : X → Space d} (hι : Measurable ι)
    {h : Fin N → X → ℝ≥0∞} (hh : ∀ w, Measurable (h w)) (hh1 : ∀ w x, h w x ≤ 1)
    {g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞}
    (hg : ∀ w, Measurable (g w)) {B : Set (Space d)} (hB : MeasurableSet B) :
    (∫⁻ x in ι ⁻¹' B, WeightedBlock ι h g x ∂μ) =
      ∑ w, ∫⁻ x, g w x ∂projectionLaw (((μ.withDensity (h w)).map ι).restrict B) m := by
  classical
  let (w : Fin N) : IsFiniteMeasure (μ.withDensity (h w)) :=
    isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 w)).trans_lt (by simp)))
  let G (w : Fin N) (x : X) (A : Fin m → Space d) := g w (A, fun j => ⟪ι x,A j⟫) * h w x
  have hG (w) : Measurable (Function.uncurry (G w)) :=
    ((hg w).comp (by fun_prop)).mul ((hh w).comp measurable_fst)
  have he (w) : (∫⁻ u, g w u ∂projectionLaw (((μ.withDensity (h w)).map ι).restrict B) m) =
      ∫⁻ x in ι ⁻¹' B, ∫⁻ A, G w x A
        ∂Measure.pi (fun _ : Fin m => stdGaussian (Space d)) ∂μ := by
    have hobs : Measurable (fun x : (Fin m → Space d) × Space d =>
        g w (x.1,fun j => ⟪x.2,x.1 j⟫)) := (hg w).comp (by fun_prop)
    have htech : Measurable (fun x : (Fin m → Space d) × X =>
        g w (x.1,fun j => ⟪ι x.2,x.1 j⟫)) := (hg w).comp (by fun_prop)
    rw [projectionLaw_lintegral _ _ (hg w), Measure.restrict_map hι hB,
      lintegral_map hobs.lintegral_prod_left hι,
      restrict_withDensity (hι hB), lintegral_withDensity_eq_lintegral_mul _ (hh w)
        htech.lintegral_prod_left]
    apply lintegral_congr
    intro x
    simp only [Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ (ne_of_lt ((hh1 w x).trans_lt (by simp)))]
    apply lintegral_congr
    intro A
    exact mul_comm _ _
  simp_rw [he]
  rw [← lintegral_finsetSum _ (fun w _ => (hG w).lintegral_prod_right)]
  apply lintegral_congr
  intro x
  unfold WeightedBlock
  exact lintegral_finsetSum _ (fun w _ => (hG w).comp (measurable_const.prodMk measurable_id))
end WeightedImage
end MemoryPrecision


end

end OAI
