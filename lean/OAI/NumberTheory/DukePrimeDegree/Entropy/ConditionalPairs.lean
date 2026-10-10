import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfPairs
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

namespace OAI

/-!
# Pairs sampled from a conditional measure

Resampling the second coordinate from its conditional distribution
preserves both coordinate marginals. These pairs let the Hopf principle
apply inside a foliation chart, with both ambient marginals dominated
by the original finite invariant measure.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Uniformity

namespace DukePrimeDegree

variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

/-- Keep the transverse coordinate and independently resample the leaf
coordinate using its conditional law. -/
noncomputable def conditionalPairMeasure (ρ : Measure (S × B)) [IsFiniteMeasure ρ] :
    Measure ((S × B) × B) :=
  ρ ⊗ₘ ρ.condKernel.comap Prod.fst measurable_fst

instance (ρ : Measure (S × B)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (conditionalPairMeasure ρ) := by
  unfold conditionalPairMeasure
  infer_instance

lemma conditionalPairMeasure_left (ρ : Measure (S × B)) [IsFiniteMeasure ρ] :
    (conditionalPairMeasure ρ).map Prod.fst = ρ := by
  exact Measure.fst_compProd ρ _

lemma conditionalPairMeasure_right (ρ : Measure (S × B)) [IsFiniteMeasure ρ] :
    (conditionalPairMeasure ρ).map (fun z => (z.1.1, z.2)) = ρ := by
  ext A hA
  have hm : Measurable (fun z : (S × B) × B => (z.1.1, z.2)) := by fun_prop
  rw [Measure.map_apply hm hA, conditionalPairMeasure,
    Measure.compProd_apply (hA.preimage hm)]
  change (∫⁻ z : S × B, ρ.condKernel z.1 (Prod.mk z.1 ⁻¹' A) ∂ρ) = ρ A
  calc
    _ = ∫⁻ s, ρ.condKernel s (Prod.mk s ⁻¹' A) ∂ρ.fst :=
      (lintegral_map (Kernel.measurable_kernel_prodMk_left hA) measurable_fst).symm
    _ = (ρ.fst ⊗ₘ ρ.condKernel) A := (Measure.compProd_apply hA).symm
    _ = ρ A := by rw [Measure.disintegrate]

lemma map_conditionalPair_left {α : Type*} [MeasurableSpace α]
    (ρ : Measure (S × B)) [IsFiniteMeasure ρ]
    (R : S × B → α) (hR : Measurable R) :
    (conditionalPairMeasure ρ).map (fun z => R z.1) = ρ.map R := by
  change (conditionalPairMeasure ρ).map (R ∘ Prod.fst) = ρ.map R
  rw [← Measure.map_map hR measurable_fst, conditionalPairMeasure_left]

lemma map_conditionalPair_right {α : Type*} [MeasurableSpace α]
    (ρ : Measure (S × B)) [IsFiniteMeasure ρ]
    (R : S × B → α) (hR : Measurable R) :
    (conditionalPairMeasure ρ).map (fun z => R (z.1.1, z.2)) = ρ.map R := by
  let r : (S × B) × B → S × B := fun z => (z.1.1, z.2)
  have hr : Measurable r := by fun_prop
  change (conditionalPairMeasure ρ).map (R ∘ r) = ρ.map R
  rw [← Measure.map_map hR hr]
  exact congrArg (Measure.map R) (conditionalPairMeasure_right ρ)

/-- An ambient almost-everywhere property holds at both sampled points. -/
lemma ae_conditionalPair_of_ambient (ρ : Measure (S × B)) [IsFiniteMeasure ρ]
    {P : S × B → Prop} (hP : ∀ᵐ z ∂ρ, P z) :
    ∀ᵐ z ∂conditionalPairMeasure ρ, P z.1 ∧ P (z.1.1, z.2) := by
  have hleft : ∀ᵐ z ∂conditionalPairMeasure ρ, P z.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rwa [conditionalPairMeasure_left]
  have hright : ∀ᵐ z ∂conditionalPairMeasure ρ, P (z.1.1, z.2) := by
    apply ae_of_ae_map (by fun_prop :
      Measurable (fun z : (S × B) × B => (z.1.1, z.2))).aemeasurable
    rwa [conditionalPairMeasure_right]
  exact hleft.and hright

/-- A chart whose same-fiber point pairs become asymptotic carries
constant conditional values for every integrable invariant observable.
The conclusion is with respect to the actual conditional kernel. -/
theorem ae_conditionalPair_eq_of_asymptotic_orbits
    {α : Type*} [UniformSpace α] [T2Space α] [NormalSpace α]
    [WeaklyLocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [μ.Regular]
    (ρ : Measure (S × B)) [IsFiniteMeasure ρ]
    (R : S × B → α) (hR : Measurable R) (hRμ : ρ.map R ≤ μ)
    (T : α → α) (hT : MeasurePreserving T μ μ)
    (hasymptotic : ∀ᵐ z ∂conditionalPairMeasure ρ,
      Tendsto (fun n => (T^[n] (R z.1), T^[n] (R (z.1.1, z.2)))) atTop (𝓤 α))
    (f : α → ℝ) (hf : Integrable f μ) (hfinv : (fun x => f (T x)) =ᵐ[μ] f) :
    ∀ᵐ z ∂conditionalPairMeasure ρ, f (R z.1) = f (R (z.1.1, z.2)) := by
  have hl : (conditionalPairMeasure ρ).map (fun z => R z.1) ≤ μ := by
    rw [map_conditionalPair_left ρ R hR]
    exact hRμ
  have hr : (conditionalPairMeasure ρ).map (fun z => R (z.1.1, z.2)) ≤ μ := by
    rw [map_conditionalPair_right ρ R hR]
    exact hRμ
  have hh := ae_eq_of_asymptotic_pair_orbits μ (conditionalPairMeasure ρ)
    (fun z => R z.1) (fun z => R (z.1.1, z.2))
    (hR.comp measurable_fst) (by fun_prop) hl hr T hT hasymptotic f hf hfinv
  exact hh


theorem ae_conditional_eq_of_asymptotic_orbits
    {α : Type*} [UniformSpace α] [T2Space α] [NormalSpace α]
    [WeaklyLocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [μ.Regular]
    (ρ : Measure (S × B)) [IsFiniteMeasure ρ]
    (R : S × B → α) (hR : Measurable R) (hRμ : ρ.map R ≤ μ)
    (T : α → α) (hT : MeasurePreserving T μ μ)
    (hasymptotic : ∀ᵐ z ∂conditionalPairMeasure ρ,
      Tendsto (fun n => (T^[n] (R z.1), T^[n] (R (z.1.1, z.2)))) atTop (𝓤 α))
    (f : α → ℝ) (hf : Integrable f μ) (hfinv : (fun x => f (T x)) =ᵐ[μ] f) :
    ∀ᵐ z ∂ρ, ∀ᵐ t ∂ρ.condKernel z.1, f (R z) = f (R (z.1, t)) := by
  have hh := ae_conditionalPair_eq_of_asymptotic_orbits μ ρ R hR hRμ T hT
    hasymptotic f hf hfinv
  exact Measure.ae_ae_of_ae_compProd
    (μ := ρ) (κ := ρ.condKernel.comap Prod.fst measurable_fst)
    (p := fun z : (S × B) × B => f (R z.1) = f (R (z.1.1, z.2))) hh

end DukePrimeDegree

end OAI
