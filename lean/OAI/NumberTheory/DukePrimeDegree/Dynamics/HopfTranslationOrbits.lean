import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfContracting
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalPairs

namespace OAI

/-!
# Contracting translations of conditional pairs

The Hopf argument applies to forward iterates whenever their relative
translation contracts in the acting group. This formulation also works
for measurable observables with a countably separated target.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {G X Z : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [UniformSpace X] [T2Space X] [NormalSpace X]
  [WeaklyLocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z]

theorem ae_eq_of_contracting_pair_orbits
    (μ : Measure X) [μ.Regular] (nu : Measure Z) [IsFiniteMeasure nu]
    (r s : Z → X) (hr : Measurable r) (hs : Measurable s)
    (hrμ : nu.map r ≤ μ) (hsμ : nu.map s ≤ μ)
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (a : ℕ → Z → G)
    (ha : ∀ᵐ z ∂nu, Tendsto (fun n => a n z) atTop (𝓝 1))
    (hpair : ∀ᵐ z ∂nu, ∀ n, T^[n] (s z) = a n z • T^[n] (r z))
    (f : X → ℝ) (hf : Integrable f μ)
    (hfinv : (fun x => f (T x)) =ᵐ[μ] f) :
    (fun z => f (r z)) =ᵐ[nu] fun z => f (s z) := by
  have hi (n : ℕ) : (fun x => f (T^[n] x)) =ᵐ[μ] f := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh : ∀ᵐ x ∂μ, f (T^[n] (T x)) = f (T x) := by
        exact ae_of_ae_map hT.measurable.aemeasurable
          (p := fun x => f (T^[n] x) = f x) (by rwa [hT.map_eq])
      filter_upwards [hh, hfinv] with x hx h0
      simpa only [Function.iterate_succ_apply] using hx.trans h0
  have hmap (r : Z → X) (hr : Measurable r) (hrμ : nu.map r ≤ μ) (n : ℕ) :
      nu.map (fun z => T^[n] (r z)) ≤ μ := by
    change nu.map (T^[n] ∘ r) ≤ μ
    rw [← Measure.map_map (hT.iterate n).measurable hr]
    exact (Measure.map_mono hrμ (hT.iterate n).measurable).trans_eq (hT.iterate n).map_eq
  have hfix (r : Z → X) (hr : Measurable r) (hrμ : nu.map r ≤ μ) (n : ℕ) :
      (fun z => f (T^[n] (r z))) =ᵐ[nu] fun z => f (T^[0] (r z)) := by
    exact ae_of_ae_map hr.aemeasurable
      (p := fun x => f (T^[n] x) = f x) (ae_mono hrμ (hi n))
  have h := ae_eq_of_contracting_translation_pairs μ nu
    (fun n z => T^[n] (r z)) (fun n z => T^[n] (s z))
    (fun n => (hT.iterate n).measurable.comp hr)
    (fun n => (hT.iterate n).measurable.comp hs)
    (hmap r hr hrμ) (hmap s hs hsμ) a ha hpair f hf
    (hfix r hr hrμ) (hfix s hs hsμ)
  simpa only [Function.iterate_zero, id_eq] using h

/-- The actual conditional kernel version of the translation criterion. -/
theorem ae_conditional_eq_of_contracting_orbits
    {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (μ : Measure X) [μ.Regular]
    (ρ : Measure (S × B)) [IsFiniteMeasure ρ]
    (R : S × B → X) (hR : Measurable R) (hRμ : ρ.map R ≤ μ)
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (a : ℕ → ((S × B) × B) → G)
    (ha : ∀ᵐ z ∂conditionalPairMeasure ρ,
      Tendsto (fun n => a n z) atTop (𝓝 1))
    (hpair : ∀ᵐ z ∂conditionalPairMeasure ρ, ∀ n,
      T^[n] (R (z.1.1, z.2)) = a n z • T^[n] (R z.1))
    (f : X → ℝ) (hf : Integrable f μ)
    (hfinv : (fun x => f (T x)) =ᵐ[μ] f) :
    ∀ᵐ z ∂ρ, ∀ᵐ t ∂ρ.condKernel z.1, f (R z) = f (R (z.1, t)) := by
  have hl : (conditionalPairMeasure ρ).map (fun z => R z.1) ≤ μ := by
    rw [map_conditionalPair_left ρ R hR]
    exact hRμ
  have hr : (conditionalPairMeasure ρ).map (fun z => R (z.1.1, z.2)) ≤ μ := by
    rw [map_conditionalPair_right ρ R hR]
    exact hRμ
  have hh := ae_eq_of_contracting_pair_orbits μ (conditionalPairMeasure ρ)
    (fun z => R z.1) (fun z => R (z.1.1, z.2))
    (hR.comp measurable_fst) (by fun_prop) hl hr T hT a ha hpair f hf hfinv
  exact Measure.ae_ae_of_ae_compProd
    (μ := ρ) (κ := ρ.condKernel.comap Prod.fst measurable_fst)
    (p := fun z : (S × B) × B => f (R z.1) = f (R (z.1.1, z.2))) hh

end DukePrimeDegree

end OAI
