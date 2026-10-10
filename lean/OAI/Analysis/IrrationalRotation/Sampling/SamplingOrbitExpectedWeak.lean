import OAI.Analysis.IrrationalRotation.Sampling.SamplingOrbitWeak
import OAI.Analysis.IrrationalRotation.Sampling.ProductInfiniteSamplingMoments

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.SamplingCylinderWeak

theorem tendsto_eLpNorm_of_toLp_norm
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ℕ → X → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (h : Tendsto (fun n => ‖(hf n).toLp (f n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_iff
    (fun n => (hf n).eLpNorm_ne_top) ENNReal.zero_ne_top).mp
  simpa only [Lp.norm_toLp, ENNReal.toReal_zero] using h

end Invariant233.SamplingCylinderWeak

namespace Invariant233.ProductModel.TailTrimming
open SamplingCylinderWeak

theorem ae_all_triangular_orbitAverage_weaklyConverges_of_expected_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (θ : Ω → ℕ → ℝ) (N : ℕ → Finset ℕ)
    (w : Finset ℕ → Ω → ℕ → ℕ → Base → ℝ)
    (hw : ∀ I ω l, ∀ n ∈ N l, Measurable (w I ω l n))
    (hw0 : ∀ I ω l, ∀ n ∈ N l, ∀ x, 0 ≤ w I ω l n x)
    (g : Finset ℕ → CylinderTest (Bool × ℕ) → ℕ → Base → ℝ)
    (hg : ∀ I t l, MemLp (g I t l) 2 baseMeasure)
    (b : Finset ℕ → CylinderTest (Bool × ℕ) → ℕ → ℝ)
    (hmeas : ∀ I t l, AEStronglyMeasurable
      (fun p : Ω × Base =>
        cylinderTestAverage (θ p.1) (N l) (w I p.1 l) t p.2 - g I t l p.2)
      (P.prod baseMeasure))
    (hsq : ∀ I t l, Integrable
      (fun p : Ω × Base =>
        (cylinderTestAverage (θ p.1) (N l) (w I p.1 l) t p.2 - g I t l p.2)^2)
      (P.prod baseMeasure))
    (hbound : ∀ I t, ∀ᶠ l in atTop,
      (∫ ω, ∫ x,
        (cylinderTestAverage (θ ω) (N l) (w I ω l) t x - g I t l x)^2
        ∂baseMeasure ∂P) ≤ b I t l)
    (hb : ∀ I t, Summable (b I t))
    (hideal : ∀ I t, Tendsto (fun l => ∫ x, g I t l x ∂baseMeasure) atTop
      (𝓝 ((triangularLaw I).real (endpointCylinder t)))) :
    ∀ᵐ ω ∂P, ∀ I, WeaklyConverges
      (fun l => orbitAverageMeasure (θ ω) (N l)
        (fun n x => ENNReal.ofReal (w I ω l n x))) (triangularLaw I) := by
  let F : (Finset ℕ × CylinderTest (Bool × ℕ)) → ℕ → Ω → Base → ℝ :=
    fun it l ω x =>
      cylinderTestAverage (θ ω) (N l) (w it.1 ω l) it.2 x - g it.1 it.2 l x
  have hall := ProductSampling.ae_all_memLp_and_tendsto_norm_of_eventually_expected_sq
    F (fun it => b it.1 it.2)
    (fun it => hmeas it.1 it.2) (fun it => hsq it.1 it.2)
    (fun it => hbound it.1 it.2) (fun it => hb it.1 it.2)
  filter_upwards [hall] with ω hω
  intro I
  have hf (t : CylinderTest (Bool × ℕ)) (l : ℕ) :
      MemLp (cylinderTestAverage (θ ω) (N l) (w I ω l) t) 2 baseMeasure := by
    obtain ⟨he, _, _⟩ := hω (I, t)
    have h := (he l).add (hg I t l)
    change MemLp ((cylinderTestAverage (θ ω) (N l) (w I ω l) t - g I t l) +
      g I t l) 2 baseMeasure at h
    simpa only [sub_add_cancel] using h
  have herr (t : CylinderTest (Bool × ℕ)) :
      Tendsto (fun l => eLpNorm
        (fun x => cylinderTestAverage (θ ω) (N l) (w I ω l) t x - g I t l x)
        2 baseMeasure) atTop (𝓝 0) := by
    obtain ⟨he, _, hconv⟩ := hω (I, t)
    exact tendsto_eLpNorm_of_toLp_norm (fun l => F (I, t) l ω) he hconv
  have hν : IsFiniteMeasure (triangularLaw I) := by
    unfold triangularLaw
    infer_instance
  exact orbitAverage_weaklyConverges_of_tested_L2 (θ ω) N (w I ω)
    (hw I ω) (hw0 I ω) (g I) hf (hg I) hν herr (hideal I)

end Invariant233.ProductModel.TailTrimming

end

end OAI
