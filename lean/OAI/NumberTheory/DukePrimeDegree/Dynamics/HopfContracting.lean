import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfPairs
import OAI.NumberTheory.DukePrimeDegree.Geometry.CompactAction

namespace OAI

/-!
# Contracting group translations in the Hopf argument

Two orbit points may leave every compact set. It is enough that their
relative group translation tends to the identity: every compactly
supported observable then has vanishing oscillation, and L¹ approximation
identifies invariant observables along the pair.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {G X Z : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [UniformSpace X] [T2Space X] [NormalSpace X]
  [WeaklyLocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z]

omit [T2Space X] [NormalSpace X] [WeaklyLocallyCompactSpace X] in
lemma integral_compact_observable_of_contracting_pairs
    (nu : Measure Z) [IsFiniteMeasure nu]
    (p q : ℕ → Z → X) (hp : ∀ n, Measurable (p n)) (hq : ∀ n, Measurable (q n))
    (a : ℕ → Z → G)
    (ha : ∀ᵐ z ∂nu, Tendsto (fun n => a n z) atTop (𝓝 1))
    (hpair : ∀ᵐ z ∂nu, ∀ n, q n z = a n z • p n z)
    (g : X → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun n => ∫ z, |g (p n z) - g (q n z)| ∂nu) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hg
  have hlim : ∀ᵐ z ∂nu,
      Tendsto (fun n => |g (p n z) - g (q n z)|) atTop (𝓝 0) := by
    filter_upwards [ha, hpair] with z hz hpz
    have h := compact_observable_moving_smul_difference g hg hc
      (fun n => p n z) (fun n => a n z) hz
    simpa only [hpz, abs_sub_comm] using h
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z => |g (p n z) - g (q n z)|) nu := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_apply] using
      ((hg.measurable.comp (hp n)).sub
        (hg.measurable.comp (hq n))).norm.aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ z ∂nu, ‖|g (p n z) - g (q n z)|‖ ≤ 2 * C := by
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |g (p n z) - g (q n z)| ≤ |g (p n z)| + |g (q n z)| := abs_sub _ _
      _ ≤ C + C := add_le_add (hC _) (hC _)
      _ = 2 * C := by ring
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _ : Z => 2 * C) hm
      (integrable_const _) hb hlim

/-- The measurable stable-pair conclusion follows from contraction in
the acting group, with no compactness assumption on the orbit points. -/
theorem ae_eq_of_contracting_translation_pairs
    (μ : Measure X) [μ.Regular] (nu : Measure Z) [IsFiniteMeasure nu]
    (p q : ℕ → Z → X) (hp : ∀ n, Measurable (p n)) (hq : ∀ n, Measurable (q n))
    (hpμ : ∀ n, nu.map (p n) ≤ μ) (hqμ : ∀ n, nu.map (q n) ≤ μ)
    (a : ℕ → Z → G)
    (ha : ∀ᵐ z ∂nu, Tendsto (fun n => a n z) atTop (𝓝 1))
    (hpair : ∀ᵐ z ∂nu, ∀ n, q n z = a n z • p n z)
    (f : X → ℝ) (hf : Integrable f μ)
    (hfp : ∀ n, (fun z => f (p n z)) =ᵐ[nu] fun z => f (p 0 z))
    (hfq : ∀ n, (fun z => f (q n z)) =ᵐ[nu] fun z => f (q 0 z)) :
    (fun z => f (p 0 z)) =ᵐ[nu] fun z => f (q 0 z) :=
  ae_eq_of_compact_observable_dominated_pairs μ nu p q hp hq hpμ hqμ
    (fun g hg hc => integral_compact_observable_of_contracting_pairs
      nu p q hp hq a ha hpair g hg hc) f hf hfp hfq

end DukePrimeDegree

end OAI
