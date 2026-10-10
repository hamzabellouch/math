import OAI.Probability.InvariantIsing.Cavity.CavityHaarPriorMoment
import OAI.Probability.InvariantIsing.Cavity.CavitySampledBlocks

namespace OAI

/-! The measurable physical cavity model, with original disorder and fresh
Haar frames outside the replica prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityHaarSpinPriorKernel {Ω X U : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace U] {k : ℕ}
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (π : Measure (Spin k)) [IsProbabilityMeasure π] : Kernel (Ω × U) (X × Spin k) :=
  let νK := Kernel.mk ν hν
  let : IsMarkovKernel νK := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  (νK.comap Prod.fst measurable_fst).prod (Kernel.const _ π)

@[simp] lemma cavityHaarSpinPriorKernel_apply {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U] {k : ℕ}
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (p : Ω × U) :
    cavityHaarSpinPriorKernel ν hν π p = (ν p.1).prod π := by
  let νK : Kernel Ω X := Kernel.mk ν hν
  let : IsMarkovKernel νK := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  change (νK.comap Prod.fst measurable_fst).prod (Kernel.const (Ω × U) π) p = _
  rw [Kernel.prod_apply]
  rfl

instance cavityHaarSpinPriorKernel_isMarkov {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U] {k : ℕ}
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    IsMarkovKernel (cavityHaarSpinPriorKernel (U := U) ν hν π) := by
  constructor
  intro p
  rw [cavityHaarSpinPriorKernel_apply]
  infer_instance

def cavityHaarSpinPotential {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) : ℝ :=
  cavityLogFactor K L C
    (cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2.1) p.2.2

lemma measurable_cavityHaarSpinPotential {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) :
    Measurable (cavityHaarSpinPotential e v A₀ K L C) := by
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun z : Ω × ((a : Fin m) → Orthogonal (N a)) =>
    cavityLogFactor K L C (cavitySelectedSiteProjection e (v z.1)
      (cavityGroupHaarFrames A₀ z.2) x.1) x.2)
  exact (continuous_cavityLogFactor K L C x.2).measurable.comp
    ((measurable_cavitySelectedSiteProjection e v hv A₀).comp
      (measurable_id.prodMk (show Measurable (fun _ => x.1) from measurable_const)))

def cavityHaarSpinReplicaTest {m r k : ℕ} {Ω X U : Type*}
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (p : (Ω × U) × (Fin r → X × Spin k)) : ℝ :=
  cavityProjectedSpinTest (B p.1.1) F p.2

lemma measurable_cavityHaarSpinReplicaTest {m r k : ℕ} {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    [Countable X] [MeasurableSingletonClass X]
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityHaarSpinReplicaTest (U := U) B F) := by
  apply measurable_from_prod_countable_left
  intro σ
  change Measurable (fun z : Ω × U => F (B z.1 (fun i => (σ i).1), fun i => (σ i).2))
  exact F.continuous.measurable.comp
    (((hB (fun i => (σ i).1)).comp measurable_fst).prodMk
      (show Measurable (fun _ : Ω × U => fun i => (σ i).2) from measurable_const))

lemma cavityHaarSpinReplicaTest_bound {m r k : ℕ} {Ω X U : Type*}
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (p : (Ω × U) × (Fin r → X × Spin k)) :
    |cavityHaarSpinReplicaTest B F p| ≤ ‖F‖ := by
  exact (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _)

end InvariantIsing

end

end OAI
