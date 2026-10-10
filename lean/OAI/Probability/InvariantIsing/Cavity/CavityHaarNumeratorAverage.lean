import OAI.Probability.InvariantIsing.Cavity.CavityProjectedSpinNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityDisorderPrefix

namespace OAI

/-! The physical capped numerator is the fresh-Haar test under the
infinite replica law, retaining the common original disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityGroupMatrixProjection_uncurry {m r q : ℕ} (N : Fin m → ℕ) :
    Measurable (fun p : ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
      ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) => cavityGroupMatrixProjection p.1 p.2) := by
  let : OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)) :=
    inferInstanceAs (OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Fin (N a) → Fin q → ℝ)))
  have hc : Continuous (fun p : ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
      ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) => cavityGroupMatrixProjection p.1 p.2) := by
    unfold cavityGroupMatrixProjection
    fun_prop
  exact hc.measurable

lemma measurable_cavityCappedHaarReplicaValue {m r q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (Fin r → X) =>
      cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F
        (B p.1.1 p.2, cavityGroupMatrixProjection (fun a i => v p.1.1 a (p.2 i))
          (cavityGroupHaarFrames A₀ p.1.2))) := by
  apply measurable_from_prod_countable_left
  intro σ
  have hvec : Measurable (fun ω : Ω => fun a i => v ω a (σ i)) :=
    Measurable.of_eval fun a => Measurable.of_eval fun i => (measurable_pi_apply a).comp (hv (σ i))
  have hg : Measurable (fun p : Ω × ((a : Fin m) → Orthogonal (N a)) =>
      cavityGroupMatrixProjection (fun a i => v p.1 a (σ i)) (cavityGroupHaarFrames A₀ p.2)) :=
    (measurable_cavityGroupMatrixProjection_uncurry N).comp
      ((hvec.comp measurable_fst).prodMk
        ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))
  exact (continuous_cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F).measurable.comp
    (((hB σ).comp measurable_fst).prodMk hg)

theorem cavity_haar_spin_numerator_average {m r q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, ∫ U, cavityWeightNumerator ((ν ω).prod π)
      (fun x => Real.exp (min (cavityLogFactor K L C
        (cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ U) x.1) x.2) τ))
      (cavityProjectedSpinTest (B ω) F) ∂Measure.pi μ ∂P) =
    ∫ z, ∫ U, cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F
      (B z.1 (fun i : Fin r => z.2 i),
        cavityGroupMatrixProjection (fun a i => v z.1 a (z.2 i)) (cavityGroupHaarFrames A₀ U))
      ∂Measure.pi μ ∂disorderReplicaLaw P ν hν := by
  let G := fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (Fin r → X) =>
    cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F
      (B p.1.1 p.2, cavityGroupMatrixProjection (fun a i => v p.1.1 a (p.2 i))
        (cavityGroupHaarFrames A₀ p.1.2))
  have hG : Measurable G := measurable_cavityCappedHaarReplicaValue
    (m := m) (r := r) (q := q) (d := d) (k := k) (N := N) (Ω := Ω) (X := X)
    A₀ B hB e v hv K L C τ π F
  have hb (p) : ‖G p‖ ≤ (Real.exp τ)^r * ‖F‖ :=
    cavityCappedSpinReplicaValue_bound K L C τ (cavitySelectedGroupProjection e) π F _
  have hswap := cavity_disorder_replica_prefix_swap_raw (Ω := Ω) (X := X)
    (U := (a : Fin m) → Orthogonal (N a)) (r := r) P ν hν (Measure.pi μ) G hG hb
  calc
    _ = ∫ ω, ∫ U, ∫ σ : Fin r → X, G ((ω, U), σ)
        ∂Measure.pi (fun _ => ν ω) ∂Measure.pi μ ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun U =>
        cavity_projected_spin_numerator (m := m) (r := r) (q := q) (d := d) (k := k)
          (N := N) (X := X) (ν ω) (B ω) e (v ω)
          (cavityGroupHaarFrames A₀ U) K L C τ π F)
    _ = _ := hswap

end InvariantIsing

end

end OAI
