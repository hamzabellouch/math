import OAI.Probability.InvariantIsing.Cavity.CavityHaarNumeratorAverage
import OAI.Probability.InvariantIsing.Cavity.CavityProjectedRestrictedNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityDisorderPrefix

namespace OAI

/-! The physical hard-restricted numerator is the fresh-Haar test under the
infinite replica law, retaining the common original disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityRestrictedHaarReplicaValue {m r q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (Fin r → X) =>
      cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F
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
  exact (measurable_cavityRestrictedSpinReplicaValue K L C τ hBcut (cavitySelectedGroupProjection e) π F).comp
    (((hB σ).comp measurable_fst).prodMk hg)

theorem cavity_haar_restricted_spin_numerator_average {m r q d k : ℕ} {N : Fin m → ℕ}
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
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, ∫ U, cavityWeightNumerator ((ν ω).prod π)
      (fun x => if 1+‖cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ U) x.1‖^2 ≤ 1+Bcut^2 then
        Real.exp (min (cavityLogFactor K L C
          (cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ U) x.1) x.2) τ) else 0)
      (cavityProjectedSpinTest (B ω) F) ∂Measure.pi μ ∂P) =
    ∫ z, ∫ U, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F
      (B z.1 (fun i : Fin r => z.2 i),
        cavityGroupMatrixProjection (fun a i => v z.1 a (z.2 i)) (cavityGroupHaarFrames A₀ U))
      ∂Measure.pi μ ∂disorderReplicaLaw P ν hν := by
  let G := fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (Fin r → X) =>
    cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F
      (B p.1.1 p.2, cavityGroupMatrixProjection (fun a i => v p.1.1 a (p.2 i))
        (cavityGroupHaarFrames A₀ p.1.2))
  have hG : Measurable G := measurable_cavityRestrictedHaarReplicaValue
    (m := m) (r := r) (q := q) (d := d) (k := k) (N := N) (Ω := Ω) (X := X)
    A₀ B hB e v hv K L C τ hBcut π F
  have hb (p) : ‖G p‖ ≤ (Real.exp τ)^r * ‖F‖ :=
    cavityRestrictedSpinReplicaValue_bound K L C τ hBcut (cavitySelectedGroupProjection e) π F _
  have hswap := cavity_disorder_replica_prefix_swap_raw (Ω := Ω) (X := X)
    (U := (a : Fin m) → Orthogonal (N a)) (r := r) P ν hν (Measure.pi μ) G hG hb
  calc
    _ = ∫ ω, ∫ U, ∫ σ : Fin r → X, G ((ω, U), σ)
        ∂Measure.pi (fun _ => ν ω) ∂Measure.pi μ ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun U =>
        cavity_projected_restricted_spin_numerator (m := m) (r := r) (q := q) (d := d) (k := k)
          (N := N) (X := X) (ν ω) (B ω) e (v ω)
          (cavityGroupHaarFrames A₀ U) K L C τ Bcut π F)
    _ = _ := hswap

end InvariantIsing

end

end OAI
