import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinModel
import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCapIntegral

namespace OAI

/-! Product-disorder integration for physical Haar spin numerators. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_haar_spin_replica_integral {m q d k r : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, ∫ U, cavityWeightedReplicaMean ((ν ω).prod π)
      (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C ((ω,U),x)) T))
      (cavityProjectedSpinTest (B ω) F) ∂Measure.pi μ ∂P) =
    ∫ p, cavityWeightedReplicaMean ((ν p.1).prod π)
      (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C (p,x)) T))
      (cavityProjectedSpinTest (B p.1) F) ∂P.prod (Measure.pi μ) := by
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N a)) ν hν π
  let V := fun z => min (cavityHaarSpinPotential e v A₀ K L C z) T
  have hV : Measurable V := (measurable_cavityHaarSpinPotential e v hv A₀ K L C).min measurable_const
  have he p : Integrable (fun x => Real.exp (V (p,x))) (κ p) :=
    integrable_of_measurable_abs_le ((hV.comp measurable_prodMk_left).exp)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hi := cavity_exp_replicaMean_integrable (P.prod (Measure.pi μ)) κ κ.measurable V hV
    (cavityHaarSpinReplicaTest B F) (measurable_cavityHaarSpinReplicaTest B hB F)
    (ae_of_all _ he) (fun p σ => cavityHaarSpinReplicaTest_bound B F (p,σ))
  simpa only [κ, V, cavityHaarSpinPriorKernel_apply, cavityHaarSpinReplicaTest] using
    (integral_prod _ hi).symm

lemma cavity_haar_spin_numerator_integral {m q d k r : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, ∫ U, cavityWeightNumerator ((ν ω).prod π)
      (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C ((ω,U),x)) T))
      (cavityProjectedSpinTest (B ω) F) ∂Measure.pi μ ∂P) =
    ∫ p, cavityWeightNumerator ((ν p.1).prod π)
      (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C (p,x)) T))
      (cavityProjectedSpinTest (B p.1) F) ∂P.prod (Measure.pi μ) := by
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N a)) ν hν π
  have hm := measurable_cavityWeightNumerator κ κ.measurable
    (fun p => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C p) T))
    (((measurable_cavityHaarSpinPotential e v hv A₀ K L C).min measurable_const).exp)
    (cavityHaarSpinReplicaTest B F) (measurable_cavityHaarSpinReplicaTest B hB F)
  have hb (p : Ω × ((a : Fin m) → Orthogonal (N a))) :
      |cavityWeightNumerator (κ p)
        (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C (p,x)) T))
        (fun σ => cavityHaarSpinReplicaTest B F (p,σ))| ≤ ‖F‖ * (Real.exp T)^r :=
    cavityWeightNumerator_abs_le (κ p) _ _ (Real.exp_pos T).le (norm_nonneg F)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
      (fun σ => cavityHaarSpinReplicaTest_bound B F (p,σ))
  have hi := Integrable.of_bound (μ := P.prod (Measure.pi μ)) hm.aestronglyMeasurable
    (‖F‖ * (Real.exp T)^r) (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p)
  simpa only [κ, cavityHaarSpinPriorKernel_apply, cavityHaarSpinReplicaTest] using
    (integral_prod _ hi).symm

lemma cavity_group_gram_diagonal_norm {m : ℕ} {N : Fin m → ℕ}
    (hN : ∀ a, 0 < N a) (v : (a : Fin m) → Fin (N a) → ℝ) {C : ℝ}
    (hv : ∀ a, |cavityGroupReplicaGram (fun a (_ : Fin 1) => v a) a 0 0| ≤ C) :
    ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a := by
  intro a
  have hn : 0 < (N a : ℝ) := Nat.cast_pos.mpr (hN a)
  have h := (le_abs_self _).trans (hv a)
  have he : cavityGroupReplicaGram (fun a (_ : Fin 1) => v a) a 0 0 =
      ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 / (N a : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [cavityGroupReplicaGram, pow_two]
  rw [he] at h
  exact (div_le_iff₀ hn).mp h

end InvariantIsing

end

end OAI
