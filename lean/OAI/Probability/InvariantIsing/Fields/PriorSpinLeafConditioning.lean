import OAI.Probability.InvariantIsing.Arrays.NSpinTensorPairConditioning

namespace OAI

/-! Conditional independent spin sampling for a finite constrained prior.
The prior is retained in both its terminal and its conditional spin kernels. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal NNReal

namespace InvariantIsing

def priorSpinLeafTerminal {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (H : Spin N × LabeledLeaf n → ℝ) (α : LabeledLeaf n) : ℝ :=
  finiteLogIntegral μ (fun σ => H (σ, α))

lemma exp_priorSpinLeafTerminal {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (H : Spin N × LabeledLeaf n → ℝ) (α : LabeledLeaf n) :
    Real.exp (priorSpinLeafTerminal μ H α) =
      referencePartition μ (fun σ => H (σ, α)) := by
  exact Real.exp_log (integral_exp_pos (Integrable.of_finite))

lemma priorSpinLeafPartition_eq {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν)) :
    referencePartition (μ.prod ν) H =
      referencePartition ν (priorSpinLeafTerminal μ H) := by
  unfold referencePartition
  rw [integral_prod_symm _ he]
  apply integral_congr_ae
  exact ae_of_all _ fun α => (exp_priorSpinLeafTerminal μ H α).symm

lemma priorSpinLeafTerminal_exp_integrable {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν)) :
    Integrable (fun α => Real.exp (priorSpinLeafTerminal μ H α)) ν := by
  convert he.integral_prod_right using 1
  ext α
  exact exp_priorSpinLeafTerminal μ H α

lemma priorSpinLeafGibbs_singleton {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (σ : Spin N) (α : LabeledLeaf n) :
    gibbsProbability (μ.prod ν) H {(σ, α)} =
      gibbsProbability ν (priorSpinLeafTerminal μ H) {α} *
        gibbsProbability μ (fun τ => H (τ, α)) {σ} := by
  have hi := priorSpinLeafTerminal_exp_integrable μ ν H he
  have hs : Integrable (fun τ : Spin N => Real.exp (H (τ, α)))
      μ := Integrable.of_finite
  have hZ : 0 < referencePartition ν (priorSpinLeafTerminal μ H) := integral_exp_pos hi
  have hS : 0 < referencePartition μ (fun τ => H (τ, α)) :=
    integral_exp_pos hs
  rw [gibbsProbability_eq_tilted _ _ he, gibbsProbability_eq_tilted _ _ hi,
    gibbsProbability_eq_tilted _ _ hs, tilted_singleton, tilted_singleton, tilted_singleton,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    priorSpinLeafPartition_eq μ ν H he, exp_priorSpinLeafTerminal]
  have hc :
      ENNReal.ofReal (Real.exp (H (σ, α)) / referencePartition ν (priorSpinLeafTerminal μ H)) =
        ENNReal.ofReal
          (referencePartition μ (fun τ => H (τ, α)) /
            referencePartition ν (priorSpinLeafTerminal μ H)) *
          ENNReal.ofReal
            (Real.exp (H (σ, α)) /
              referencePartition μ (fun τ => H (τ, α))) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hS.le hZ.le)]
    congr 1
    field_simp
  rw [hc]
  ac_rfl

def priorSpinLeafPairResidualKernel {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (H : Spin N × LabeledLeaf n → ℝ) :
    Kernel (Fin 2 → LabeledLeaf n) (Fin 2 → Spin N) :=
  ⟨fun α => Measure.pi (fun i : Fin 2 =>
      gibbsProbability μ (fun σ => H (σ, α i))),
    measurable_of_countable _⟩

instance priorSpinLeafPairResidualKernel_markov {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (H : Spin N × LabeledLeaf n → ℝ) :
    IsMarkovKernel (priorSpinLeafPairResidualKernel μ H) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

def priorSpinLeafPairJoin {N n : ℕ}
    (p : (Fin 2 → LabeledLeaf n) × (Fin 2 → Spin N)) : Fin 2 → Spin N × LabeledLeaf n :=
  fun i => (p.2 i, p.1 i)

lemma measurable_priorSpinLeafPairJoin {N n : ℕ} :
    Measurable (priorSpinLeafPairJoin (N := N) (n := n)) := by
  unfold priorSpinLeafPairJoin
  fun_prop

/-- Conditional on the two leaf labels, the spin residual draws are
independent, including when the leaf labels coincide. -/
theorem priorSpinLeafPairLaw {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν)) :
    ((Measure.pi (fun _ : Fin 2 => gibbsProbability ν (priorSpinLeafTerminal μ H))) ⊗ₘ
      priorSpinLeafPairResidualKernel μ H).map priorSpinLeafPairJoin =
      Measure.pi (fun _ : Fin 2 => gibbsProbability (μ.prod ν) H) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply measurable_priorSpinLeafPairJoin (measurableSet_singleton _)]
  have hp : priorSpinLeafPairJoin ⁻¹' {x} =
      {(fun i => (x i).2, fun i => (x i).1)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply Prod.ext
      · funext i
        exact congrArg Prod.snd (congrFun h i)
      · funext i
        exact congrArg Prod.fst (congrFun h i)
    · intro h
      subst p
      rfl
  rw [hp, ← Set.singleton_prod_singleton, Measure.compProd_apply_prod
    (measurableSet_singleton _) (measurableSet_singleton _), lintegral_singleton]
  change (Measure.pi (fun i : Fin 2 =>
      gibbsProbability μ (fun σ => H (σ, (x i).2))))
      {fun i => (x i).1} *
        (Measure.pi (fun _ : Fin 2 => gibbsProbability ν (priorSpinLeafTerminal μ H)))
          {fun i => (x i).2} = _
  simp only [Measure.pi_singleton]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm]
  exact (priorSpinLeafGibbs_singleton μ ν H he (x i).1 (x i).2).symm

theorem priorSpinLeafPair_conditioning {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (D : (Fin 2 → Spin N × LabeledLeaf n) → ℝ)
    (hD : ∃ C : ℝ, ∀ x, |D x| ≤ C) :
    referenceReplicaMean (μ.prod ν) H D =
      referenceReplicaMean ν (priorSpinLeafTerminal μ H)
        (fun α => ∫ σ, D (priorSpinLeafPairJoin (α, σ)) ∂priorSpinLeafPairResidualKernel μ H α) := by
  have hmD : Measurable D := measurable_of_countable _
  have hiD : Integrable D
      (Measure.pi (fun _ : Fin 2 =>
        gibbsProbability (μ.prod ν) H)) := by
    obtain ⟨C, hC⟩ := hD
    exact integrable_of_measurable_abs_le hmD hC
  have hp : MeasurePreserving priorSpinLeafPairJoin
      ((Measure.pi (fun _ : Fin 2 => gibbsProbability ν (priorSpinLeafTerminal μ H))) ⊗ₘ
        priorSpinLeafPairResidualKernel μ H)
      (Measure.pi (fun _ : Fin 2 =>
        gibbsProbability (μ.prod ν) H)) :=
    ⟨measurable_priorSpinLeafPairJoin, priorSpinLeafPairLaw μ ν H he⟩
  have hcomp := hp.hasLaw.integrable_comp hiD
  rw [referenceReplicaMean_eq_tilted _ _ he, ← gibbsProbability_eq_tilted _ _ he,
    referenceReplicaMean_eq_tilted _ _ (priorSpinLeafTerminal_exp_integrable μ ν H he),
    ← gibbsProbability_eq_tilted _ _ (priorSpinLeafTerminal_exp_integrable μ ν H he)]
  rw [← hp.hasLaw.integral_comp hmD.aestronglyMeasurable]
  exact integral_compProd hcomp

end InvariantIsing

end

end OAI
