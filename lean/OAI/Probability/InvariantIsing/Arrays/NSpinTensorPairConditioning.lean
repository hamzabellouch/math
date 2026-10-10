import OAI.Probability.InvariantIsing.Arrays.NSpinTensorAncestorInput

namespace OAI

/-! Conditional independent spin residuals at two sampled cascade leaves. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal NNReal

namespace InvariantIsing

def spinLeafTerminal {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) (α : LabeledLeaf n) : ℝ :=
  finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) (fun σ => H (σ, α))

lemma exp_spinLeafTerminal {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) (α : LabeledLeaf n) :
    Real.exp (spinLeafTerminal H α) =
      referencePartition (uniformSpinPrior N : Measure (Spin N)) (fun σ => H (σ, α)) := by
  exact Real.exp_log (integral_exp_pos (Integrable.of_finite))

lemma spinLeafPartition_eq {N n : ℕ} (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ((uniformSpinPrior N : Measure (Spin N)).prod ν)) :
    referencePartition ((uniformSpinPrior N : Measure (Spin N)).prod ν) H =
      referencePartition ν (spinLeafTerminal H) := by
  unfold referencePartition
  rw [integral_prod_symm _ he]
  apply integral_congr_ae
  exact ae_of_all _ fun α => (exp_spinLeafTerminal H α).symm

lemma spinLeafTerminal_exp_integrable {N n : ℕ} (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ((uniformSpinPrior N : Measure (Spin N)).prod ν)) :
    Integrable (fun α => Real.exp (spinLeafTerminal H α)) ν := by
  convert he.integral_prod_right using 1
  ext α
  exact exp_spinLeafTerminal H α

lemma spinLeafGibbs_singleton {N n : ℕ} (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ((uniformSpinPrior N : Measure (Spin N)).prod ν))
    (σ : Spin N) (α : LabeledLeaf n) :
    gibbsProbability ((uniformSpinPrior N : Measure (Spin N)).prod ν) H {(σ, α)} =
      gibbsProbability ν (spinLeafTerminal H) {α} *
        gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fun τ => H (τ, α)) {σ} := by
  have hi := spinLeafTerminal_exp_integrable ν H he
  have hs : Integrable (fun τ : Spin N => Real.exp (H (τ, α)))
      (uniformSpinPrior N : Measure (Spin N)) := Integrable.of_finite
  have hZ : 0 < referencePartition ν (spinLeafTerminal H) := integral_exp_pos hi
  have hS : 0 < referencePartition (uniformSpinPrior N : Measure (Spin N)) (fun τ => H (τ, α)) :=
    integral_exp_pos hs
  rw [gibbsProbability_eq_tilted _ _ he, gibbsProbability_eq_tilted _ _ hi,
    gibbsProbability_eq_tilted _ _ hs, tilted_singleton, tilted_singleton, tilted_singleton,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    spinLeafPartition_eq ν H he, exp_spinLeafTerminal]
  have hc :
      ENNReal.ofReal (Real.exp (H (σ, α)) / referencePartition ν (spinLeafTerminal H)) =
        ENNReal.ofReal
          (referencePartition (uniformSpinPrior N : Measure (Spin N)) (fun τ => H (τ, α)) /
            referencePartition ν (spinLeafTerminal H)) *
          ENNReal.ofReal
            (Real.exp (H (σ, α)) /
              referencePartition (uniformSpinPrior N : Measure (Spin N)) (fun τ => H (τ, α))) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hS.le hZ.le)]
    congr 1
    field_simp
  rw [hc]
  ac_rfl

def spinLeafPairResidualKernel {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) :
    Kernel (Fin 2 → LabeledLeaf n) (Fin 2 → Spin N) :=
  ⟨fun α => Measure.pi (fun i : Fin 2 =>
      gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fun σ => H (σ, α i))),
    measurable_of_countable _⟩

instance spinLeafPairResidualKernel_markov {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) :
    IsMarkovKernel (spinLeafPairResidualKernel H) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

def spinLeafPairJoin {N n : ℕ}
    (p : (Fin 2 → LabeledLeaf n) × (Fin 2 → Spin N)) : Fin 2 → Spin N × LabeledLeaf n :=
  fun i => (p.2 i, p.1 i)

lemma measurable_spinLeafPairJoin {N n : ℕ} :
    Measurable (spinLeafPairJoin (N := N) (n := n)) := by
  unfold spinLeafPairJoin
  fun_prop

/-- Conditional on the two leaf labels, the spin residual draws are
independent, including when the leaf labels coincide. -/
theorem spinLeafPairLaw {N n : ℕ} (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ((uniformSpinPrior N : Measure (Spin N)).prod ν)) :
    ((Measure.pi (fun _ : Fin 2 => gibbsProbability ν (spinLeafTerminal H))) ⊗ₘ
      spinLeafPairResidualKernel H).map spinLeafPairJoin =
      Measure.pi (fun _ : Fin 2 => gibbsProbability ((uniformSpinPrior N : Measure (Spin N)).prod ν) H) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply measurable_spinLeafPairJoin (measurableSet_singleton _)]
  have hp : spinLeafPairJoin ⁻¹' {x} =
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
      gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fun σ => H (σ, (x i).2))))
      {fun i => (x i).1} *
        (Measure.pi (fun _ : Fin 2 => gibbsProbability ν (spinLeafTerminal H)))
          {fun i => (x i).2} = _
  simp only [Measure.pi_singleton]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm]
  exact (spinLeafGibbs_singleton ν H he (x i).1 (x i).2).symm

theorem spinLeafPair_conditioning {N n : ℕ} (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ((uniformSpinPrior N : Measure (Spin N)).prod ν))
    (D : (Fin 2 → Spin N × LabeledLeaf n) → ℝ)
    (hD : ∃ C : ℝ, ∀ x, |D x| ≤ C) :
    referenceReplicaMean ((uniformSpinPrior N : Measure (Spin N)).prod ν) H D =
      referenceReplicaMean ν (spinLeafTerminal H)
        (fun α => ∫ σ, D (spinLeafPairJoin (α, σ)) ∂spinLeafPairResidualKernel H α) := by
  have hmD : Measurable D := measurable_of_countable _
  have hiD : Integrable D
      (Measure.pi (fun _ : Fin 2 =>
        gibbsProbability ((uniformSpinPrior N : Measure (Spin N)).prod ν) H)) := by
    obtain ⟨C, hC⟩ := hD
    exact integrable_of_measurable_abs_le hmD hC
  have hp : MeasurePreserving spinLeafPairJoin
      ((Measure.pi (fun _ : Fin 2 => gibbsProbability ν (spinLeafTerminal H))) ⊗ₘ
        spinLeafPairResidualKernel H)
      (Measure.pi (fun _ : Fin 2 =>
        gibbsProbability ((uniformSpinPrior N : Measure (Spin N)).prod ν) H)) :=
    ⟨measurable_spinLeafPairJoin, spinLeafPairLaw ν H he⟩
  have hcomp := hp.hasLaw.integrable_comp hiD
  rw [referenceReplicaMean_eq_tilted _ _ he, ← gibbsProbability_eq_tilted _ _ he,
    referenceReplicaMean_eq_tilted _ _ (spinLeafTerminal_exp_integrable ν H he),
    ← gibbsProbability_eq_tilted _ _ (spinLeafTerminal_exp_integrable ν H he)]
  rw [← hp.hasLaw.integral_comp hmD.aestronglyMeasurable]
  exact integral_compProd hcomp

def tensorLeafSpinHamiltonian {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n)
    (s : Spin N × LabeledLeaf n) : ℝ :=
  tensorSpinBaseEnergy eig U c I degree amplitude
    (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) s.2 z) s.1

lemma tensorLeafSpinHamiltonian_eq_coordinates {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n)
    (s : Spin N × LabeledLeaf n) :
    tensorLeafSpinHamiltonian eig U c I degree amplitude n z p s =
      tensorLabeledEnergy eig U c I degree amplitude n z
        (tensorEnergyCoordinates U I degree amplitude n p) s := by
  have hmarks : spinTensorEnergy U I degree amplitude
      (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) s.2 z) s.1 =
      spinTensorEnergy U I degree amplitude z s.1 +
        ∑ i : Fin n, spinTensorEnergy U I degree amplitude (p.2 (edgeAt n s.2 i)) s.1 := by
    unfold spinTensorEnergy
    simp only [labeledEnergy_edge_sum, add_mul, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  change rotatedEnergy eig U s.1 + fieldEnergy c s.1 + _ =
    rotatedEnergy eig U s.1 + fieldEnergy c s.1 + _ + _
  rw [hmarks]
  dsimp only [tensorEnergyCoordinates]
  ring

theorem tensorLeafSpin_exp_integrable_ae {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ∀ᵐ p ∂tensorCoordinateLaw I degree n b v,
      Integrable (fun s => Real.exp (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p s))
        ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw n p.1)) := by
  have h := (tensorEnergyCoordinates_measurePreserving U I degree amplitude n b v).quasiMeasurePreserving.ae
    (tensorLabeled_exp_integrable hN eig U c I degree amplitude n b v hb z)
  filter_upwards [h] with p hp
  simpa only [tensorLeafSpinHamiltonian_eq_coordinates, tensorLabeledReference,
    tensorEnergyCoordinates, labeledSpinReference] using hp

lemma spinLeafTerminal_tensorLeafSpinHamiltonian {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n)
    (α : LabeledLeaf n) :
    spinLeafTerminal (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) α =
      spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z) := by
  exact finiteLogIntegral_uniformSpinPrior _

/-- Actual finite tensor Hamiltonian version of conditional spin sampling. -/
theorem tensorLeafSpinPair_conditioning {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorCoordinateData I degree n)
    (he : Integrable (fun s => Real.exp (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p s))
      ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw n p.1)))
    (D : (Fin 2 → Spin N × LabeledLeaf n) → ℝ)
    (hD : ∃ C : ℝ, ∀ x, |D x| ≤ C) :
    referenceReplicaMean ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw n p.1))
      (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) D =
      referenceReplicaMean (labeledLeafLaw n p.1)
        (fun α => spinTensorTerminal eig U c I degree amplitude
          (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z))
        (fun α => ∫ σ, D (spinLeafPairJoin (α, σ))
          ∂spinLeafPairResidualKernel (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) α) := by
  have ht : spinLeafTerminal (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) =
      (fun α => spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z)) := by
    funext α
    exact spinLeafTerminal_tensorLeafSpinHamiltonian eig U c I degree amplitude n z p α
  simpa only [ht] using spinLeafPair_conditioning (labeledLeafLaw n p.1)
    (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) he D hD

/-- The actual Gaussian/cascade disorder satisfies the conditional pair
factorization almost surely, on one event for every bounded pair test. -/
theorem tensorLeafSpinPair_conditioning_ae {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ∀ᵐ p ∂tensorCoordinateLaw I degree n b v,
      ∀ D : (Fin 2 → Spin N × LabeledLeaf n) → ℝ,
        (∃ C : ℝ, ∀ x, |D x| ≤ C) →
        referenceReplicaMean ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw n p.1))
          (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) D =
          referenceReplicaMean (labeledLeafLaw n p.1)
            (fun α => spinTensorTerminal eig U c I degree amplitude
              (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z))
            (fun α => ∫ σ, D (spinLeafPairJoin (α, σ))
              ∂spinLeafPairResidualKernel (tensorLeafSpinHamiltonian eig U c I degree amplitude n z p) α) := by
  filter_upwards [tensorLeafSpin_exp_integrable_ae hN eig U c I degree amplitude n b v hb z] with p hp
  intro D hD
  exact tensorLeafSpinPair_conditioning eig U c I degree amplitude n z p hp D hD

end InvariantIsing

end

end OAI
