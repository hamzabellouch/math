import OAI.Probability.InvariantIsing.Arrays.NSpinTensorPairPaths
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! Terminal derivatives and the projected magnetization form of pair paths. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

lemma integral_uniformSpinPrior {N : ℕ} (f : Spin N → ℝ) :
    (∫ σ, f σ ∂(uniformSpinPrior N : Measure (Spin N))) =
      (Fintype.card (Spin N) : ℝ)⁻¹ * ∑ σ, f σ := by
  change (∫ σ, f σ ∂(PMF.uniformOfFintype (Spin N)).toMeasure) = _
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [Finset.mul_sum]

lemma integral_uniformSpinGibbs_eq {N : ℕ} (H A : Spin N → ℝ) :
    (∫ σ, A σ ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) =
      gibbsAverage (fun _ => 1) H A := by
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite, integral_tilted,
    integral_uniformSpinPrior]
  have hp : referencePartition (uniformSpinPrior N : Measure (Spin N)) H =
      (Fintype.card (Spin N) : ℝ)⁻¹ * finitePartition (fun _ => 1) H := by
    rw [referencePartition, integral_uniformSpinPrior]
    simp only [finitePartition, one_mul]
  change (Fintype.card (Spin N) : ℝ)⁻¹ *
      ∑ σ, (Real.exp (H σ) / referencePartition (uniformSpinPrior N : Measure (Spin N)) H) * A σ = _
  rw [hp, Finset.mul_sum]
  unfold gibbsAverage finiteGibbs
  apply Finset.sum_congr rfl
  intro σ _
  have hc : (Fintype.card (Spin N) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ : finitePartition (fun _ : Spin N => 1) H ≠ 0 :=
    ne_of_gt (finitePartition_pos GibbsReference_one H)
  field_simp

def tensorCoordinateVariation {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (z : SpinTensorIndex I degree → ℝ)
    (j : SpinTensorIndex I degree) (t : ℝ) : SpinTensorIndex I degree → ℝ :=
  fun i => z i + if i = j then t else 0

lemma spinTensorEnergy_coordinateVariation {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (j : SpinTensorIndex I degree) (t : ℝ) (σ : Spin N) :
    spinTensorEnergy U I degree amplitude (tensorCoordinateVariation I degree z j t) σ =
      spinTensorEnergy U I degree amplitude z σ + t * spinTensorFeature U I degree amplitude σ j := by
  classical
  simp only [spinTensorEnergy, tensorCoordinateVariation, add_mul, Finset.sum_add_distrib]
  congr 1
  simp only [ite_mul, zero_mul]
  simp

def tensorTerminalCoordinateMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (j : SpinTensorIndex I degree) : ℝ :=
  gibbsAverage (fun _ => 1) (tensorSpinBaseEnergy eig U c I degree amplitude z)
    (fun σ => spinTensorFeature U I degree amplitude σ j)

def tensorFeatureCoordinateCap {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (j : SpinTensorIndex I degree) : ℝ :=
  ∑ σ : Spin N, |spinTensorFeature U I degree amplitude σ j|

lemma tensorTerminalCoordinateMean_abs_le {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (j : SpinTensorIndex I degree) :
    |tensorTerminalCoordinateMean eig U c I degree amplitude z j| ≤
      tensorFeatureCoordinateCap U I degree amplitude j := by
  apply abs_gibbsAverage_le GibbsReference_one
  intro σ
  exact Finset.single_le_sum (fun τ _ => abs_nonneg (spinTensorFeature U I degree amplitude τ j))
    (Finset.mem_univ σ)

lemma measurable_tensorTerminalCoordinateMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (j : SpinTensorIndex I degree) :
    Measurable (fun z => tensorTerminalCoordinateMean eig U c I degree amplitude z j) := by
  apply measurable_gibbsAverage (fun _ => 1)
  · intro σ
    exact (((measurable_pi_apply σ).comp (measurable_spinTensorEnergyMark U I degree amplitude))).const_add
      (rotatedEnergy eig U σ + fieldEnergy c σ)
  · intro _
    exact measurable_const

/-- An actual coordinate derivative of the finite Ising terminal. -/
theorem hasDerivAt_spinTensorTerminal_coordinate {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (j : SpinTensorIndex I degree) (t : ℝ) :
    HasDerivAt (fun s => spinTensorTerminal eig U c I degree amplitude
      (tensorCoordinateVariation I degree z j s))
      (tensorTerminalCoordinateMean eig U c I degree amplitude
        (tensorCoordinateVariation I degree z j t) j) t := by
  have hH (σ : Spin N) : HasDerivAt (fun s => tensorSpinBaseEnergy eig U c I degree amplitude
      (tensorCoordinateVariation I degree z j s) σ) (spinTensorFeature U I degree amplitude σ j) t := by
    simp only [tensorSpinBaseEnergy, spinTensorEnergy_coordinateVariation]
    convert ((hasDerivAt_id t).mul_const (spinTensorFeature U I degree amplitude σ j)).const_add
      (rotatedEnergy eig U σ + fieldEnergy c σ + spinTensorEnergy U I degree amplitude z σ) using 1
    · funext s
      simp only [id_eq]
      ring
    · simp
  have hd := (hasDerivAt_log_finitePartition GibbsReference_one hH).sub_const
    (Real.log (Fintype.card (Spin N)))
  convert hd using 1
  · funext s
    simp only [spinTensorTerminal, logPartition_eq, finitePartition, one_mul, tensorSpinBaseEnergy]
  · rfl

def tensorProjectedMagnetization {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (a : Fin N) : ℝ :=
  gibbsAverage (fun _ => 1) (tensorSpinBaseEnergy eig U c I degree amplitude z)
    (fun σ => U (spinVector σ) a)

lemma tensorProjectedMagnetization_eq {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (a : Fin N) :
    tensorProjectedMagnetization eig U c I degree amplitude z a =
      U (WithLp.toLp 2 (fun i => tensorTerminalCoordinateMean eig U c I degree amplitude z (Sum.inl i))) a := by
  let H := tensorSpinBaseEnergy eig U c I degree amplitude z
  have hm : WithLp.toLp 2 (fun i => tensorTerminalCoordinateMean eig U c I degree amplitude z (Sum.inl i)) =
      ∑ σ : Spin N, finiteGibbs (fun _ => 1) H σ • spinVector σ := by
    ext i
    change tensorTerminalCoordinateMean eig U c I degree amplitude z (Sum.inl i) =
      (WithLp.ofLp (∑ σ : Spin N, finiteGibbs (fun _ => 1) H σ • spinVector σ)) i
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [tensorTerminalCoordinateMean, gibbsAverage, spinTensorFeature,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, spinVector, H]
  rw [hm, map_sum]
  change gibbsAverage (fun _ => 1) H (fun σ => U (spinVector σ) a) =
    (WithLp.ofLp (∑ σ : Spin N, U (finiteGibbs (fun _ => 1) H σ • spinVector σ))) a
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, gibbsAverage]

lemma tensorPairPathSpinMean_overlap {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (p : TensorPairPathData I degree n) (J : Finset (Fin N)) :
    tensorPairPathSpinMean eig U c I degree amplitude n p
      (fun σ => projectedOverlap U J (σ 0) (σ 1)) =
      (N : ℝ)⁻¹ * ∑ a ∈ J,
        tensorProjectedMagnetization eig U c I degree amplitude (tensorPairPathState I degree n p 0) a *
          tensorProjectedMagnetization eig U c I degree amplitude (tensorPairPathState I degree n p 1) a := by
  let μ := fun j : Fin 2 => gibbsProbability (uniformSpinPrior N : Measure (Spin N))
    (tensorSpinBaseEnergy eig U c I degree amplitude (tensorPairPathState I degree n p j))
  change (∫ σ : Fin 2 → Spin N, (N : ℝ)⁻¹ *
    ∑ a ∈ J, U (spinVector (σ 0)) a * U (spinVector (σ 1)) a ∂Measure.pi μ) = _
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have h := integral_fin_nat_prod_eq_prod (μ := μ) (fun (_ : Fin 2) (σ : Spin N) => U (spinVector σ) a)
  simpa only [Fin.prod_univ_two, μ, integral_uniformSpinGibbs_eq, tensorProjectedMagnetization] using h

/-- The actual projected overlap along two paths is the product of the
projected terminal Gibbs gradients. -/
theorem tensorPairPathSpinMean_overlap_gradient {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (p : TensorPairPathData I degree n) (J : Finset (Fin N)) :
    tensorPairPathSpinMean eig U c I degree amplitude n p
      (fun σ => projectedOverlap U J (σ 0) (σ 1)) =
      (N : ℝ)⁻¹ * ∑ a ∈ J,
        U (WithLp.toLp 2 (fun i => tensorTerminalCoordinateMean eig U c I degree amplitude
          (tensorPairPathState I degree n p 0) (Sum.inl i))) a *
        U (WithLp.toLp 2 (fun i => tensorTerminalCoordinateMean eig U c I degree amplitude
          (tensorPairPathState I degree n p 1) (Sum.inl i))) a := by
  simp only [tensorPairPathSpinMean_overlap, tensorProjectedMagnetization_eq]

end InvariantIsing

end

end OAI
