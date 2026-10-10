import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFlatLaw
import OAI.Probability.InvariantIsing.Pressure.PressureDifferenceConcentration

namespace OAI

/-! Transfer the actual three-disorder pressure moments to one frozen Gaussian CGF. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

private lemma joint_map_eq_of_conditional_map_eq {Ω G E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure G) [SFinite Q]
    (f g : Ω × G → E) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ ω, Q.map (fun z => f (ω, z)) = Q.map (fun z => g (ω, z))) :
    (P.prod Q).map f = (P.prod Q).map g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply (hf hs), Measure.prod_apply (hg hs)]
  apply lintegral_congr_ae
  refine ae_of_all P fun ω => ?_
  have h := congrArg (fun ν : Measure E => ν s) (he ω)
  have hfω : Measurable (fun z => f (ω, z)) := hf.comp (measurable_const.prodMk measurable_id)
  have hgω : Measurable (fun z => g (ω, z)) := hg.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hfω hs, Measure.map_apply hgω hs] at h
  exact h

private lemma tensorNamespacedLog_conditional_law {N m k : ℕ} (eig c : Fin N → ℝ)
    (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (T : LabeledTree n) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    gaussianCoordinates.map (fun g => tensorFlatLog eig (specialRotation U) c I degree amplitude n
      (tensorPathProfile I degree n treeDegree h) (T, g)) =
    gaussianCoordinates.map (fun g => tensorNamespacedLog eig c I degree amplitude n treeDegree h ((U, T), g)) := by
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
  let H := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1
  let K := fun F : Spin N × LabeledLeaf n → ℝ => Real.log (∫ x, Real.exp (H x + F x) ∂ν)
  have : ∀ F : (Spin N × LabeledLeaf n → ℝ), IsProbabilityMeasure ((fun _ => ν) F) :=
    fun _ => by
      change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
      infer_instance
  have hE : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) × (Spin N × LabeledLeaf n) => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hc : Measurable (fun _ : Spin N × LabeledLeaf n → ℝ => H x) := measurable_const
    exact hc.add (measurable_pi_apply x)
  have hK : Measurable K := (measurable_random_referencePartition
    (ν := fun _ : Spin N × LabeledLeaf n → ℝ => ν) measurable_const hE).log
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hleft : Measurable (fun g x => cylinderField
      (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) g) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  have hright : Measurable (fun g x => cylinderField
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) g) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  change gaussianCoordinates.map (K ∘ (fun g x => cylinderField
      (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) g)) =
    gaussianCoordinates.map (K ∘ (fun g x => cylinderField
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) g))
  rw [← Measure.map_map hK hleft, ← Measure.map_map hK hright, tensorNamespacedFields_law]

private lemma measurable_tensorLeafField_joint {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (tensorLeafCoefficients (specialRotation p.1) I degree amplitude n v x) p.2) := by
  simp only [tensorLeafCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_spinTensorFeature I degree amplitude x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag n x.2 i)).comp measurable_snd)

private lemma measurable_tensorJointLog {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (Y : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) × (Spin N × LabeledLeaf n)) → ℝ)
    (hY : Measurable Y) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      Real.log (∫ x : Spin N × LabeledLeaf n,
        Real.exp (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 + Y (p, x))
        ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)) := by
  have hbase : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) => rotatedEnergy eig (specialRotation p.1.1.1) p.2.1 + fieldEnergy c p.2.1) := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
      unfold rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
    exact (hr.comp measurable_fst.fst).add_const (fieldEnergy c x.1)
  let ν := fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    infer_instance
  exact (measurable_random_referencePartition (ν := ν)
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd)
    (hbase.add hY)).log

lemma measurable_tensorNamespacedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (tensorNamespacedLog eig c I degree amplitude n treeDegree h) := by
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hY : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amplitude n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hp : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
        (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
    convert (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp hp using 1
    rfl
  exact measurable_tensorJointLog eig c n _ hY

private lemma measurable_tensorJointFlatLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      tensorFlatLog eig (specialRotation p.1.1) c I degree amplitude n
        (tensorPathProfile I degree n treeDegree h) (p.1.2, p.2)) := by
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hY : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorLeafCoefficients (specialRotation p.1.1.1) I degree amplitude n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hp : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
        (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
    convert (measurable_tensorLeafField_joint I degree amplitude n v x).comp hp using 1
    rfl
  exact measurable_tensorJointLog eig c n _ hY

def tensorNamespacedPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) : ℝ :=
  (N : ℝ)⁻¹ * tensorNamespacedLog eig c I degree amplitude n treeDegree h p

/-- The tensor pressure has the marked-cascade pressure law,
including the Haar rotation. This is a law identity, stronger than matching means. -/
theorem tensorNamespacedPressure_law {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hb : CascadeExponents n b) :
    HasLaw (tensorNamespacedPressure eig c I degree amplitude n treeDegree h)
      ((μ.prod (tensorRootTreeLaw I degree n b
        (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
        (tensorPathProfile I degree n treeDegree h 0))).map
          (tensorDisorderPressure eig c I degree amplitude n))
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  let P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
    tensorFlatLog eig (specialRotation p.1.1) c I degree amplitude n
      (tensorPathProfile I degree n treeDegree h) (p.1.2, p.2)
  let G := tensorNamespacedLog eig c I degree amplitude n treeDegree h
  have hF : Measurable F := measurable_tensorJointFlatLog eig c I degree amplitude n treeDegree h
  have hG : Measurable G := measurable_tensorNamespacedLog eig c I degree amplitude n treeDegree h
  have he : (P.prod gaussianCoordinates).map F = (P.prod gaussianCoordinates).map G :=
    joint_map_eq_of_conditional_map_eq P gaussianCoordinates F G hF hG
      (fun ω => tensorNamespacedLog_conditional_law eig c ω.1 I degree amplitude n ω.2 treeDegree h)
  let S := fun x : ℝ => (N : ℝ)⁻¹ * x
  have hS : Measurable S := measurable_id.const_mul _
  have hes : (P.prod gaussianCoordinates).map (S ∘ F) = (P.prod gaussianCoordinates).map (S ∘ G) := by
    rw [← Measure.map_map hS hF, ← Measure.map_map hS hG, he]
  have hactual := (hasLaw_map (measurable_tensorDisorderPressure eig c I degree amplitude n).aemeasurable).comp
    (tensorFlatToDisorder_measurePreserving μ I degree n b (tensorPathProfile I degree n treeDegree h)).hasLaw
  have hflat := hactual.congr (tensorFlatPressure_eq_disorder_ae μ eig c I degree amplitude n b
    (tensorPathProfile I degree n treeDegree h) hb)
  refine ⟨(hG.const_mul (N : ℝ)⁻¹).aemeasurable, ?_⟩
  exact hes.symm.trans hflat.map_eq

/-- Transport both the second moment and the exact variance and mean. -/
theorem tensorNamespacedPressure_moments {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hb : CascadeExponents n b)
    (hF : MemLp (tensorDisorderPressure eig c I degree amplitude n) 2
      (μ.prod (tensorRootTreeLaw I degree n b
        (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
        (tensorPathProfile I degree n treeDegree h 0)))) :
    let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
    let R := μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0))
    let F := tensorNamespacedPressure eig c I degree amplitude n treeDegree h
    MemLp F 2 Q ∧ variance F Q = variance (tensorDisorderPressure eig c I degree amplitude n) R ∧
      (∫ p, F p ∂Q) = ∫ p, tensorDisorderPressure eig c I degree amplitude n p ∂ R := by
  intro Q R F
  have hlaw := tensorNamespacedPressure_law μ eig c I degree amplitude n b treeDegree h hb
  have hid : MemLp id 2 (R.map (tensorDisorderPressure eig c I degree amplitude n)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hF.aemeasurable).mpr hF
  refine ⟨hlaw.memLp hid, hlaw.variance_eq.trans (variance_id_map hF.aemeasurable), ?_⟩
  exact hlaw.integral_eq.trans (integral_map hF.aemeasurable aestronglyMeasurable_id)

/-- Freezing one Gaussian namespace preserves the pressure law at every
value of that namespace's amplitude, including zero. -/
theorem tensorFrozenPressure_moments {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hb : CascadeExponents n b)
    (j : Fin k) (t : ℝ)
    (hF : MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j t) n) 2
      (μ.prod (tensorRootTreeLaw I degree n b
        (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
        (tensorPathProfile I degree n treeDegree h 0)))) :
    let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let R := μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0))
    let F := fun p => (N : ℝ)⁻¹ * tensorFrozenPartitionLog eig c I degree amplitude n treeDegree h j t p
    MemLp F 2 Q ∧
      variance F Q = variance (tensorDisorderPressure eig c I degree (Function.update amplitude j t) n) R ∧
      (∫ p, F p ∂Q) = ∫ p, tensorDisorderPressure eig c I degree (Function.update amplitude j t) n p ∂ R := by
  intro Q R F
  have hp := tensorFrozenInsertion_measurePreserving μ n b j
  have hm := tensorNamespacedPressure_moments μ eig c I degree (Function.update amplitude j t)
    n b treeDegree h hb hF
  refine ⟨hm.1.comp_measurePreserving hp, ?_, ?_⟩
  · exact (hp.variance_fun_comp hm.1.aemeasurable).trans hm.2.1
  · exact (hp.hasLaw.integral_comp hm.1.aestronglyMeasurable).trans hm.2.2

lemma tensorFrozenCGF_eq_scaled_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (j : Fin k) (t : ℝ) :
    tensorFrozenCGF eig c I degree amplitude n treeDegree h j t =ᵐ[
      (tensorFrozenLaw μ n b j).prod gaussianCoordinates]
      (fun p => (N : ℝ) *
        ((N : ℝ)⁻¹ * tensorFrozenPartitionLog eig c I degree amplitude n treeDegree h j t p -
          (N : ℝ)⁻¹ * tensorFrozenPartitionLog eig c I degree amplitude n treeDegree h j 0 p)) := by
  filter_upwards [tensorFrozenCGF_eq_log_difference μ eig c I degree amplitude n b treeDegree h hh h0 j t]
    with p hp
  rw [hp]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp

/-- The expected frozen CGF is the volume times the difference of the
two actual all-disorder pressures. -/
theorem tensorFrozenCGF_mean {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin k) (t : ℝ)
    (hF : ∀ a : ℝ, a = t ∨ a = 0 →
      MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
          (tensorPathProfile I degree n treeDegree h 0)))) :
    let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let R := μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0))
    (∫ p, tensorFrozenCGF eig c I degree amplitude n treeDegree h j t p ∂Q) =
      (N : ℝ) * ((∫ p, tensorDisorderPressure eig c I degree (Function.update amplitude j t) n p ∂ R) -
        ∫ p, tensorDisorderPressure eig c I degree (Function.update amplitude j 0) n p ∂ R) := by
  intro Q R
  have hmt := tensorFrozenPressure_moments μ eig c I degree amplitude n b treeDegree h hb j t (hF t (Or.inl rfl))
  have hmz := tensorFrozenPressure_moments μ eig c I degree amplitude n b treeDegree h hb j 0 (hF 0 (Or.inr rfl))
  rw [integral_congr_ae (tensorFrozenCGF_eq_scaled_difference hN μ eig c I degree amplitude n b treeDegree h hh h0 j t),
    integral_const_mul, integral_sub (hmt.1.integrable (by norm_num)) (hmz.1.integrable (by norm_num)),
    hmt.2.2, hmz.2.2]

/-- The actual full-disorder pressure variance controls the centered
selected-field CGF. The two pressures may be dependent. -/
theorem tensorFrozenCGF_centered_L1_bound {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin k) (t B : ℝ)
    (hF : ∀ a : ℝ, a = t ∨ a = 0 →
      MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
          (tensorPathProfile I degree n treeDegree h 0))))
    (hv : ∀ a : ℝ, a = t ∨ a = 0 →
      variance (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n)
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
          (tensorPathProfile I degree n treeDegree h 0))) ≤ B) :
    let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let Z := tensorFrozenCGF eig c I degree amplitude n treeDegree h j t
    MemLp Z 2 Q ∧ (∫ p, |Z p - ∫ p', Z p' ∂Q| ∂Q) ≤ 2 * N * Real.sqrt B := by
  intro Q Z
  let F := fun a p => (N : ℝ)⁻¹ * tensorFrozenPartitionLog eig c I degree amplitude n treeDegree h j a p
  have ht : t = t ∨ t = 0 := Or.inl rfl
  have hz : (0 : ℝ) = t ∨ (0 : ℝ) = 0 := Or.inr rfl
  have hmt := tensorFrozenPressure_moments μ eig c I degree amplitude n b treeDegree h hb j t (hF t ht)
  have hmz := tensorFrozenPressure_moments μ eig c I degree amplitude n b treeDegree h hb j 0 (hF 0 hz)
  have he : Z =ᵐ[Q] fun p => (N : ℝ) * (F t p - F 0 p) := by
    exact tensorFrozenCGF_eq_scaled_difference hN μ eig c I degree amplitude n b treeDegree h hh h0 j t
  simpa only [abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)] using
    centered_scaled_difference_L1_bound Q hmt.1 hmz.1
      (hmt.2.1.trans_le (hv t ht)) (hmz.2.1.trans_le (hv 0 hz)) he

end InvariantIsing

end

end OAI
