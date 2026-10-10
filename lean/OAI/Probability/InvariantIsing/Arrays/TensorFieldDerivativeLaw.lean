import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivative
import OAI.Probability.InvariantIsing.Arrays.TensorCoefficientDerivative

namespace OAI

/-! Increasing the linear field in a nonnegative monotone direction is
exactly an independent Gaussian insertion in the actual tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma tensorNamespacedPath_field_add_cross {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedCoefficients U I degree amp n
      (fun i => tensorPathProfile I degree n treeDegree (fun j => h j + a * g j) i) x)
      (tensorNamespacedCoefficients U I degree amp n
        (fun i => tensorPathProfile I degree n treeDegree (fun j => h j + a * g j) i) y) =
      cylinderCross (tensorNamespacedCoefficients U I degree amp n
        (fun i => tensorPathProfile I degree n treeDegree h i) x)
        (tensorNamespacedCoefficients U I degree amp n
          (fun i => tensorPathProfile I degree n treeDegree h i) y) +
        a * cylinderCross (tensorLinearCoefficients n g x) (tensorLinearCoefficients n g y) := by
  simp_rw [tensorNamespacedCoefficients_mixed_cross_eq]
  rw [tensorPathProfile_covariance U I degree amp n treeDegree _
      (monotone_field_add hh hg ha) (field_add_nonneg h0 g0 ha),
    tensorPathProfile_covariance U I degree amp n treeDegree h hh h0,
    tensorLinearCoefficients_cross n g hg g0]
  ring

def tensorFieldInsertedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ)
    (p : TensorFlatDisorder N n × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (tensorNamespacedHamiltonian eig c I degree amp n treeDegree h p.1 x +
      Real.sqrt a * cylinderField (tensorLinearCoefficients n g x) p.2)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2)

def tensorFieldInsertedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ)
    (p : TensorFlatDisorder N n × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) : ℝ :=
  tensorNamespacedHamiltonian eig c I degree amp n treeDegree h p.1 x +
    Real.sqrt a * cylinderField (tensorLinearCoefficients n g x) p.2

lemma measurable_tensorFieldInsertedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) :
    Measurable (Function.uncurry (tensorFieldInsertedHamiltonian eig c I degree amp n treeDegree h g a)) := by
  have hm : Measurable (fun p : (TensorFlatDisorder N n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      (p.1.1,p.2)) := measurable_fst.fst.prodMk measurable_snd
  have hM := (measurable_tensorNamespacedHamiltonian eig c I degree amp n treeDegree h).comp hm
  have hH : Measurable (fun p : (TensorFlatDisorder N n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      tensorNamespacedHamiltonian eig c I degree amp n treeDegree h p.1.1 p.2) := by
    convert hM using 1
    rfl
  have hG : Measurable (fun p : (TensorFlatDisorder N n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      Real.sqrt a * cylinderField (tensorLinearCoefficients n g p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hx : Measurable (fun p : TensorFlatDisorder N n × (ℕ → ℝ) =>
        cylinderField (tensorLinearCoefficients n g x) p.2) :=
      (measurable_cylinderField (tensorLinearCoefficients n g x)).comp measurable_snd
    exact hx.const_mul _
  exact hH.add hG

lemma measurable_tensorFieldInsertedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) :
    Measurable (tensorFieldInsertedLog eig c I degree amp n treeDegree h g a) := by
  let ν := fun p : TensorFlatDisorder N n × (ℕ → ℝ) =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst.fst.snd
  have hm := (measurable_random_referencePartition hν
    (measurable_tensorFieldInsertedHamiltonian eig c I degree amp n treeDegree h g a)).log
  convert hm using 1
  rfl

lemma tensorFieldInsertedLog_conditional_law {N m k n : ℕ} (eig c : Fin N → ℝ)
    (U : SpecialOrthogonal N) (T : LabeledTree n)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) :
    (gaussianCoordinates.prod gaussianCoordinates).map (fun z : (ℕ → ℝ) × (ℕ → ℝ) =>
      tensorFieldInsertedLog eig c I degree amp n treeDegree h g a (((U,T),z.1),z.2)) =
      gaussianCoordinates.map (fun z => tensorNamespacedLog eig c I degree amp n treeDegree
        (fun i => h i + a * g i) ((U,T),z)) := by
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
  let H := fun x : Spin N × LabeledLeaf n =>
    rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1
  let K := fun F : (Spin N × LabeledLeaf n → ℝ) => Real.log (∫ x, Real.exp (H x + F x) ∂ν)
  have : ∀ F : (Spin N × LabeledLeaf n → ℝ), IsProbabilityMeasure ((fun _ => ν) F) :=
    fun _ => by change IsProbabilityMeasure ν; infer_instance
  have hE : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) × (Spin N × LabeledLeaf n) =>
      H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hx : Measurable (fun _ : Spin N × LabeledLeaf n → ℝ => H x) := measurable_const
    exact hx.add (measurable_pi_apply x)
  have hK : Measurable K := (measurable_random_referencePartition
    (ν := fun _ : Spin N × LabeledLeaf n → ℝ => ν) measurable_const hE).log
  let A : Spin N × LabeledLeaf n → ℕ →₀ ℝ := tensorNamespacedCoefficients (specialRotation U) I degree amp n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  let B : Spin N × LabeledLeaf n → ℕ →₀ ℝ := tensorLinearCoefficients n g
  let C : Spin N × LabeledLeaf n → ℕ →₀ ℝ := tensorNamespacedCoefficients (specialRotation U) I degree amp n
    (fun i => tensorPathProfile I degree n treeDegree (fun j => h j + a * g j) i)
  have hf : Measurable (fun z : (ℕ → ℝ) × (ℕ → ℝ) =>
      fun x => cylinderField (A x) z.1 + Real.sqrt a * cylinderField (B x) z.2) :=
    Measurable.of_eval (fun x => ((measurable_cylinderField (A x)).comp measurable_fst).add
      (((measurable_cylinderField (B x)).comp measurable_snd).const_mul _))
  have hc : Measurable (fun z => fun x => cylinderField (C x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (C x))
  have he := cylinder_independent_sum_law A B C (Real.sqrt a) (fun x y => by
    rw [Real.sq_sqrt ha]
    exact tensorNamespacedPath_field_add_cross (specialRotation U) I degree amp n treeDegree h g hh h0 hg g0 a ha x y)
  have hl : (fun z : (ℕ → ℝ) × (ℕ → ℝ) =>
      tensorFieldInsertedLog eig c I degree amp n treeDegree h g a (((U,T),z.1),z.2)) =
      K ∘ (fun z => fun x => cylinderField (A x) z.1 + Real.sqrt a * cylinderField (B x) z.2) := by
    funext z
    apply congrArg Real.log
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    apply congrArg Real.exp
    dsimp [tensorNamespacedHamiltonian, H, A, B]
    ring
  change _ = gaussianCoordinates.map (K ∘ (fun z => fun x => cylinderField (C x) z))
  rw [hl, ← Measure.map_map hK hf, ← Measure.map_map hK hc, he]

private lemma tensorField_joint_map_eq {Ω A B E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure A) (R : Measure B) [SFinite Q] [SFinite R]
    (f : Ω × A → E) (g : Ω × B → E) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ ω, Q.map (fun z => f (ω,z)) = R.map (fun z => g (ω,z))) :
    (P.prod Q).map f = (P.prod R).map g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply (hf hs), Measure.prod_apply (hg hs)]
  apply lintegral_congr_ae
  refine ae_of_all _ fun ω => ?_
  have h := congrArg (fun ν : Measure E => ν s) (he ω)
  have hfω : Measurable (fun z => f (ω,z)) := hf.comp (measurable_const.prodMk measurable_id)
  have hgω : Measurable (fun z => g (ω,z)) := hg.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hfω hs, Measure.map_apply hgω hs] at h
  exact h

theorem tensorFieldInsertedLog_identDistrib {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) :
    IdentDistrib (tensorFieldInsertedLog eig c I degree amp n treeDegree h g a)
      (tensorNamespacedLog eig c I degree amp n treeDegree (fun i => h i + a * g i))
      (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod gaussianCoordinates)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  let P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := fun p : (SpecialOrthogonal N × LabeledTree n) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
    tensorFieldInsertedLog eig c I degree amp n treeDegree h g a ((p.1,p.2.1),p.2.2)
  let G := tensorNamespacedLog eig c I degree amp n treeDegree (fun i => h i + a * g i)
  have hf : Measurable F := (measurable_tensorFieldInsertedLog eig c I degree amp n treeDegree h g a).comp
    MeasurableEquiv.prodAssoc.symm.measurable
  have hg' : Measurable G := measurable_tensorNamespacedLog eig c I degree amp n treeDegree _
  have he := tensorField_joint_map_eq P (gaussianCoordinates.prod gaussianCoordinates) gaussianCoordinates
    F G hf hg' (fun ω => tensorFieldInsertedLog_conditional_law eig c ω.1 ω.2 I degree amp treeDegree h g hh h0 hg g0 a ha)
  have hs := measurePreserving_prodAssoc P gaussianCoordinates gaussianCoordinates
  refine ⟨(measurable_tensorFieldInsertedLog eig c I degree amp n treeDegree h g a).aemeasurable,
    hg'.aemeasurable, ?_⟩
  change ((P.prod gaussianCoordinates).prod gaussianCoordinates).map
    (F ∘ (MeasurableEquiv.prodAssoc : ((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (ℕ → ℝ) → (SpecialOrthogonal N × LabeledTree n) × ((ℕ → ℝ) × (ℕ → ℝ)))) =
      (P.prod gaussianCoordinates).map G
  rw [← Measure.map_map hf hs.measurable, hs.map_eq]
  exact he

end InvariantIsing

end

end OAI
