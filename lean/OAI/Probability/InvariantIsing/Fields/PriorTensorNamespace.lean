import OAI.Probability.InvariantIsing.Fields.PriorTensorPressure
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozenCGF

namespace OAI

/-! Independent Gaussian namespaces for the actual fixed-prior model.
Changing Gaussian coordinates preserves its entire pressure law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorNamespacedHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation p.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorNamespacedCoefficients (specialRotation p.1) I degree amplitude n v x) p.2

lemma measurable_priorNamespacedHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (Function.uncurry (priorNamespacedHamiltonian eig c I degree amplitude v)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hb : Measurable (fun U : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1) := by
    exact ((Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul
        (1/2 : ℝ)).add_const _
  exact (hb.comp measurable_fst).add (measurable_tensorNamespacedFields_joint I degree amplitude n v x)

def priorNamespacedLog {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x, Real.exp (priorNamespacedHamiltonian eig c I degree amplitude v p x) ∂ν)

lemma measurable_priorNamespacedLog {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (priorNamespacedLog ν eig c I degree amplitude v) :=
  (measurable_priorNamespacedHamiltonian eig c I degree amplitude v).exp.stronglyMeasurable
    |>.integral_prod_right' |>.measurable.log

lemma priorNamespacedLog_conditional_law {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    gaussianCoordinates.map (fun z => priorTensorLog ν eig c I degree amplitude v (U,z)) =
      gaussianCoordinates.map (fun z => priorNamespacedLog ν eig c I degree amplitude v (U,z)) := by
  let H := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation U) x.1+fieldEnergy c x.1
  let K := fun F : Spin N × LabeledLeaf n → ℝ => Real.log (∫ x, Real.exp (H x+F x) ∂ν)
  have hK : Measurable K := by
    have he : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) ×
        (Spin N × LabeledLeaf n) => H p.2+p.1 p.2) :=
      measurable_from_prod_countable_left fun x => by
        change Measurable (fun F : Spin N × LabeledLeaf n → ℝ => H x+F x)
        exact measurable_const.add (measurable_pi_apply x)
    exact he.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hl : Measurable (fun z x => cylinderField
      (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) z) :=
    Measurable.of_eval fun _ => measurable_cylinderField _
  have hr : Measurable (fun z x => cylinderField
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) z) :=
    Measurable.of_eval fun _ => measurable_cylinderField _
  change gaussianCoordinates.map (K ∘ (fun z x => cylinderField
    (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) z)) =
      gaussianCoordinates.map (K ∘ (fun z x => cylinderField
        (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) z))
  rw [← Measure.map_map hK hl,← Measure.map_map hK hr,tensorNamespacedFields_law]

theorem priorNamespacedLog_law {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    HasLaw (priorNamespacedLog ν eig c I degree amplitude v)
      ((μ.prod gaussianCoordinates).map (priorTensorLog ν eig c I degree amplitude v))
      (μ.prod gaussianCoordinates) := by
  have hl := measurable_priorTensorLog ν eig c I degree amplitude v
  have hr := measurable_priorNamespacedLog ν eig c I degree amplitude v
  refine ⟨hr.aemeasurable,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hr hs,Measure.map_apply hl hs,Measure.prod_apply (hr hs),Measure.prod_apply (hl hs)]
  apply lintegral_congr_ae
  apply ae_of_all
  intro U
  have he := congrArg (fun Q : Measure ℝ => Q s)
    (priorNamespacedLog_conditional_law ν eig c U I degree amplitude v)
  have hlU : Measurable (fun z : ℕ → ℝ => priorTensorLog ν eig c I degree amplitude v (U,z)) :=
    hl.comp (measurable_const.prodMk measurable_id)
  have hrU : Measurable (fun z : ℕ → ℝ => priorNamespacedLog ν eig c I degree amplitude v (U,z)) :=
    hr.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hlU hs,Measure.map_apply hrU hs] at he
  exact he.symm

theorem priorNamespacedLog_moments {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (hF : MemLp (priorTensorLog ν eig c I degree amplitude v) 2 (μ.prod gaussianCoordinates)) :
    MemLp (priorNamespacedLog ν eig c I degree amplitude v) 2 (μ.prod gaussianCoordinates) ∧
    variance (priorNamespacedLog ν eig c I degree amplitude v) (μ.prod gaussianCoordinates) =
      variance (priorTensorLog ν eig c I degree amplitude v) (μ.prod gaussianCoordinates) ∧
    (∫ p, priorNamespacedLog ν eig c I degree amplitude v p ∂μ.prod gaussianCoordinates) =
      ∫ p, priorTensorLog ν eig c I degree amplitude v p ∂μ.prod gaussianCoordinates := by
  have hlaw := priorNamespacedLog_law μ ν eig c I degree amplitude v
  have hid : MemLp id 2 ((μ.prod gaussianCoordinates).map (priorTensorLog ν eig c I degree amplitude v)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hF.aemeasurable).mpr hF
  exact ⟨hlaw.memLp hid,hlaw.variance_eq.trans (variance_id_map hF.aemeasurable),
    hlaw.integral_eq.trans (integral_map hF.aemeasurable aestronglyMeasurable_id)⟩

end InvariantIsing

end

end OAI
