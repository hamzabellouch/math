import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CoefficientStep

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)
private def versionCoordinates (hK : K.Completed) (t : ℕ) (j : State M)
    (obs : Vector d × ℝ) (a : Action M) : ℝ≥0∞ :=
  (hK t j a).mk (fun obs => K.transition t j obs a) obs
private lemma measurable_versionCoordinates (hK : K.Completed) (t : ℕ) (j : State M) (a : Action M) :
    Measurable (fun obs => K.versionCoordinates hK t j obs a) :=
  (hK t j a).measurable_mk
private lemma versionCoordinates_ae (hK : K.Completed) (t : ℕ) (j : State M) :
    ∀ᵐ obs ∂ObservationReference d, ∀ a, K.versionCoordinates hK t j obs a = K.transition t j obs a := by
  apply ae_all_iff.mpr
  intro a
  exact (hK t j a).ae_eq_mk.symm

def version (hK : K.Completed) : Policy d M T where
  initial := K.initial
  initial_sum := K.initial_sum
  transition := fun t j obs a => if ∑ b, K.versionCoordinates hK t j obs b = 1
    then K.versionCoordinates hK t j obs a else if a = (false,0) then 1 else 0
  transition_sum := by
    intro t j obs
    split_ifs with h
    · exact h
    · simp
  output := K.output
  output_probability := K.output_probability

lemma version_borel (hK : K.Completed) : (K.version hK).Borel := by
  intro t j a
  exact Measurable.ite
    (measurableSet_eq_fun (Finset.measurable_sum _ (fun b _ =>
      K.measurable_versionCoordinates hK t j b)) measurable_const)
    (K.measurable_versionCoordinates hK t j a) measurable_const

lemma version_transition_ae (hK : K.Completed) (t : ℕ) (j : State M) :
    ∀ᵐ obs ∂ObservationReference d, ∀ a, (K.version hK).transition t j obs a = K.transition t j obs a := by
  filter_upwards [K.versionCoordinates_ae hK t j] with obs h
  have he : ∑ a, K.versionCoordinates hK t j obs a = 1 := by
    simpa only [h] using K.transition_sum t j obs
  intro a
  simp only [version, h, K.transition_sum, ite_true]

lemma eval_eq_of_rules {L : Policy d M T} {X : Type*}
    (w : ℕ → State M → X → ℝ≥0∞) (n k : ℕ) (j : State M) (s : X)
    (obs : Observations d k)
    (h : ∀ t j i a, K.transition t j (obs i) a = L.transition t j (obs i) a) :
    K.eval w n k j s obs = L.eval w n k j s obs := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    simp only [eval, h]
    congr 1
    funext a
    congr 1
    split
    · rfl
    · exact ih (n+1) a.2 (Fin.tail obs) (fun t j i a => h t j i.succ a)

lemma version_pathValue_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hK : K.Completed) (s : X → Sphere d) (obs : X → Observations d T)
    (ho : ∀ i : Fin T, Measure.QuasiMeasurePreserving (fun z => obs z i) μ (ObservationReference d))
    (f : Sphere d × Sphere d → ℝ≥0∞) :
    (fun z => (K.version hK).pathValue ((K.version hK).outputTest f) (s z) (obs z)) =ᵐ[μ]
      (fun z => K.pathValue (K.outputTest f) (s z) (obs z)) := by
  have hall : ∀ᵐ z ∂μ, ∀ i t j a,
      (K.version hK).transition t j (obs z i) a = K.transition t j (obs z i) a := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro t
    apply ae_all_iff.mpr
    intro j
    exact (ho i).ae (K.version_transition_ae hK t j)
  filter_upwards [hall] with z hz
  change (∑ a : Action M, K.initial a * if a.1 then K.outputTest f 0 a.2 (s z)
    else (K.version hK).eval (K.outputTest f) 0 T a.2 (s z) (obs z)) = _
  simp only [pathValue]
  congr 1
  funext a
  congr 1
  split
  · rfl
  · exact (K.version hK).eval_eq_of_rules (K.outputTest f) 0 T a.2 (s z) (obs z)
      (fun t j i a => hz i t j a)
end Policy
end MemoryPrecision.Kernel


end

end OAI
