import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

abbrev Prefix (S : Type*) (n : ℕ) := Finset.Iic n → S
abbrev Path (S : Type*) := ℕ → S

def historyKernel (step : ℕ → S → PMF S) (n : ℕ) : Kernel (Prefix S n) S :=
  Kernel.ofFunOfCountable (fun h => (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)

instance historyKernel_isMarkov (step : ℕ → S → PMF S) (n : ℕ) :
    IsMarkovKernel (historyKernel step n) :=
  ⟨fun h => by
    change IsProbabilityMeasure ((step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)
    infer_instance⟩

def pathLaw (step : ℕ → S → PMF S) (s₀ : S) : Measure (Path S) :=
  Kernel.traj (X := fun _ => S) (historyKernel step) 0 (fun _ => s₀)

instance pathLaw_isProbability (step : ℕ → S → PMF S) (s₀ : S) :
    IsProbabilityMeasure (pathLaw step s₀) := by
  unfold pathLaw
  infer_instance

def filtration : Filtration ℕ (inferInstance : MeasurableSpace (Path S)) :=
  Filtration.piLE

def stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) (ω : Path S) : ℝ :=
  f (frestrictLe n ω) (ω (n + 1))

lemma measurable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) :
    Measurable (stepObservable n f) := by
  have hm : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  exact (measurable_of_countable (Function.uncurry f)).comp hm

lemma integrable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ)
    (ν : Measure (Path S)) [IsFiniteMeasure ν] : Integrable (stepObservable n f) ν := by
  have hmap : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hi : Integrable (Function.uncurry f)
      (ν.map (fun ω : Path S => (frestrictLe n ω, ω (n + 1)))) := .of_finite
  exact hi.comp_measurable hmap

lemma map_next_traj (step : ℕ → S → PMF S) (n : ℕ) (h : Prefix S n) :
    (Kernel.traj (X := fun _ => S) (historyKernel step) n h).map (fun ω : Path S => ω (n + 1)) =
      (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure := by
  rw [← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
  rfl

lemma integral_stepObservable_traj (step : ℕ → S → PMF S) (n : ℕ)
    (h : Prefix S n) (f : Prefix S n → S → ℝ) :
    (∫ ω, stepObservable n f ω ∂Kernel.traj (X := fun _ => S) (historyKernel step) n h) =
      ∑ s, (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f h s := by
  rw [Kernel.integral_traj h (measurable_stepObservable n f).stronglyMeasurable.aestronglyMeasurable]
  have hfreeze (ω : Path S) :
      stepObservable n f (Function.updateFinset ω (Finset.Iic n) h) = f h (ω (n + 1)) := by
    have hp : frestrictLe n (Function.updateFinset ω (Finset.Iic n) h) = h := by
      funext j
      simp [frestrictLe, Function.updateFinset, j.property]
    simp [stepObservable, hp, Function.updateFinset]
  simp_rw [hfreeze]
  rw [← integral_map (measurable_pi_apply (n + 1)).aemeasurable
    (measurable_of_countable (f h)).stronglyMeasurable.aestronglyMeasurable,
    map_next_traj, PMF.integral_eq_sum]
  rfl

theorem condExp_stepObservable (step : ℕ → S → PMF S) (s₀ : S)
    (n : ℕ) (f : Prefix S n → S → ℝ) :
    (pathLaw step s₀)[stepObservable n f | filtration n] =ᵐ[pathLaw step s₀]
      fun ω => ∑ s, (step n (ω n) s).toReal * f (frestrictLe n ω) s := by
  have h := Kernel.condExp_traj (X := fun _ => S) (κ := historyKernel step) (Nat.zero_le n)
    (x₀ := fun _ => s₀) (integrable_stepObservable n f (pathLaw step s₀))
  filter_upwards [h] with ω hω
  change (pathLaw step s₀)[stepObservable n f | filtration n] ω = _ at hω ⊢
  rw [hω, integral_stepObservable_traj]
  rfl

theorem map_prefix_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => S) (historyKernel step) 0 n (fun _ => s₀) :=
  Kernel.traj_map_frestrictLe_apply (X := fun _ => S) (κ := historyKernel step) 0 n (fun _ => s₀)

theorem map_prefix_next_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) =
      ((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n := by
  rw [map_prefix_pathLaw]
  exact (Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => S) (κ := historyKernel step) (x₀ := fun _ => s₀) (Nat.zero_le n)).symm

end Balanced.FiniteHistory

end

end OAI
