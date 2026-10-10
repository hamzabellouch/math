import OAI.Probability.DilutedSpin.ReservoirBondEnergy
import OAI.Probability.DilutedSpin.ReservoirSitePoisson

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ}

noncomputable def clippedSiteInsertion (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) : ℝ :=
  insertionPoisson M C H N L u
    (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
    (fun _ z => cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2)) r
noncomputable def clippedBondInsertion (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) : ℝ :=
  insertionPoisson M C H N L u
    (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
    (fun _ θ => cavityBondEnergy (fun j => clipSample C (θ j))) r
noncomputable def clippedCavityProxy (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) : ℝ := Real.log 2+
  clippedSiteInsertion M C H N L u (M.alpha*p)-
  clippedBondInsertion M C H N L u (M.alpha*(p-1:ℕ))

lemma clippedCavityProxy_eq (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H) :
    clippedCavityProxy M C H N L u=cavityProxy M C H N L u := by
  have heθ : ∀ k,∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),
      (fun j => clipSample C (θ j))=θ := by
    intro k
    have hh := Filter.eventually_all.mpr (fun j =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => M.disorder.toMeasure) (i := j)).eventually hθ)
    filter_upwards [hh] with θ hθ
    exact funext (fun j => clipSample_eq (hθ j))
  have hes r : clippedSiteInsertion M C H N L u r=
      insertionPoisson M C H N L u
        (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
        (fun _ z => cavitySiteEnergy z.1 z.2) r := by
    unfold clippedSiteInsertion insertionPoisson
    apply integral_congr_ae
    filter_upwards [] with k
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (heθ k),
      Measure.quasiMeasurePreserving_snd.ae hh] with z hz hh
    rw [hz,clipReal_eq hh]
  have heb r : clippedBondInsertion M C H N L u r=
      insertionPoisson M C H N L u (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
        (fun _ θ => cavityBondEnergy θ) r := by
    unfold clippedBondInsertion insertionPoisson
    apply integral_congr_ae
    filter_upwards [] with k
    apply integral_congr_ae
    filter_upwards [heθ k] with θ hθ
    rw [hθ]
  simp only [clippedCavityProxy,cavityProxy,hes,heb]

end DilutedSpinGlass.UniversalDictionary

end

end OAI
