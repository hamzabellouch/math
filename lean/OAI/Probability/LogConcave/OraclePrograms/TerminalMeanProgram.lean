import Mathlib
import OAI.Probability.LogConcave.Analysis.GaussianAffineNormMoment
import OAI.Probability.LogConcave.Dynamics.Squared
import OAI.Probability.LogConcave.OraclePrograms.ReservedProgram

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Program Coupling
open scoped Classical BigOperators NNReal

variable {d : ℕ}

def terminalMeanProgram (d : ℕ) (r σ : ℝ) : SeedProgram d where
  slots := 2
  calls := 1
  program := SeedCompiler.terminalMean d r σ
  shift := SeedCompiler.terminalShift 1

def terminalReservedProgram (d : ℕ) (r η : ℝ) : ReservedProgram d where
  slots := 2
  calls := 1
  pre := oneQuery (fun p => p.1+r • p.2 0) (by fun_prop)
    (fun p => p.1.2 0-r • p.2.2+(Real.sqrt 3*η/2) • p.1.2 1) (by fun_prop)
  shift := SeedCompiler.terminalShift 1
  reserve := η/2

lemma terminalReservedProgram_pre_run (r η : ℝ) (V : Point d → ℝ)
    (x : Point d) (g : Fin 2 → Point d) :
    (terminalReservedProgram d r η).pre.run V (x,g)=
      g 0-r • gradient V (x+r • g 0)+(Real.sqrt 3*η/2) • g 1 := by
  exact oneQuery_run (fun p : Point d × (Fin 2 → Point d) => p.1+r • p.2 0) (by fun_prop)
    (fun p => p.1.2 0-r • p.2.2+(Real.sqrt 3*η/2) • p.1.2 1) (by fun_prop) V (x,g)

abbrev gaussianTape (d n : ℕ) : Measure (Fin n → Point d) :=
  Measure.pi fun _ => stdGaussian (Point d)

variable {slotCount : ℕ}

lemma gaussianTape_eval (i : Fin slotCount) :
    (gaussianTape d slotCount).map (fun g => g i)=stdGaussian (Point d) :=
  (measurePreserving_eval (fun _ : Fin slotCount => stdGaussian (Point d)) i).map_eq

lemma gaussianTape_integrable_eval (f : Point d → ℝ) (_hf : Measurable f)
    (hi : Integrable f (stdGaussian (Point d))) (i : Fin slotCount) :
    Integrable (fun g : Fin slotCount → Point d => f (g i)) (gaussianTape d slotCount) := by
  have hh : Integrable f ((gaussianTape d slotCount).map (fun g => g i)) := by rw [gaussianTape_eval]; exact hi
  exact hh.comp_measurable (measurable_pi_apply i)

lemma gaussianTape_integral_eval (f : Point d → ℝ) (hf : Measurable f) (i : Fin slotCount) :
    (∫g : Fin slotCount → Point d,f (g i) ∂gaussianTape d slotCount)=∫z,f z ∂stdGaussian (Point d) :=
  (measurePreserving_eval (fun _ : Fin slotCount => stdGaussian (Point d)) i).hasLaw.integral_comp hf.aestronglyMeasurable

theorem terminalMeanProgram_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r : ℝ} (hr : 0≤r) (hl : (lam:ℝ)*r^2≤1/2) (σ : ℝ) :
    SquaredAt (gaussianTape d 2) (stdGaussian (Point d))
      (fun g => (terminalMeanProgram d r σ).program.run F (x,g))
      (fun g => primitiveExpectedField F x r+σ • g)
      ((2*((lam:ℝ)*r))^2*(2*(Real.pi*Real.sqrt d+r*‖primitiveField F x r 0‖)^2+2*d)) := by
  have hm : Measurable (fun z => ‖primitiveField F x r z-primitiveExpectedField F x r‖^2) :=
    ((primitiveField_contDiff hF x r).continuous.measurable.sub measurable_const).norm.pow_const 2
  have he (g : Fin 2 → Point d) :
      ‖(terminalMeanProgram d r σ).program.run F (x,g)-
        (primitiveExpectedField F x r+σ • g 1)‖^2=
      ‖primitiveField F x r (g 0)-primitiveExpectedField F x r‖^2 := by
    change ‖(SeedCompiler.terminalMean d r σ).run F (x,g)-_‖^2=_
    rw [SeedCompiler.terminalMean_run,add_sub_add_right_eq_sub]
    rfl
  have ht := terminal_mean_squared_error hF x hr hl
  apply SquaredAt.of_joint (gaussianTape d 2) (gaussianTape d 2) (stdGaussian (Point d))
    id (fun g => g 1) measurable_id (measurable_pi_apply 1) Measure.map_id (gaussianTape_eval 1)
    _ _ ?_ (by fun_prop)
  · simpa only [id_eq,he] using gaussianTape_integrable_eval _ hm ht.1 (0:Fin 2)
  · simpa only [id_eq,he,gaussianTape_integral_eval _ hm (0:Fin 2)] using ht.2
  · change Measurable (fun g => (SeedCompiler.terminalMean d r σ).run F (x,g))
    simp only [SeedCompiler.terminalMean_run]
    have hg := hF.gradient_lipschitz.continuous.measurable
    fun_prop
end LogConcaveSampling

end

end

end OAI
