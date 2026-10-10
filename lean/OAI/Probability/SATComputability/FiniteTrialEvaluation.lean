import OAI.Probability.SATComputability.RationalHierarchy
import OAI.Probability.DilutedSpin.QSubtreePotential

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

local instance finiteTrialEvaluationMeasurable (X : TopCat) : MeasurableSpace X := borel X
local instance finiteTrialEvaluationBorel (X : TopCat) : BorelSpace X := ⟨rfl⟩

noncomputable def finiteLogMean {ι : Type} [Fintype ι] :
    (r : ℕ) → ((ι → ℝ) → ℝ) → (Fin r → ℝ) → (ι → RationalTree r) → ℝ
  | 0, g, _, t => g (fun i => Rat.cast (K := ℝ) (t i))
  | r+1, g, m, t => by
    classical
    exact Real.log ((FiniteLaw.pi (fun i => (t i).2.1.toLaw)).expect (fun a =>
      Real.exp (m 0 * finiteLogMean r g (fun j => m j.succ) (fun i => (t i).2.2 (a i))))) / m 0

theorem rationalTreeValue_asProbability (r : ℕ) (t : RationalTree (r+1)) :
    rationalTreeValue (r+1) t =
      t.2.1.toLaw.asProbability (fun a => rationalTreeValue r (t.2.2 a)) := by
  rfl

theorem finiteLogMean_eq {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (t : ι → RationalTree r) :
    finiteLogMean r g m t = logMean r g m (fun i => rationalTreeValue r (t i)) := by
  classical
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [finiteLogMean, logMean, rationalTreeValue_asProbability]
    rw [FiniteLaw.integral_pi_asProbability]
    congr 2
    apply FiniteLaw.expect_congr
    intro a
    rw [ih]

noncomputable def finiteTrialLog {ι : Type} [Fintype ι] (r : ℕ)
    (t : RationalTree (r+1)) (m : Fin r → ℝ) (g : (ι → ℝ) → ℝ) : ℝ := by
  classical
  exact (FiniteLaw.pi (fun _ : ι => t.2.1.toLaw)).expect
    (fun a => finiteLogMean r g m (fun i => t.2.2 (a i)))

theorem finiteTrialLog_eq {ι : Type} [Fintype ι] (r : ℕ)
    (t : RationalTree (r+1)) (m : Fin r → ℝ) (g : (ι → ℝ) → ℝ) :
    finiteTrialLog r t m g = trialLog r (rationalTreeValue (r+1) t) m g := by
  classical
  rw [trialLog, rationalTreeValue_asProbability, FiniteLaw.integral_pi_asProbability]
  apply FiniteLaw.expect_congr
  intro a
  exact finiteLogMean_eq r g m _

end FixedClauseThreshold.Computability

end OAI
