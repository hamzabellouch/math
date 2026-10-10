import OAI.Combinatorics.ContingencyTables.Counting.CompanionCanonicalPhaseLaw
import OAI.Combinatorics.ContingencyTables.Counting.CountingActualInitialization

namespace OAI

/-! # The executed original-input controls are exactly the source settings -/
namespace ContingencyTables.CountingActualSettings
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}
variable (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
variable (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
variable (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
local notation "A" => ComputedCountingParameters.data hEK r c b hne epsilon he
local notation "s" => ComputedCountingParameters.settings hEK r c b hne epsilon he
local notation "e" => CountingBaseProgram.half (TreeFraction.repr epsilon)
local notation "v" => CountingPreparedState.start A (RootedPhaseHistory.Settings.K s)
  (ComputedCountingParameters.binCount_pos r c b epsilon he)
local notation "p" => CompanionInitializedRestartProgram.parameters A (RootedPhaseHistory.Settings.H s)
  (CompanionTargetMixing.restartTime A (RootedPhaseHistory.Settings.H s) (RootedPhaseHistory.Settings.L s))
  (RootedPhaseHistory.Settings.N s) (RootedPhaseHistory.Settings.n s) (RootedPhaseHistory.Settings.L s) e

lemma precision : CountingPhaseParametersProgram.precision p=(s).k := by
  have h := CountingComputedSettings.precision_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at h
  exact h

lemma observations : CountingPhaseParametersProgram.observations p=(s).N := by
  unfold CompanionInitializedRestartProgram.parameters
  rw [CountingPhaseParametersProgram.observations_val,CountingBaseProgram.half_val,
    TreeFraction.val_repr he.le]
  rfl

lemma noise : TreeFraction.val (CountingPhaseParametersProgram.noise p)=(s).xi := by
  have h := CountingComputedSettings.noise_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at h
  exact h

lemma noise_pos : 0<TreeFraction.val (CountingPhaseParametersProgram.noise p) := by
  rw [noise hEK r c b hne epsilon he]
  exact CountingPhaseSchedule.noise_pos _ _ _ _ _

lemma raw_settings : CompanionCanonicalPhaseLaw.rawSettings A (s).C (s).K (s).H (s).N (s).n (s).L
    e (s).hK (s).hW v=s := by
  apply CompanionCanonicalPhaseLaw.rawSettings_eq
  · exact precision hEK r c b hne epsilon he
  · exact observations hEK r c b hne epsilon he
  · rfl
  · exact noise hEK r c b hne epsilon he
  · exact CountingPreparedState.start_transport hEK r c b hne epsilon he

lemma coefficient_pos : 0<(s).C := ComputedCountingParameters.coefficient_pos r c b epsilon he

lemma height : (s).H ≤ rationalHeight A (s).C :=
  (ComputedCountingParameters.phases_height hEK r c b hne epsilon he).le

lemma bin_width : ((s).K:ℝ)=binWidth A (s).C :=
  ComputedCountingParameters.binCount_cast hEK r c b hne epsilon he

end
end ContingencyTables.CountingActualSettings

end OAI
