import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateGeometry
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Profiles

namespace OAI

/-! Three explicit smooth transition clocks leave collars between the
vertical, horizontal, and final vertical motions of each address gate. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff

def firstWeight (a T : ℝ) : ℝ → ℝ := smoothRamp (a + T / 12) (a + T / 4)
def secondWeight (a T : ℝ) : ℝ → ℝ := smoothRamp (a + 5 * T / 12) (a + 7 * T / 12)
def thirdWeight (a T : ℝ) : ℝ → ℝ := smoothRamp (a + 3 * T / 4) (a + 11 * T / 12)

theorem weights_smooth (a T : ℝ) :
    ContDiff ℝ ∞ (firstWeight a T) ∧ ContDiff ℝ ∞ (secondWeight a T) ∧
      ContDiff ℝ ∞ (thirdWeight a T) :=
  ⟨smoothRamp_smooth _ _, smoothRamp_smooth _ _, smoothRamp_smooth _ _⟩

theorem weights_slots (a : ℝ) {T : ℝ} (hT : 0 < T) (t : ℝ) :
    (secondWeight a T t = 0 ∧ thirdWeight a T t = 0) ∨
      (firstWeight a T t = 1 ∧ thirdWeight a T t = 0) ∨
      (firstWeight a T t = 1 ∧ secondWeight a T t = 1) := by
  unfold firstWeight secondWeight thirdWeight
  by_cases h₂ : t ≤ a + 5 * T / 12
  · left
    exact ⟨smoothRamp_before (by linarith) h₂,
      smoothRamp_before (by linarith) (by linarith)⟩
  · right
    by_cases h₃ : t ≤ a + 3 * T / 4
    · left
      exact ⟨smoothRamp_after (by linarith) (by linarith),
        smoothRamp_before (by linarith) h₃⟩
    · right
      exact ⟨smoothRamp_after (by linarith) (by linarith),
        smoothRamp_after (by linarith) (by linarith)⟩

theorem thirdWeight_le_firstWeight (a : ℝ) {T : ℝ} (hT : 0 < T) (t : ℝ) :
    thirdWeight a T t ≤ firstWeight a T t := by
  rcases weights_slots a hT t with h | h | h
  · rw [h.2]
    exact (smoothRamp_range _ _ _).1
  · rw [h.1]
    exact (smoothRamp_range _ _ _).2
  · rw [h.1]
    exact (smoothRamp_range _ _ _).2

def scheduledCenter (a T S S' : ℝ) (k target : ℕ) (terminal : Bool) (t : ℝ) : Plane :=
  gateCenter S S' k target terminal (firstWeight a T t) (secondWeight a T t)
    (thirdWeight a T t)

theorem scheduledCenter_smooth (a T S S' : ℝ) (k target : ℕ) (terminal : Bool) :
    ContDiff ℝ ∞ (scheduledCenter a T S S' k target terminal) := by
  obtain ⟨h₁, h₂, h₃⟩ := weights_smooth a T
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun t => (1 - secondWeight a T t) * S * k +
      secondWeight a T t * S' * target)
    fun_prop
  · change ContDiff ℝ ∞ (fun t => -(1 - firstWeight a T t) * S +
      (firstWeight a T t - thirdWeight a T t) * (-((k : ℝ) + 2) * S) +
      thirdWeight a T t * (if terminal then S' else -S'))
    fun_prop

theorem scheduledCenter_initial (a : ℝ) {T : ℝ} (hT : 0 < T)
    (S S' : ℝ) (k target : ℕ) (terminal : Bool) :
    scheduledCenter a T S S' k target terminal a = ![S * k, -S] := by
  have h₁ : firstWeight a T a = 0 := smoothRamp_before (by linarith) (by linarith)
  have h₂ : secondWeight a T a = 0 := smoothRamp_before (by linarith) (by linarith)
  have h₃ : thirdWeight a T a = 0 := smoothRamp_before (by linarith) (by linarith)
  rw [scheduledCenter, h₁, h₂, h₃, gateCenter_initial]

theorem scheduledCenter_final (a : ℝ) {T : ℝ} (hT : 0 < T)
    (S S' : ℝ) (k target : ℕ) (terminal : Bool) :
    scheduledCenter a T S S' k target terminal (a + T) =
      ![S' * target, if terminal then S' else -S'] := by
  have h₁ : firstWeight a T (a + T) = 1 := smoothRamp_after (by linarith) (by linarith)
  have h₂ : secondWeight a T (a + T) = 1 := smoothRamp_after (by linarith) (by linarith)
  have h₃ : thirdWeight a T (a + T) = 1 := smoothRamp_after (by linarith) (by linarith)
  rw [scheduledCenter, h₁, h₂, h₃, gateCenter_final]

theorem scheduledCenter_separated (a : ℝ) {T S S' : ℝ} (hT : 0 < T)
    (hS : 0 ≤ S) (hSS' : S ≤ S') {k l k' l' : ℕ}
    (hkl : k ≠ l) (htarget : k' ≠ l') (hk hl : Bool) (t : ℝ) :
    ∃ j : Fin 2, S ≤ |scheduledCenter a T S S' k k' hk t j -
      scheduledCenter a T S S' l l' hl t j| :=
  gateCenter_separated hS hSS' hkl htarget hk hl _ _ _ (weights_slots a hT t)

theorem scheduledCenter_nonterminal (a : ℝ) {T S S' : ℝ} (hT : 0 < T)
    (hS : 0 ≤ S) (hSS' : S ≤ S') (k target : ℕ) (t : ℝ) :
    scheduledCenter a T S S' k target false t 1 ≤ -S :=
  nonterminal_gate_below hS hSS' k target (smoothRamp_range _ _ _).1
    (thirdWeight_le_firstWeight a hT t)

end ForcedComputation.ExpandingDetector

end

end OAI
