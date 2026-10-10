import OAI.Probability.PosteriorReplicas.Regression.LearnerBasics
import OAI.Probability.PosteriorReplicas.Regression.StreamIntegrals

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

def forcedRun (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → State M
  | 0 => (L.initialChoice ω).2
  | n+1 =>
    if hn : n < T then
      (L.transition (n+1) ω (L.forcedRun s ω x n) (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).2
    else L.forcedRun s ω x n

lemma forcedRun_eq_route (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.forcedRun s ω x n =
      streamRoute (fun t j obs => (L.transition t ω j obs).2) 0 n (L.initialChoice ω).2
        ((fun i => x (Fin.castLE hn i)), (fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [forcedRun, dite_eq_left (by omega), ih (by omega)]
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫), streamRoute_snoc]
    simp only [zero_add, real_inner_comm]

lemma run_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    (n : ℕ) (hn : n ≤ T) :
    (L.run s ω x n = .inl (L.forcedRun s ω x n)) ∨
      ∃ t ≤ n, L.run s ω x n = .inr (t, L.forcedRun s ω x t) := by
  induction n with
  | zero =>
    simp only [run, start, forcedRun]
    split
    · exact Or.inr ⟨0, le_rfl, rfl⟩
    · exact Or.inl rfl
  | succ n ih =>
    rcases ih (by omega) with h | ⟨t,ht,h⟩
    · have hnt : n < T := by omega
      rw [run, h]
      simp only [dite_eq_left hnt, forcedRun]
      split
      · exact Or.inr ⟨n+1, le_rfl, by simp [forcedRun, hnt]⟩
      · exact Or.inl rfl
    · right
      exact ⟨t, by omega, by rw [run, h]⟩

lemma terminal_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    ∃ t ≤ T, L.terminal s ω x = (t, L.forcedRun s ω x t) := by
  rcases L.run_forced_witness s ω x T le_rfl with h | ⟨t,ht,h⟩
  · exact ⟨T, le_rfl, by simp [terminal, h]⟩
  · exact ⟨t, ht, by simp [terminal, h]⟩

end Learner

end PosteriorRegression
end

end OAI
