import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.NonzeroFiber

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

lemma veryGenerally_of_nonempty_open
    {Y : SmoothProjectiveVariety} {P : Y.ComplexPoint → Prop}
    {U : Y.scheme.Opens} (hne : U ≠ ⊥)
    (hP : ∀ y : Y.ComplexPoint, y.point ∈ U → P y) : VeryGenerally Y P := by
  classical
  refine ⟨fun _ => U.compl, fun _ => ?_, ?_⟩
  · intro htop
    change U.compl = ⊤ at htop
    apply hne
    apply le_bot_iff.mp
    intro x hx
    have hc : x ∈ U.compl := by rw [htop]; trivial
    exact (hc hx).elim
  · intro y hy
    apply hP y
    exact Classical.not_not.mp (hy 0)

 

theorem exists_open_fiber_kodaira_ne_bot
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (hE : E.kodaira ≠ ⊥) :
    ∃ U : Y.scheme.Opens, U ≠ ⊥ ∧ U ≤ D.complement ∧
      ∀ (y : Y.ComplexPoint), y.point ∈ U →
        ∀ F : FiberModel f.toBoundaryFibration y, F.boundary.kodaira ≠ ⊥ := by
  classical
  have hs : ∃ (m : ℕ), 0 < m ∧ ∃ s : X.RationalPluriform m,
      s ∈ E.sections m ∧ s ≠ 0 := by
    by_contra! h
    exact hE (E.kodaira_eq_bot_iff.mpr h)
  obtain ⟨m, hm, s, hs, hn⟩ := hs
  obtain ⟨U, hne, hU, hf⟩ := exists_open_nonzero_fiber_pluriform f m hm s hs hn
  refine ⟨U, hne, hU, ?_⟩
  intro y hy F hF
  obtain ⟨σ, hσ, hnσ⟩ := hf y hy F
  exact hnσ (F.boundary.kodaira_eq_bot_iff.mp hF m hm σ hσ)

 

theorem veryGenerally_fiber_negative_branch
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) :
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      ∀ F : FiberModel f.toBoundaryFibration y, F.boundary.kodaira = ⊥ →
        E.kodaira = D.kodaira + F.boundary.kodaira ∧
        ∀ (m : ℕ), 0 < m → ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by
  classical
  by_cases hE : E.kodaira = ⊥
  · have hne : D.complement ≠ ⊥ := by
      intro hD
      have hg := D.generic_mem_complement
      rw [hD] at hg
      exact hg
    apply veryGenerally_of_nonempty_open hne
    intro y hy
    refine ⟨hy, fun F hF => ⟨?_, E.kodaira_eq_bot_iff.mp hE⟩⟩
    simpa only [hF, WithBot.add_bot] using hE
  · obtain ⟨U, hne, hU, hf⟩ := exists_open_fiber_kodaira_ne_bot f hE
    apply veryGenerally_of_nonempty_open hne
    intro y hy
    exact ⟨hU hy, fun F hF => ((hf y hy F) hF).elim⟩

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI
