import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BoundedProfiles

namespace OAI

/-! Ordered directional derivatives can be grouped into time derivatives and
spatial derivatives, by the symmetry already proved for the flat calculus. -/

noncomputable section
open scoped ContDiff
open ShearFlows

namespace ForcedComputation

theorem mixedDerivative_perm {V : Velocity} (hV : ContDiff ℝ ∞ V)
    {α β : List (Fin 4)} (h : α.Perm β) : mixedDerivative V α = mixedDerivative V β := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [mixedDerivative, ih]
  | swap a b α => exact mixedDerivative_commute hV α b a
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem time_spatial_normal_form (α : List (Fin 4)) :
    ∃ n : ℕ, ∃ β : List (Fin 3), α.Perm (List.replicate n 0 ++ β.map Fin.succ) := by
  induction α with
  | nil => exact ⟨0, [], List.Perm.refl _⟩
  | cons a α ih =>
    obtain ⟨n, β, h⟩ := ih
    refine Fin.cases ?_ (fun j => ?_) a
    · refine ⟨n + 1, β, ?_⟩
      simpa only [List.replicate_succ, List.cons_append] using h.cons 0
    · refine ⟨n, j :: β, ?_⟩
      have he := (List.perm_append_comm :
        ([j.succ] ++ List.replicate n 0).Perm (List.replicate n 0 ++ [j.succ])).append_right
        (β.map Fin.succ)
      exact (h.cons j.succ).trans (by simpa only [List.singleton_append, List.map_cons,
        List.append_assoc, List.cons_append, List.nil_append] using he)

theorem mixedDerivative_time_spatial {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (n : ℕ) (β : List (Fin 3)) (t : ℝ) (x : Space) :
    mixedDerivative V (List.replicate n 0 ++ β.map Fin.succ) (t, x) =
      iteratedDeriv n (fun s => spatialWord β (fun y => V (s, y)) x) t := by
  have he := iteratedDeriv_eq_mixedTime (spatialPhase_smooth hV β) n t x
  calc
    _ = mixedDerivative (spatialPhase V β) (List.replicate n 0) (t, x) := by
      rw [spatialPhase_eq_mixed hV, mixedDerivative_append]
    _ = _ := he.symm

end ForcedComputation

end

end OAI
