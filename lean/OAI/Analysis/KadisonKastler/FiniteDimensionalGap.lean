import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Finite dimensionality across a small algebra gap

A finite net in the second unit ball produces a net of radius less than
one in the first unit ball. Riesz's lemma then forces finite dimensionality.
Only the fixed small constant needed in the type-stability argument is used.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem finiteDimensional_of_unitBall_approx
    (S T : Submodule ℂ B) [FiniteDimensional ℂ T]
    (happrox : ∀ x : S, ‖x‖ ≤ 1 →
      ∃ y : T, ‖y‖ ≤ 1 ∧ ‖(x : B) - (y : B)‖ < 1 / 10) :
    FiniteDimensional ℂ S := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := (isCompact_closedBall (0 : T) 1).finite_cover_balls
    (show (0 : ℝ) < 1 / 10 by norm_num)
  let center (y : T) : S := if h : ∃ x : S, ‖(x : B) - (y : B)‖ < 1 / 5
    then h.choose else 0
  have hcenter (y : T) (h : ∃ x : S, ‖(x : B) - (y : B)‖ < 1 / 5) :
      ‖(center y : B) - (y : B)‖ < 1 / 5 := by
    dsimp [center]
    rw [dite_eq_left h]
    exact h.choose_spec
  let L : Submodule ℂ S := Submodule.span ℂ (center '' t)
  have hfg : L.FG := Submodule.fg_span (ht.image center)
  have : FiniteDimensional ℂ L := Module.Finite.of_fg hfg
  by_contra hdim
  have hproper : ∃ x : S, x ∉ L := by
    by_contra! h
    have htop : L = ⊤ := top_unique (fun x _ => h x)
    rw [htop] at hfg
    exact hdim (Module.Finite.of_fg_top hfg)
  obtain ⟨x, _, hxnorm, hfar⟩ := riesz_lemma_of_lt_one
    (Submodule.closed_of_finiteDimensional L) hproper (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨y, hynorm, hxy⟩ := happrox x hxnorm.le
  have hyball : y ∈ Metric.closedBall (0 : T) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hynorm
  obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (hcover hyball)
  have hyz' : ‖(y : B) - (z : B)‖ < 1 / 10 := by
    rw [Metric.mem_ball, dist_eq_norm] at hyz
    change ‖((y - z : T) : B)‖ < 1 / 10 at hyz
    exact hyz
  have hxz : ‖(x : B) - (z : B)‖ < 1 / 5 := by
    have hh : ‖(x : B) - (z : B)‖ ≤
        ‖(x : B) - (y : B)‖ + ‖(y : B) - (z : B)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (x : B) (y : B) (z : B)
    linarith
  have hcz := hcenter z ⟨x, hxz⟩
  have hnear : ‖x - center z‖ < 2 / 5 := by
    have hh : ‖(x : B) - (center z : B)‖ ≤
        ‖(x : B) - (z : B)‖ + ‖(z : B) - (center z : B)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (x : B) (z : B) (center z : B)
    rw [norm_sub_rev (z : B) (center z : B)] at hh
    change ‖(x : B) - (center z : B)‖ < 2 / 5
    linarith
  have hlow := hfar (center z) (Submodule.subset_span ⟨z, hzt, rfl⟩)
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A neighbor of a finite-dimensional algebra at the constant used in
the finite-type theorem is itself finite-dimensional. -/
theorem finiteDimensional_of_near_finiteDimensional
    (M N : VonNeumannAlgebra H) [FiniteDimensional ℂ (Algebra N)]
    (hgap : kkDistance M N < 1 / 10) : FiniteDimensional ℂ (Algebra M) := by
  apply finiteDimensional_of_unitBall_approx M.toStarSubalgebra.toSubmodule
    N.toStarSubalgebra.toSubmodule
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx ⟨x.property, hx⟩ hgap
  exact ⟨⟨y, hy.1⟩, hy.2, hxy⟩

end

end KadisonKastler

end OAI
