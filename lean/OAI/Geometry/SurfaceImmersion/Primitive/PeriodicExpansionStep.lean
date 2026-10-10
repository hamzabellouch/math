import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFamilySupport

namespace OAI

/-! The triangular cancellation step in the finite periodic metric expansion. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The pointwise geometry used by the periodic coefficient recursion. -/
structure Geometry (v : A) where
  plane : A → Submodule ℝ E
  Y : A → E
  C : A → E
  X₀ : A → E
  smoothY : ContDiff ℝ ∞ Y
  smoothC : ContDiff ℝ ∞ C
  smoothX₀ : ContDiff ℝ ∞ X₀
  derivativeY : ∀ p, fderiv ℝ Y p v = C p
  gram_ne : ∀ p, PeriodicCorrector.gramDet (Y p) (C p) ≠ 0
  perpY : ∀ p w, w ∈ plane p → inner ℝ (Y p) w = 0
  perpC : ∀ p w, w ∈ plane p → inner ℝ (C p) w = 0
  perpX₀ : ∀ p w, w ∈ plane p → inner ℝ (X₀ p) w = 0
  V : Family A E
  V_mem : ∀ p t, V.val p t ∈ plane p
  q : A → ℝ
  smoothq : ContDiff ℝ ∞ q
  q_pos : ∀ p, 0 < q p
  circle : ∀ p t, inner ℝ (V.val p t) (V.val p t) = q p

namespace Geometry

variable {v : A} (g : Geometry (E := E) v)

def longitudinal : Family A E := Family.constant g.X₀ g.smoothX₀ + g.V

def transverse : Family A E := Family.constant g.Y g.smoothY

theorem exists_system (h j e : Family A ℝ)
    (hh : ∀ p, average (h.val p) = 0) (hj : ∀ p, average (j.val p) = 0)
    (he : ∀ p, average (e.val p) = 0) :
    ∃ U : Family A E, (∀ p, average (U.val p) = 0) ∧
      g.transverse.inner U.angle = h ∧
      g.transverse.inner (U.slow v) = j ∧
      (g.longitudinal.inner U.angle).fluct = e ∧
      (∀ O : Set A, IsOpen O → (∀ p ∈ O, h.val p = 0) →
        (∀ p ∈ O, j.val p = 0) → (∀ p ∈ O, e.val p = 0) → ∀ p ∈ O, U.val p = 0) := by
  obtain ⟨U, D, hUs, _, hU0, hUd, hYd, hYs, hX, hzero⟩ :=
    PeriodicCorrector.solve_full_smooth_family v g.plane g.Y g.C g.X₀
      g.smoothY g.smoothC g.smoothX₀ g.derivativeY g.gram_ne
      g.perpY g.perpC g.perpX₀ g.V.val g.V_mem g.V.smooth
      g.q g.smoothq g.q_pos g.circle h.val j.val e.val h.smooth j.smooth e.smooth hh hj he
  let U' : Family A E := ⟨U, hUs⟩
  have hangle (p : A) (t : Period) : U'.angle.val p t = D p t := by
    refine Quotient.inductionOn' t ?_
    intro x
    exact (angle_hasDerivAt hUs p x).unique (hUd p x)
  refine ⟨U', hU0, ?_, ?_, ?_, hzero⟩
  · ext p t
    change inner ℝ (g.Y p) (U'.angle.val p t) = h.val p t
    rw [hangle]
    exact hYd p t
  · ext p t
    refine Quotient.inductionOn' t ?_
    intro x
    exact hYs p x
  · ext p t
    change fluctuation (fun t => inner ℝ (g.X₀ p + g.V.val p t) (U'.angle.val p t)) t = e.val p t
    simp only [hangle]
    exact congrFun (hX p) t

/-- One new coefficient cancels the current xx and xy fluctuations and
the next yy fluctuation, as in the manuscript's triangular recursion. -/
theorem exists_cancellation (b c d : Family A ℝ) :
    ∃ U : Family A E, (∀ p, average (U.val p) = 0) ∧
      (g.transverse.inner U.angle + b).fluct = 0 ∧
      (g.longitudinal.inner U.angle + c).fluct = 0 ∧
      ((2 : ℝ) • g.transverse.inner (U.slow v) + d).fluct = 0 ∧
      (∀ O : Set A, IsOpen O → (∀ p ∈ O, b.val p = 0) →
        (∀ p ∈ O, c.val p = 0) → (∀ p ∈ O, d.val p = 0) → ∀ p ∈ O, U.val p = 0) := by
  have hs (a : ℝ) (f : Family A ℝ) (p : A) :
      average ((a • f.fluct).val p) = 0 := by
    change average (fun t => a • f.fluct.val p t) = 0
    rw [average_const_smul, f.fluct_mean_zero, smul_zero]
  obtain ⟨U, hU0, hY, hS, hX, hzero⟩ := g.exists_system
    ((-1 : ℝ) • b.fluct) ((-1 / 2 : ℝ) • d.fluct) ((-1 : ℝ) • c.fluct)
    (hs _ _) (hs _ _) (hs _ _)
  refine ⟨U, hU0, ?_, ?_, ?_, ?_⟩
  · rw [Family.fluct_add, hY, Family.fluct_smul, Family.fluct_fluct]
    module
  · rw [Family.fluct_add, hX]
    module
  · rw [Family.fluct_add, Family.fluct_smul, hS, Family.fluct_smul, Family.fluct_fluct]
    module

  · intro O hO hb hc hd
    have hz (a : ℝ) (f : Family A ℝ) (hf : ∀ p ∈ O, f.val p = 0) :
        ∀ p ∈ O, (a • f.fluct).val p = 0 := by
      intro p hp
      change a • f.fluct.val p = 0
      rw [f.fluct_zero_at (hf p hp), smul_zero]
    exact hzero O hO (hz _ _ hb) (hz _ _ hd) (hz _ _ hc)

end Geometry
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
