import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicExpansionStep
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialVector

namespace OAI

/-! The complete periodic system with its explicit solution retained in the
family interface, for propagation of polynomial coefficient representations. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}
namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

theorem exists_system_formula (h j e : Family O ℝ)
    (hh : ∀ p ∈ O, average (h.val p) = 0) (hj : ∀ p ∈ O, average (j.val p) = 0)
    (he : ∀ p ∈ O, average (e.val p) = 0) :
    ∃ U : Family O E, (∀ p ∈ O, average (U.val p) = 0) ∧
      g.transverse.inner U.angle = h ∧
      g.transverse.inner (U.slow v) = j ∧
      (g.longitudinal.inner U.angle).fluct = e ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, h.val p = 0) →
        (∀ p ∈ Z, j.val p = 0) → (∀ p ∈ Z, e.val p = 0) → ∀ p ∈ Z, U.val p = 0) ∧
      (∀ p ∈ O, ∀ t : ℝ, U.val p (t : Period) =
        PeriodicCorrector.fullSolutionFormula v g.Y g.C g.X₀ g.V.val g.q h.val j.val e.val (p, t)) := by
  obtain ⟨U, D, hUs, _, hU0, hUd, hYd, hYs, hX, hzero, hformula⟩ :=
    PeriodicCorrector.solve_full_smooth_family_on_formula O O.isOpen v g.plane g.Y g.C g.X₀
      g.smoothY g.smoothC g.smoothX₀ g.derivativeY g.gram_ne
      g.perpY g.perpC g.perpX₀ g.V.val g.V_mem g.V.smooth
      g.q g.smoothq g.q_pos g.circle h.val j.val e.val h.smooth j.smooth e.smooth hh hj he
  let U' : Family O E := Family.ofLocal U hUs
  have hval (p : A) (hp : p ∈ O) : U'.val p = U p := by
    ext t
    exact Family.ofLocal_apply U hUs hp t
  have hangle (p : A) (hp : p ∈ O) (t : Period) : U'.angle.val p t = D p t := by
    refine Quotient.inductionOn' t ?_
    intro x
    have hd := U'.angle_hasDerivAt hp x
    simp only [hval p hp] at hd
    exact hd.unique (hUd p hp x)
  refine ⟨U', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hval p hp]
    exact hU0 p hp
  · ext p hp t
    simp only [Family.inner_apply, transverse, Family.constant_apply _ _ hp, hangle p hp]
    exact hYd p hp t
  · ext p hp t
    refine Quotient.inductionOn' t ?_
    intro x
    simp only [Family.inner_apply, transverse, Family.constant_apply _ _ hp, Family.slow_apply _ _ hp]
    rw [← fderiv_slice O.isOpen U'.smooth hp]
    have hv : (fun q => U'.val q (x : Period)) =ᶠ[𝓝 p] fun q => U q (x : Period) := by
      filter_upwards [O.isOpen.mem_nhds hp] with q hq
      rw [hval q hq]
    rw [hv.fderiv_eq, fderiv_slice O.isOpen hUs hp]
    exact hYs p hp x
  · ext p hp t
    have hinner : (g.longitudinal.inner U'.angle).val p =
        ⟨fun t => inner ℝ (g.X₀ p + g.V.val p t) (D p t),
          (continuous_const.add (g.V.val p).continuous).inner (D p).continuous⟩ := by
      ext s
      simp only [Family.inner_apply, longitudinal, Family.add_apply, Family.constant_apply _ _ hp, hangle p hp]
      rfl
    simp only [Family.fluct_apply, fluctuation, hinner]
    exact congrFun (hX p hp) t
  · intro Z hZ hZO hhZ hjZ heZ p hp
    rw [hval p (hZO hp)]
    exact hzero Z hZ hZO hhZ hjZ heZ p hp

  · intro p hp t
    rw [hval p hp]
    exact hformula p hp t

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
