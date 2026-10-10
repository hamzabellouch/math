import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFamilyAlgebra

namespace OAI

/-! The finite periodic cancellation step on an open admissible domain. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

structure Geometry (O : TopologicalSpace.Opens A) (v : A) where
  plane : A → Submodule ℝ E
  Y : A → E
  C : A → E
  X₀ : A → E
  smoothY : ContDiffOn ℝ ∞ Y O
  smoothC : ContDiffOn ℝ ∞ C O
  smoothX₀ : ContDiffOn ℝ ∞ X₀ O
  derivativeY : ∀ p ∈ O, fderiv ℝ Y p v = C p
  gram_ne : ∀ p ∈ O, PeriodicCorrector.gramDet (Y p) (C p) ≠ 0
  perpY : ∀ p ∈ O, ∀ w, w ∈ plane p → inner ℝ (Y p) w = 0
  perpC : ∀ p ∈ O, ∀ w, w ∈ plane p → inner ℝ (C p) w = 0
  perpX₀ : ∀ p ∈ O, ∀ w, w ∈ plane p → inner ℝ (X₀ p) w = 0
  V : Family O E
  V_mem : ∀ p ∈ O, ∀ t, V.val p t ∈ plane p
  q : A → ℝ
  smoothq : ContDiffOn ℝ ∞ q O
  q_pos : ∀ p ∈ O, 0 < q p
  circle : ∀ p ∈ O, ∀ t, inner ℝ (V.val p t) (V.val p t) = q p

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

def longitudinal : Family O E := Family.constant g.X₀ g.smoothX₀ + g.V

def transverse : Family O E := Family.constant g.Y g.smoothY

theorem exists_system (h j e : Family O ℝ)
    (hh : ∀ p ∈ O, average (h.val p) = 0) (hj : ∀ p ∈ O, average (j.val p) = 0)
    (he : ∀ p ∈ O, average (e.val p) = 0) :
    ∃ U : Family O E, (∀ p ∈ O, average (U.val p) = 0) ∧
      g.transverse.inner U.angle = h ∧
      g.transverse.inner (U.slow v) = j ∧
      (g.longitudinal.inner U.angle).fluct = e ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, h.val p = 0) →
        (∀ p ∈ Z, j.val p = 0) → (∀ p ∈ Z, e.val p = 0) → ∀ p ∈ Z, U.val p = 0) := by
  obtain ⟨U, D, hUs, _, hU0, hUd, hYd, hYs, hX, hzero⟩ :=
    PeriodicCorrector.solve_full_smooth_family_on O O.isOpen v g.plane g.Y g.C g.X₀
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
  refine ⟨U', ?_, ?_, ?_, ?_, ?_⟩
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

/-- One coefficient cancels the next three fluctuation equations. -/
theorem exists_cancellation (b c d : Family O ℝ) :
    ∃ U : Family O E, (∀ p ∈ O, average (U.val p) = 0) ∧
      (g.transverse.inner U.angle + b).fluct = 0 ∧
      (g.longitudinal.inner U.angle + c).fluct = 0 ∧
      ((2 : ℝ) • g.transverse.inner (U.slow v) + d).fluct = 0 ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, b.val p = 0) →
        (∀ p ∈ Z, c.val p = 0) → (∀ p ∈ Z, d.val p = 0) → ∀ p ∈ Z, U.val p = 0) := by
  have hs (a : ℝ) (f : Family O ℝ) (p : A) (_ : p ∈ O) :
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
  · intro Z hZ hZO hb hc hd
    have hz (a : ℝ) (f : Family O ℝ) (hf : ∀ p ∈ Z, f.val p = 0) :
        ∀ p ∈ Z, (a • f.fluct).val p = 0 := by
      intro p hp
      change a • f.fluct.val p = 0
      rw [f.fluct_zero_at (hf p hp), smul_zero]
    exact hzero Z hZ hZO (hz _ _ hb) (hz _ _ hd) (hz _ _ hc)

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
