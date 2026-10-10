import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicExpansionStep

namespace OAI

/-! The initial coefficient and its transverse cancellation in the periodic expansion. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace Family

def vectorMean (F : Family A E) : Family A E :=
  constant (fun p => average (F.val p)) (contDiff_average_joint F.smooth)

omit [FiniteDimensional ℝ E] in
@[simp] lemma vectorMean_apply (F : Family A E) (p : A) (t : Period) :
    F.vectorMean.val p t = average (F.val p) := rfl

omit [FiniteDimensional ℝ E] in
lemma centered_mean_zero (F : Family A E) (p : A) :
    average ((F - F.vectorMean).val p) = 0 := by
  change average (fun t => F.val p t - average (F.val p)) = 0
  rw [average_sub (F.val p).continuous continuous_const, average_const, sub_self]

lemma primitive_mem (F : Family A E) (hm : ∀ p, average (F.val p) = 0)
    (S : A → Submodule ℝ E) (hS : ∀ p t, F.val p t ∈ S p) (p : A) (t : Period) :
    (F.primitive hm).val p t ∈ S p := by
  refine Quotient.inductionOn' t ?_
  intro x
  exact PeriodicPrimitive.primitive_mem_submodule (S p)
    ((F.val p).continuous.comp (AddCircle.continuous_mk' 1)) (fun y => hS p (y : Period)) x

end Family

namespace Geometry

variable {v : A} (g : Geometry (E := E) v)

def initial : Family A E :=
  (g.V - g.V.vectorMean).primitive g.V.centered_mean_zero

omit [FiniteDimensional ℝ E] in
lemma initial_mean_zero (p : A) : average (g.initial.val p) = 0 :=
  Family.primitive_mean_zero _ _ p

omit [FiniteDimensional ℝ E] in
lemma initial_angle : g.initial.angle = g.V - g.V.vectorMean :=
  Family.primitive_angle _ _

lemma initial_mem (p : A) (t : Period) : g.initial.val p t ∈ g.plane p := by
  apply Family.primitive_mem
  intro q s
  exact (g.plane q).sub_mem (g.V_mem q s)
    (average_mem_submodule (g.plane q) (g.V.val q).continuous (g.V_mem q))

lemma initial_pairing (p : A) (t : Period) :
    inner ℝ (g.Y p) (g.initial.val p t) = 0 ∧
      inner ℝ (g.C p) (g.initial.val p t) = 0 :=
  ⟨g.perpY p _ (g.initial_mem p t), g.perpC p _ (g.initial_mem p t)⟩

/-- The yy coefficient at order one vanishes before higher correctors are added. -/
lemma initial_transverse_derivative : g.transverse.inner (g.initial.slow v) = 0 := by
  ext p t
  refine Quotient.inductionOn' t ?_
  intro x
  have hUt : ContDiff ℝ ∞ (fun p => g.initial.val p (x : Period)) :=
    g.initial.smooth.comp (contDiff_id.prodMk contDiff_const)
  have hK : inner ℝ (g.C p) (g.initial.val p (x : Period)) =
      fderiv ℝ (fun _ : A => (0 : ℝ)) p v - 0 := by
    simpa using (g.initial_pairing p (x : Period)).2
  have hd := PeriodicCorrector.directional_pairing_constraint
    (g.smoothY.differentiable (by simp) p) (hUt.differentiable (by simp) p)
    (differentiableAt_const (c := (0 : ℝ)))
    (fun q => (g.initial_pairing q (x : Period)).1) (g.derivativeY p) hK
  change inner ℝ (g.Y p)
    (slowDerivative (fun z : A × ℝ => g.initial.val z.1 (z.2 : Period)) v (p, x)) = 0
  rwa [fderiv_slice g.initial.smooth] at hd

end Geometry
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
