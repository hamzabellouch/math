import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicExpansionStep

namespace OAI

/-! Initial coefficient and transverse cancellation on the admissible domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

def initial : Family O E :=
  (g.V - g.V.vectorMean).primitive (fun p _ => g.V.centered_mean_zero p)

omit [FiniteDimensional ℝ E] in
lemma initial_mean_zero {p : A} (hp : p ∈ O) : average (g.initial.val p) = 0 :=
  Family.primitive_mean_zero _ _ hp

omit [FiniteDimensional ℝ E] in
lemma initial_angle : g.initial.angle = g.V - g.V.vectorMean :=
  Family.primitive_angle _ _

lemma initial_mem {p : A} (hp : p ∈ O) (t : Period) : g.initial.val p t ∈ g.plane p := by
  apply Family.primitive_mem _ _ _ _ hp
  intro q hq s
  simp only [Family.sub_apply, Family.vectorMean_apply]
  exact (g.plane q).sub_mem (g.V_mem q hq s)
    (average_mem_submodule (g.plane q) (g.V.val q).continuous (g.V_mem q hq))

lemma initial_pairing {p : A} (hp : p ∈ O) (t : Period) :
    inner ℝ (g.Y p) (g.initial.val p t) = 0 ∧
      inner ℝ (g.C p) (g.initial.val p t) = 0 :=
  ⟨g.perpY p hp _ (g.initial_mem hp t), g.perpC p hp _ (g.initial_mem hp t)⟩

lemma initial_transverse_derivative : g.transverse.inner (g.initial.slow v) = 0 := by
  ext p hp t
  refine Quotient.inductionOn' t ?_
  intro x
  simp only [Family.inner_apply, transverse, Family.constant_apply _ _ hp,
    Family.slow_apply _ _ hp, Family.zero_apply]
  have hUt : ContDiffAt ℝ ∞ (fun q => g.initial.val q (x : Period)) p :=
    (g.initial.smooth.contDiffAt ((O.isOpen.prod isOpen_univ).mem_nhds
      ⟨hp, Set.mem_univ x⟩)).comp p (contDiff_id.prodMk contDiff_const).contDiffAt
  have hd := PeriodicCorrector.directional_pairing_constraint_on O.isOpen hp
    ((g.smoothY.contDiffAt (O.isOpen.mem_nhds hp)).differentiableAt (by simp))
    (hUt.differentiableAt (by simp)) (differentiableAt_const (c := (0 : ℝ)))
    (fun q hq => (g.initial_pairing hq (x : Period)).1) (g.derivativeY p hp)
    (show inner ℝ (g.C p) (g.initial.val p (x : Period)) =
        fderiv ℝ (fun _ : A => (0 : ℝ)) p v - 0 by
      simpa using (g.initial_pairing hp (x : Period)).2)
  rwa [fderiv_slice O.isOpen g.initial.smooth hp] at hd

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
