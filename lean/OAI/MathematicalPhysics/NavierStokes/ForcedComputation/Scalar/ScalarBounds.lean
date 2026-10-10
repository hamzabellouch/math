import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarComparison

namespace OAI

/-! Constant and affine barriers give the quantitative scalar estimates
used during injection and stirring. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem scalarGenerator_const (ν : ℝ) (a : Plane → Plane) (c : ℝ) (x : Plane) :
    scalarGenerator ν a (fun _ => c) x = 0 := by
  have h := scalarGenerator_sub_const ν a (fun _ => 0) (-c) x
  simpa only [zero_sub, neg_neg, scalarGenerator_zero] using h

theorem affine_solution (T ν M A : ℝ) (a : ℝ → Plane → Plane) :
    TorusScalarSolution T ν a (fun _ _ => A) (fun t _ => M + A * t) (fun _ => M) := by
  refine ⟨(contDiff_const.add (contDiff_const.mul contDiff_fst)).contDiffOn,
    fun _ _ _ _ => rfl, ?_, ?_⟩
  · funext x
    simp
  · intro t _ x
    simpa only [scalarGenerator_const, zero_add, mul_one, id_eq] using
      (((hasDerivWithinAt_id t (Icc (0 : ℝ) T)).const_mul A).const_add M)

theorem TorusScalarSolution.upper_bound {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    {M A : ℝ} (hh : ∀ t ∈ Icc 0 T, ∀ x, h t x ≤ A) (h₀ : ∀ x, w₀ x ≤ M) :
    ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ M + A * t :=
  hw.compare (affine_solution T ν M A a) hT hν hh h₀

theorem TorusScalarSolution.absolute_bound {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    {M A : ℝ} (hh : ∀ t ∈ Icc 0 T, ∀ x, |h t x| ≤ A)
    (h₀ : ∀ x, |w₀ x| ≤ M) :
    ∀ t ∈ Icc 0 T, ∀ x, |w t x| ≤ M + A * t := by
  have hu := hw.upper_bound hT hν
    (fun t ht x => (abs_le.mp (hh t ht x)).2) (fun x => (abs_le.mp (h₀ x)).2)
  have hl := (affine_solution T ν (-M) (-A) a).compare hw hT hν
    (fun t ht x => (abs_le.mp (hh t ht x)).1) (fun x => (abs_le.mp (h₀ x)).1)
  intro t ht x
  apply abs_le.mpr
  constructor
  · have h := hl t ht x
    linarith
  · exact hu t ht x


/-- A residual bound gives a pointwise error bound, including an initial error. -/
theorem TorusScalarSolution.stability {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h k w v : ℝ → Plane → ℝ} {w₀ v₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀)
    (hv : TorusScalarSolution T ν a k v v₀) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    {E D : ℝ} (hres : ∀ t ∈ Icc 0 T, ∀ x, |h t x - k t x| ≤ D)
    (hinit : ∀ x, |w₀ x - v₀ x| ≤ E) :
    ∀ t ∈ Icc 0 T, ∀ x, |w t x - v t x| ≤ E + D * t :=
  (hw.sub hv).absolute_bound hT hν hres hinit

end ForcedComputation.VelocityDetector

end

end OAI
