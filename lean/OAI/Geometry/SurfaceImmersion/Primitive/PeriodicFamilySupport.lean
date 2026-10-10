import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFamilies

namespace OAI

/-! Local vanishing of smooth periodic coefficient families. -/

noncomputable section

namespace ClosedSurfaceR4.PeriodicExpansion.Family

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma angle_zero_at (F : Family A E) {p : A} (hp : F.val p = 0) : F.angle.val p = 0 :=
  derivativeFamily_zero_at F.val F.smooth hp

lemma slow_zero_on (F : Family A E) {O : Set A} (hO : IsOpen O)
    (hz : ∀ p ∈ O, F.val p = 0) (v : A) {p : A} (hp : p ∈ O) :
    (F.slow v).val p = 0 := slowDerivativeFamily_zero_on F.val F.smooth hO hz v hp

variable [FiniteDimensional ℝ A]

lemma fluct_zero_at (F : Family A ℝ) {p : A} (hp : F.val p = 0) : F.fluct.val p = 0 := by
  ext t
  change F.val p t - average (F.val p) = 0
  rw [hp]
  change (0 : ℝ) - average (fun _ => (0 : ℝ)) = 0
  rw [average_const, sub_self]

end ClosedSurfaceR4.PeriodicExpansion.Family

end

end OAI
