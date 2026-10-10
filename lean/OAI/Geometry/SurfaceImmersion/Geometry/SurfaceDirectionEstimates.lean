import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapLinearStability

namespace OAI

/-! Second-jet control of the actual surface controls the first derivative
of its direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceDirectionLinearization_sub_apply (f g : Base → ProjectionTarget 3)
    (b : Bool) (z w : Base × ℝ) :
    (surfaceDirectionLinearization g b z-surfaceDirectionLinearization f b z) w =
      w.2 • ((fderiv ℝ g z.1-fderiv ℝ f z.1) (tangentRayVelocity b)) +
      (fderiv ℝ (fderiv ℝ g) z.1-fderiv ℝ (fderiv ℝ f) z.1) w.1 (tangentRay b z.2) := by
  change (fderiv ℝ g z.1 (w.2 • tangentRayVelocity b) +
    fderiv ℝ (fderiv ℝ g) z.1 w.1 (tangentRay b z.2)) -
      (fderiv ℝ f z.1 (w.2 • tangentRayVelocity b) +
        fderiv ℝ (fderiv ℝ f) z.1 w.1 (tangentRay b z.2)) = _
  simp only [sub_apply,smul_sub,map_smul]
  abel

lemma norm_surfaceJet_operator
    (A : Base →L[ℝ] ProjectionTarget 3)
    (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) (u v : Base)
    (L : Base × ℝ →L[ℝ] ProjectionTarget 3)
    (hL : ∀ w : Base × ℝ, L w = w.2 • A v+B w.1 u) :
    ‖L‖ ≤ ‖A‖*‖v‖+‖B‖*‖u‖ := by
  apply L.opNorm_le_bound (by positivity)
  intro w
  rw [hL]
  have hb : ‖B w.1 u‖ ≤ ‖B‖*‖w.1‖*‖u‖ := by
    calc
      _ ≤ ‖B w.1‖*‖u‖ := (B w.1).le_opNorm _
      _ ≤ (‖B‖*‖w.1‖)*‖u‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
  calc
    _ ≤ ‖w.2 • A v‖+‖B w.1 u‖ := norm_add_le _ _
    _ ≤ ‖w.2‖*(‖A‖*‖v‖)+‖B‖*‖w.1‖*‖u‖ := by
      rw [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)) hb
    _ ≤ ‖w‖*(‖A‖*‖v‖)+‖B‖*‖w‖*‖u‖ := by
      gcongr
      · exact norm_snd_le w
      · exact norm_fst_le w
    _ = _ := by ring

lemma norm_surfaceDirection_fderiv_sub {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (b : Bool) (z : Base × ℝ) :
    ‖fderiv ℝ (surfaceDirection g b) z-fderiv ℝ (surfaceDirection f b) z‖ ≤
      ‖fderiv ℝ g z.1-fderiv ℝ f z.1‖*‖tangentRayVelocity b‖ +
      ‖fderiv ℝ (fderiv ℝ g) z.1-fderiv ℝ (fderiv ℝ f) z.1‖*‖tangentRay b z.2‖ := by
  have hdg := (surfaceDirection_hasFDerivAt hg b z).fderiv
  have hdf := (surfaceDirection_hasFDerivAt hf b z).fderiv
  rw [hdg,hdf]
  exact norm_surfaceJet_operator _ _ _ _ _
    (surfaceDirectionLinearization_sub_apply f g b z)

lemma tangentRay_norm_le (b : Bool) (t : ℝ) : ‖tangentRay b t‖ ≤ |t|+1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  cases b <;> fin_cases i <;> simp [tangentRay]

lemma tangentRayVelocity_norm (b : Bool) : ‖tangentRayVelocity b‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    cases b <;> fin_cases i <;> simp [tangentRayVelocity]
  · cases b
    · simpa [tangentRayVelocity] using
        (norm_le_pi_norm (tangentRayVelocity false) (1 : Fin 2))
    · simpa [tangentRayVelocity] using
        (norm_le_pi_norm (tangentRayVelocity true) (0 : Fin 2))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
