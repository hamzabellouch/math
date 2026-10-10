import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSphereHarmonicSpan

namespace OAI

/-! # Constant and coordinate moments determine degrees zero and one -/

open MvPolynomial

namespace DefocusingNLS

theorem physicalPolynomial_zero_degree_map (L : PhysicalRealPolynomial →ₗ[ℝ] ℂ)
    (hL : L 1 = 0) (p : PhysicalRealPolynomial) (hp : p.IsHomogeneous 0) : L p = 0 := by
  have he : p = C (p.coeff 0) := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 12)).mpr hp)
  rw [he, C_eq_smul_one, map_smul, hL, smul_zero]

theorem physicalPolynomial_one_degree_map (L : PhysicalRealPolynomial →ₗ[ℝ] ℂ)
    (hL : ∀ j : Fin 12, L (X j) = 0) (p : PhysicalRealPolynomial)
    (hp : p.IsHomogeneous 1) : L p = 0 := by
  have hs : homogeneousSubmodule (Fin 12) ℝ 1 ≤ L.ker := by
    rw [homogeneousSubmodule_one_eq_span_X]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hL j
  exact hs hp

theorem physicalSphereMoment_zero_degree (f : C(PhysicalUnitSphere, ℂ))
    (h : physicalSphereMoment f (physicalSpherePolynomial 1) = 0)
    (p : PhysicalRealPolynomial) (hp : p.IsHomogeneous 0) :
    physicalSphereMoment f (physicalSpherePolynomial p) = 0 :=
  physicalPolynomial_zero_degree_map
    ((physicalSphereMoment f).comp physicalSpherePolynomial.toLinearMap) h p hp

theorem physicalSphereMoment_one_degree (f : C(PhysicalUnitSphere, ℂ))
    (h : ∀ j : Fin 12, physicalSphereMoment f (physicalSpherePolynomial (X j)) = 0)
    (p : PhysicalRealPolynomial) (hp : p.IsHomogeneous 1) :
    physicalSphereMoment f (physicalSpherePolynomial p) = 0 :=
  physicalPolynomial_one_degree_map
    ((physicalSphereMoment f).comp physicalSpherePolynomial.toLinearMap) h p hp

end DefocusingNLS

end OAI
