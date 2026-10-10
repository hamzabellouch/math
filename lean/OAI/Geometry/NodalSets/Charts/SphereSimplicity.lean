import OAI.Geometry.NodalSets.Charts.SphereAffineSimplicityCriterion
import OAI.Geometry.NodalSets.Charts.SpherePreservingEquation
import OAI.Geometry.NodalSets.Charts.SphereSimplicityKernelForm

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem exists_sphere_simplicity_perturbation
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hune : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z)) (r : ℝ) (hradius : 0 < r) :
    ∃ (Q : Set Yau.Jets.Coord) (a b : Base → ℝ),
      IsCompact Q ∧ Q ⊆ seedCoordPatch r ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
      tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
      IsCompact (seedSphereFromCoord '' Q) ∧ seedSphereFromCoord '' Q ⊆ seedSpherePatch r ∧
      (∀ t x, x ∉ seedSphereFromCoord '' Q →
        A x+roundTensorPerturbation (fun y ↦ t*a y) x = A x ∧ rho x+t*b x = rho x) ∧
      ∀ (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps → ∃ delta > 0,
        ∀ t : ℝ, |t| < delta → t ≠ 0 →
          IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) ∧
          (∀ x alpha beta, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha beta =
            (A x+roundTensorPerturbation (fun y ↦ t*a y) x) beta alpha) ∧
          (∀ x alpha, alpha ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha alpha) ∧
          ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+t*b x) ∧
          (∀ x, 0 < rho x+t*b x) ∧
          sphereCoefficientDistance P J A rho
            (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) < eps ∧
          (∀ p z, -intrinsicWeightedChartOperator
            (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
            (fun x ↦ rho x+t*b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z)) ∧
          ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
            (∀ p z, -intrinsicWeightedChartOperator
              (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
              (fun x ↦ rho x+t*b x) v p z = lam*v ((extChartAt (𝓡 4) p).symm z)) →
            ∃ c : ℝ, v = c • u := by
  classical
  obtain ⟨Q,zeta,a,b,hQ,hQP,_,_,_,_,ha,hb,haQ,hbQ,_,_,hcancel,_,hkernel⟩ :=
    exists_sphere_simplicity_kernel_form A hA hs hp rho hr hrp u hu hune lam hlam heu r hradius
  have hQsource : seedSphereFromCoord '' Q ⊆ (extChartAt (𝓡 4) seedPoint).source := by
    rintro x ⟨y,_,rfl⟩
    exact seedSphereFromCoord_source y
  obtain ⟨dpre,hdpre,hpre⟩ := small_round_perturbation_in_finite_atlas A hA hs hp rho hr hrp
    a b ha hb ∅ 0 (by norm_num : (0:ℝ)<1)
  have hpres (t : ℝ) (ht : |t| < dpre) : ∀ p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
      (fun x ↦ rho x+t*b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z) := by
    obtain ⟨h1,h2,h3,_,h5,_⟩ := hpre t ht
    exact sphere_equation_preserved_by_round_cancellation A hA hs hp rho u
      (fun x ↦ t*a x) (fun x ↦ t*b x) hrp hu lam heu h1 h2 h3 h5
      (tsupport_mul_subset_right.trans (haQ.trans hQsource))
      (tsupport_mul_subset_right.trans (hbQ.trans hQsource))
      (round_preserving_cancellation_smul u a b hu ha lam t hcancel)
  obtain ⟨ds,hds,hsimple⟩ := sphere_affine_kernel_implies_simplicity A hA hs hp rho hr hrp
    a b ha hb lam u hu hune hQ haQ hbQ (fun f hf hef ↦ (hkernel f hf hef).mp) dpre hdpre hpres
  refine ⟨Q,a,b,hQ,hQP,ha,hb,haQ,hbQ,hQ.image seedSphereFromCoord_continuous,?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨seedCoordEquiv y,hQP hy,rfl⟩
  · intro t x hx
    have ha0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (haQ h))
    have hb0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hbQ h))
    simp [roundTensorPerturbation,ha0,hb0]
  · intro P J eps heps
    obtain ⟨dn,hdn,hnorm⟩ := small_round_perturbation_in_finite_atlas A hA hs hp rho hr hrp
      a b ha hb P J heps
    refine ⟨min dn (min dpre ds),lt_min hdn (lt_min hdpre hds),?_⟩
    intro t ht htne
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hnorm t (ht.trans_le (min_le_left _ _))
    refine ⟨h1,h2,h3,h4,h5,h6,hpres t (ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))),?_⟩
    exact hsimple t (ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))) htne

end
end Yau.Target

end OAI
