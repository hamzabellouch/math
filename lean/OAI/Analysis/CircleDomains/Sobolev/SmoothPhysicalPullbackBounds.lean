import OAI.Analysis.CircleDomains.Sobolev.SmoothPhysicalPullback

namespace OAI

/-! Global and localized energy bounds for a compact smooth scalar under
the actual smooth plane homeomorphism. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma physicalSmoothPartial_memLp {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u) (i : Fin 2) :
    MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) 2 volume :=
  ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hs.fderiv_apply ℝ _)

lemma physicalSmoothEnergy_integrable {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u) :
    Integrable (physicalSmoothEnergy u) volume :=
  (physicalSmoothPartial_memLp hu hs 0).integrable_sq.add
    (physicalSmoothPartial_memLp hu hs 1).integrable_sq

lemma physicalSmoothEnergy_nonneg (u : EuclideanPlane → ℝ) (x : EuclideanPlane) :
    0 ≤ physicalSmoothEnergy u x := add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma physicalSmoothPullback_energy_global (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ))
    {u : EuclideanPlane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|) :
    (∫ x, physicalSmoothEnergy (u ∘ physicalHomeomorph F) x) ≤
      K*(∫ x, physicalSmoothEnergy u x) := by
  have hvs := hs.comp_homeomorph (physicalHomeomorph F)
  have he := physicalSmoothPullback_energy F hF hu hK hD hvs.isCompact
  have hz : ∀ x ∉ tsupport (u ∘ physicalHomeomorph F),
      physicalSmoothEnergy (u ∘ physicalHomeomorph F) x=0 := by
    intro x hx
    simp [physicalSmoothEnergy, fderiv_of_notMem_tsupport ℝ hx]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral (physicalSmoothEnergy_integrable hu hs)
      (.of_forall (physicalSmoothEnergy_nonneg u))) hK)

lemma physicalSmoothPullback_energy_subset (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ))
    {u : EuclideanPlane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    {A U : Set EuclideanPlane} (hA : IsCompact A) (hAU : MapsTo (physicalHomeomorph F) A U) :
    (∫ x in A, physicalSmoothEnergy (u ∘ physicalHomeomorph F) x) ≤
      K*(∫ x in U, physicalSmoothEnergy u x) := by
  apply (physicalSmoothPullback_energy F hF hu hK hD hA).trans
  apply mul_le_mul_of_nonneg_left _ hK
  exact setIntegral_mono_set (physicalSmoothEnergy_integrable hu hs).integrableOn
    (.of_forall (physicalSmoothEnergy_nonneg u)) (Eventually.of_forall (image_subset_iff.mpr hAU))

end CircleDomainRigidity

end

end OAI
