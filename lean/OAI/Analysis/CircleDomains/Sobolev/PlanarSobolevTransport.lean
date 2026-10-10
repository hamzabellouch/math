import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import OAI.Analysis.CircleDomains.Sobolev.RectangleSobolev
import OAI.Analysis.KLS.Sobolev.Witnesses

namespace OAI

/-! Transport the actual planar weak derivative identities to the
Euclidean coordinates of the repository's Sobolev approximation library. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem weakPartial_of_planar_identity
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (i : Fin 2) (v : ℝ × ℝ)
    (hv : euclideanPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ ψ p) v) =
        -(∫p in Icc a b ×ˢ Icc c d, G p * ψ p)) :
    DeGiorgi.HasWeakPartialDeriv i (G ∘ euclideanPlaneCoordinates)
      (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)) := by
  intro φ hφ hs hsub
  let e := euclideanPlaneCoordinates
  change (∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d),
    f (e x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      -(∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), G (e x) * φ x)
  change e (EuclideanSpace.single i 1) = v at hv
  let ψ : ℝ × ℝ → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp e.symm.contDiff
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph e.symm.toHomeomorph
  have hsubψ : tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d := by
    change tsupport (φ ∘ e.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro p hp
    have hh := hsub hp
    change e (e.symm p) ∈ Ioo a b ×ˢ Ioo c d at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ ψ p) v = (fderiv ℝ φ (e.symm p)) (EuclideanSpace.single i 1) := by
    rw [fderiv_comp p (hφ.differentiable (by simp)).differentiableAt e.symm.differentiableAt,
      e.symm.fderiv]
    change (fderiv ℝ φ (e.symm p)) (e.symm v) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hp := hweak ψ hψ hsψ hsubψ
  rw [← rectangle_restrict_Ioo_eq_Icc] at hp
  have hmp : MeasurePreserving e (volume.restrict (e ⁻¹' (Ioo a b ×ˢ Ioo c d)))
      (volume.restrict (Ioo a b ×ˢ Ioo c d)) :=
    euclideanPlaneCoordinates_measurePreserving.restrict_preimage
      (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  calc
    _ = ∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), f (e x) * (fderiv ℝ ψ (e x)) v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [hd,
        ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫p in Ioo a b ×ˢ Ioo c d, f p * (fderiv ℝ ψ p) v :=
      hmp.integral_comp e.toHomeomorph.measurableEmbedding
        (fun p => f p * (fderiv ℝ ψ p) v)
    _ = -(∫p in Ioo a b ×ˢ Ioo c d, G p * ψ p) := hp
    _ = _ := by
      rw [← hmp.integral_comp e.toHomeomorph.measurableEmbedding (fun p => G p * ψ p)]
      simp only [ψ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem memW1p_of_rectangle_weak_gradient
    {f Gx Gy : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hx : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hy : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p)) :
    DeGiorgi.MemW1p 2 (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)) := by
  have hmp := euclideanPlaneCoordinates_measurePreserving.restrict_preimage (s := Ioo a b ×ˢ Ioo c d)
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hf' : MemLp f 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
    rwa [rectangle_restrict_Ioo_eq_Icc]
  have hx' : MemLp Gx 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
    rwa [rectangle_restrict_Ioo_eq_Icc]
  have hy' : MemLp Gy 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
    rwa [rectangle_restrict_Ioo_eq_Icc]
  refine ⟨hf'.comp_measurePreserving hmp, ?_⟩
  intro i
  fin_cases i
  · refine ⟨Gx ∘ euclideanPlaneCoordinates, hx'.comp_measurePreserving hmp, ?_⟩
    exact weakPartial_of_planar_identity 0 (1, 0) euclideanPlaneCoordinates_single_zero
      (fun φ hφ hs hsub => (hweak φ hφ hs hsub).1)
  · refine ⟨Gy ∘ euclideanPlaneCoordinates, hy'.comp_measurePreserving hmp, ?_⟩
    exact weakPartial_of_planar_identity 1 (0, 1) euclideanPlaneCoordinates_single_one
      (fun φ hφ hs hsub => (hweak φ hφ hs hsub).2)

end CircleDomainRigidity

end

end OAI
