import OAI.Analysis.CircleDomains.Topology.PlanarAffineRescale
import OAI.Analysis.KLS.Sobolev.WeakDerivatives

namespace OAI

/-! The actual distributional gradient under a positive affine rescaling.
The proof changes variables in the compactly supported test identity. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma weakGradient_planarAffine {u : EuclideanPlane → ℝ} {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ) (a : EuclideanPlane) {s : ℝ} (hs : 0 < s) :
    DeGiorgi.HasWeakGrad (fun x => s • V (a+s • x)) (fun x => u (a+s • x)) univ := by
  intro i φ hφ hsφ _
  let e := planarAffineHomeomorph a s hs.ne'
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp ((contDiff_id.sub contDiff_const).const_smul s⁻¹)
  have hsψ : HasCompactSupport ψ := hsφ.comp_homeomorph e.symm
  have heq (x : EuclideanPlane) : ψ (a+s • x) = φ x := e.symm_apply_apply x |> congrArg φ
  have hd (x : EuclideanPlane) :
      fderiv ℝ ψ (a+s • x) (EuclideanSpace.single i 1) =
        s⁻¹ * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    have hh := (hφ.differentiable (by simp) (e.symm (a+s • x))).hasFDerivAt.comp (a+s • x)
      (planarAffine_inverse_hasFDerivAt a hs.ne' (a+s • x))
    have h := congrArg (fun L : EuclideanPlane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hh.fderiv
    simpa only [ψ, ← planarAffineHomeomorph_apply a s hs.ne', e, Homeomorph.symm_apply_apply,
      ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul] using h
  have hbase := hw i ψ hψ hsψ (subset_univ _)
  simp only [Measure.restrict_univ] at hbase ⊢
  let A : EuclideanPlane → ℝ := fun y => u y * fderiv ℝ ψ y (EuclideanSpace.single i 1)
  let B : EuclideanPlane → ℝ := fun y => V y i * ψ y
  have ht : (∫ x, A (a+s • x)) = -(∫ x, B (a+s • x)) := by
    rw [integral_planarAffine a hs, integral_planarAffine a hs]
    change (s^2)⁻¹*(∫ y, u y*fderiv ℝ ψ y (EuclideanSpace.single i 1)) = _
    rw [hbase, mul_neg]
  have hA : (fun x => A (a+s • x)) = fun x => s⁻¹*(u (a+s • x)*fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    dsimp only [A]
    rw [hd]
    ring
  have hB : (fun x => B (a+s • x)) = fun x => V (a+s • x) i * φ x := by
    funext x
    dsimp only [B]
    rw [heq]
  rw [hA, hB, integral_const_mul] at ht
  have hh := congrArg (fun t : ℝ => s*t) ht
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_neg] at hh
  have hR : (fun x => (s • V (a+s • x)) i * φ x) = fun x => s*(V (a+s • x) i * φ x) := by
    funext x
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hR, integral_const_mul]
  exact hh

end CircleDomainRigidity

end

end OAI
