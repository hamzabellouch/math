import OAI.Geometry.NodalSets.Charts.SphereAffineFormAnnihilation
import OAI.Geometry.NodalSets.Charts.SphereSimplicitySequenceContradiction
import OAI.Geometry.NodalSets.Spectral.SphereOrthogonalEigenfunction

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_kernel_implies_simplicity
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hune : u ≠ 0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (hkernel : ∀ f : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      (∀ p z, -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) →
      sphereEnergyForm a b lam f f=0 → ∃ c : ℝ, ∀ p, f p=c*u p)
    (dpre : ℝ) (hdpre : 0 < dpre)
    (hpres : ∀ t : ℝ, |t| < dpre → ∀ p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
      (fun x ↦ rho x+t*b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z)) :
    ∃ delta > 0, ∀ t : ℝ, |t| < delta → t ≠ 0 →
      ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p z, -intrinsicWeightedChartOperator
        (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
        (fun x ↦ rho x+t*b x) v p z = lam*v ((extChartAt (𝓡 4) p).symm z)) →
      ∃ c : ℝ, v = c • u := by
  classical
  obtain ⟨ds,hds,hsmall⟩ := small_round_perturbation_in_finite_atlas A hA hs hp rho hr hrp
    a b ha hb ∅ 0 (by norm_num : (0:ℝ)<1)
  by_contra h
  push Not at h
  have hbad (j : ℕ) := h (min (min dpre ds) (1/((j:ℝ)+1)))
    (lt_min (lt_min hdpre hds) (by positivity))
  choose t ht htn v hv hev hvnot using hbad
  have hts (j : ℕ) : |t j| < ds := (ht j).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have htp (j : ℕ) : |t j| < dpre := (ht j).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have htlim : Tendsto t atTop (𝓝 0) := by
    have habs : Tendsto (fun j ↦ |t j|) atTop (𝓝 0) := squeeze_zero
      (fun j ↦ abs_nonneg (t j)) (fun j ↦ ((ht j).trans_le (min_le_right _ _)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)
  have hnorm (j : ℕ) := sphere_normalized_orthogonal_eigenfunction
    (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t j*a y) x)
    (hsmall (t j) (hts j)).1 (hsmall (t j) (hts j)).2.1 (hsmall (t j) (hts j)).2.2.1
    (fun x ↦ rho x+t j*b x) (hsmall (t j) (hts j)).2.2.2.1.continuous
    (hsmall (t j) (hts j)).2.2.2.2.1 u (v j) hu (hv j) hune lam
    (hpres (t j) (htp j)) (hev j) (by rintro ⟨c,hc⟩; exact hvnot j c hc)
  choose w hw _ hew hwn hwo using hnorm
  exact sphere_affine_orthogonal_sequence_contradiction A hA hs hp rho hr hrp a b ha hb lam
    t htlim w hw hew hwn u hu.continuous hwo hQ haQ hbQ hkernel
    (fun j f hf hef ↦ sphere_affine_form_annihilates A hA hs hp rho hr hrp a b hb lam (t j)
      (htn j) (hsmall (t j) (hts j)).1 (hsmall (t j) (hts j)).2.1
      (hsmall (t j) (hts j)).2.2.1 (hsmall (t j) (hts j)).2.2.2.2.1
      (w j) f (hw j) hf (hew j) hef)

end
end Yau.Target

end OAI
