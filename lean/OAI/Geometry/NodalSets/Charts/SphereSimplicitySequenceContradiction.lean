import OAI.Geometry.NodalSets.Charts.SphereAffineNormalizedLimit
import OAI.Geometry.NodalSets.Charts.SphereEnergyFormLimit
import OAI.Geometry.NodalSets.Charts.SphereWeightedNormalization

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter
open scoped Topology ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_orthogonal_sequence_contradiction
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t j*a y) x)
      (fun x ↦ rho x+t j*b x) (w j) p z = lam*w j ((extChartAt (𝓡 4) p).symm z))
    (hn : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) (w j)=1)
    (u : Base → ℝ) (hu : Continuous u)
    (ho : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) u=0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (hkernel : ∀ f : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      (∀ p z, -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) →
      sphereEnergyForm a b lam f f=0 → ∃ c : ℝ, ∀ p, f p=c*u p)
    (hform : ∀ j (f : Base → ℝ), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      (∀ p z, -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) →
      sphereEnergyForm a b lam (w j) f=0) : False := by
  obtain ⟨v,hv,hvne,hev,hvn,hvo,nu,hnu,_,hpartial,_⟩ :=
    sphere_affine_normalized_limit A hA hs hp rho hr hrp a b ha hb lam t ht w hw he hn u hu ho
  have hlim := sphereEnergyForm_limit a b ha hb hQ haQ hbQ lam (fun j ↦ w (nu j)) v v
    (fun j ↦ hw (nu j)) hv hv (fun ds ↦ hpartial seedPoint ds Q hQ)
  have hzero : sphereEnergyForm a b lam v v=0 := by
    apply tendsto_nhds_unique hlim
    simpa only [hform _ v hv hev] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  obtain ⟨c,hc⟩ := hkernel v hv hev hzero
  have heq : v=c • u := funext hc
  have hnormzero : sphereWeightedPairing rho v v=0 := by
    calc
      _ = sphereWeightedPairing rho v (c • u) := congrArg (sphereWeightedPairing rho v) heq
      _ = c*sphereWeightedPairing rho v u := sphereWeightedPairing_smul_right rho v u c
      _ = 0 := by rw [hvo,mul_zero]
  linarith

end
end Yau.Target

end OAI
