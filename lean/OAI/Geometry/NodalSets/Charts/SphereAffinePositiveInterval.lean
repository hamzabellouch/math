import OAI.Geometry.NodalSets.Charts.SphereAffineDivergenceJets

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_positive_interval
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ) :
    ∃ delta > 0,
      (∀ t ∈ Icc (-delta) delta,
        IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) ∧
        (∀ x v w, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v w =
          (A x+roundTensorPerturbation (fun y ↦ t*a y) x) w v) ∧
        (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v v) ∧
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+t*b x) ∧
        (∀ x, 0 < rho x+t*b x)) ∧
      Continuous (fun z : Icc (-delta) delta × Base ↦ rho z.2+(z.1:ℝ)*b z.2) ∧
      (∀ p i j ds, Continuous (fun z : Icc (-delta) delta × Yau.Jets.Coord ↦
        partialJet (fun x ↦ intrinsicDivergencePrincipal
          (fun y ↦ A y+roundTensorPerturbation (fun q ↦ (z.1:ℝ)*a q) y) p x i j) ds z.2)) ∧
      (∀ p ds, Continuous (fun z : Icc (-delta) delta × Yau.Jets.Coord ↦
        partialJet (intrinsicDivergencePotential
          (fun y ↦ rho y+(z.1:ℝ)*b y) lam p) ds z.2)) := by
  obtain ⟨d,hd,hsmall⟩ := small_round_perturbation_in_finite_atlas
    A hA hs hp rho hr hrp a b ha hb ∅ 0 (by norm_num : (0:ℝ)<1)
  refine ⟨d/2,by positivity,?_,?_,?_,?_⟩
  · intro t ht
    have ht' : |t| < d := (abs_le.mpr ht).trans_lt (by linarith)
    obtain ⟨h1,h2,h3,h4,h5,_⟩ := hsmall t ht'
    exact ⟨h1,h2,h3,h4,h5⟩
  · exact (hr.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).mul (hb.continuous.comp continuous_snd))
  · exact fun p i j ds ↦ sphere_affine_principal_joint_jets
      Subtype.val continuous_subtype_val A hA hs hp a ha p i j ds
  · exact fun p ds ↦ sphere_affine_potential_joint_jets
      Subtype.val continuous_subtype_val rho b hr hb lam p ds

end
end Yau.Target

end OAI
