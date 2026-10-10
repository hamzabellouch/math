import OAI.Geometry.NodalSets.Coefficients.IntrinsicDivergenceCoefficients
import OAI.Geometry.NodalSets.Elliptic.RealAffinePartialJets
import OAI.Geometry.NodalSets.Elliptic.SmallRoundPerturbation

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsicDivergencePrincipal_affine (A : IntrinsicTensor) (a : Base → ℝ)
    (t : ℝ) (p : Base) (x : Yau.Jets.Coord) (i j : Fin 4) :
    intrinsicDivergencePrincipal
      (fun y ↦ A y+roundTensorPerturbation (fun z ↦ t*a z) y) p x i j =
      intrinsicDivergencePrincipal A p x i j+
        t*intrinsicDivergencePrincipal (roundTensorPerturbation a) p x i j := by
  simp only [intrinsicDivergencePrincipal,intrinsicRealPrincipal,intrinsicSphereChartTensor_add,
    roundTensorPerturbation_chart,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma intrinsicDivergencePotential_affine (rho b : Base → ℝ) (lam t : ℝ)
    (p : Base) (x : Yau.Jets.Coord) :
    intrinsicDivergencePotential (fun y ↦ rho y+t*b y) lam p x =
      intrinsicDivergencePotential rho lam p x+t*intrinsicDivergencePotential b lam p x := by
  simp only [intrinsicDivergencePotential,intrinsicRealPotential]
  ring

lemma intrinsicDivergencePrincipal_round_smooth (a : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicDivergencePrincipal (roundTensorPerturbation a) p x i j) :=
  roundCoordDensity_smooth.mul (round_increment_any_entry_smooth a ha p i j)

theorem sphere_affine_principal_joint_jets {T : Type*} [TopologicalSpace T]
    (s : T → ℝ) (hs : Continuous s) (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hAs : ∀ x v w, A x v w = A x w v) (hAp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (a : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (p : Base) (i j : Fin 4) (ds : List (Fin 4)) :
    Continuous (fun z : T × Yau.Jets.Coord ↦ partialJet
      (fun x ↦ intrinsicDivergencePrincipal
        (fun y ↦ A y+roundTensorPerturbation (fun q ↦ s z.1*a q) y) p x i j) ds z.2) := by
  simp_rw [intrinsicDivergencePrincipal_affine]
  exact affine_partialJet_joint_continuous s hs _ _
    (intrinsicDivergencePrincipal_smooth A hA hAs hAp p i j)
    (intrinsicDivergencePrincipal_round_smooth a ha p i j) ds

theorem sphere_affine_potential_joint_jets {T : Type*} [TopologicalSpace T]
    (s : T → ℝ) (hs : Continuous s) (rho b : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    (lam : ℝ) (p : Base) (ds : List (Fin 4)) :
    Continuous (fun z : T × Yau.Jets.Coord ↦ partialJet
      (intrinsicDivergencePotential (fun y ↦ rho y+s z.1*b y) lam p) ds z.2) := by
  simp_rw [show ∀ t : ℝ, intrinsicDivergencePotential (fun y ↦ rho y+t*b y) lam p =
    fun x ↦ intrinsicDivergencePotential rho lam p x+t*intrinsicDivergencePotential b lam p x
    from fun t ↦ funext (intrinsicDivergencePotential_affine rho b lam t p)]
  exact affine_partialJet_joint_continuous s hs _ _
    (intrinsicDivergencePotential_smooth rho hr lam p)
    (intrinsicDivergencePotential_smooth b hb lam p) ds

end
end Yau.Target

end OAI
