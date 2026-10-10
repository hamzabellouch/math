import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCutoffSquare

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set Metric
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def principal (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ) (x : P × V) (i j : Fin 4) : ℝ :=
  cutoffPrincipal (fun i j z => a i j (x.1,z)) χ i j x.2

def first (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (χ : V → ℝ) (x : P × V) (j : Fin 4) : W →L[ℝ] W :=
  cutoffFirst (EuclideanSpace.basisFun (Fin 4) ℝ) (fun i j z => a i j (x.1,z))
    (fun j z => b j (x.1,z)) χ j x.2

def zero (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) (x : P × V) : W →L[ℝ] W :=
  cutoffZero (EuclideanSpace.basisFun (Fin 4) ℝ) (fun i j z => a i j (x.1,z))
    (fun j z => b j (x.1,z)) (fun z => c (x.1,z)) χ x.2

lemma principal_smooth (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V} (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) :
    ContDiffAt ℝ ∞ (principal a χ) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact contDiffAt_const.add ((hχ.contDiffAt.comp x contDiffAt_snd).mul ((ha i j).sub contDiffAt_const))

lemma first_smooth (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x) :
    ContDiffAt ℝ ∞ (first a b χ) x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  apply contDiffAt_pi.mpr
  intro j
  exact ((hχ.contDiffAt.comp x contDiffAt_snd).smul (hb j)).sub
    ((ContDiffAt.sum (fun i _ => ((ha i j).add (ha j i)).mul
      ((hd.contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const))).smul contDiffAt_const)

lemma zero_smooth (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ContDiffAt ℝ ∞ c x) : ContDiffAt ℝ ∞ (zero a b c χ) x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  have hdd (j : Fin 4) : ContDiff ℝ ∞ (fderiv ℝ (fun y => fderiv ℝ χ y
      (EuclideanSpace.basisFun (Fin 4) ℝ j))) :=
    (hd.clm_apply contDiff_const).fderiv_right (by simp)
  exact (((hχ.contDiffAt.comp x contDiffAt_snd).smul hc).sub
    ((ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => (ha i j).mul
      (((hdd j).contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const)))).smul contDiffAt_const)).add
    (ContDiffAt.sum (fun i _ => (((hd.contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const).smul (hb i))))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma principal_center (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ)
    (hχ : χ =ᶠ[𝓝 (0 : V)] 1) (q : P) : principal a χ (q,0) = fun i j => a i j (q,0) := by
  funext i j
  simp [principal,cutoffPrincipal,hχ.eq_of_nhds]

lemma principal_dpos_zero (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) (q : P)
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) (q,0))
    (hder : ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0) :
    dpos (principal a χ) (q,0) = 0 := by
  have he : (fun z => principal a χ (q,z)) =ᶠ[𝓝 (0 : V)] (fun z i j => a i j (q,z)) := by
    filter_upwards [hχ0] with z hz
    funext i j
    simp [principal,cutoffPrincipal,hz]
  rw [dpos_eq_at _ _ _ ((principal_smooth a χ hχ ha).differentiableAt (by simp)),he.fderiv_eq]
  have hd (i j : Fin 4) : DifferentiableAt ℝ (fun z => a i j (q,z)) 0 :=
    ((ha i j).comp 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  rw [fderiv_pi (fun i => differentiableAt_pi.mpr (hd i))]
  ext v i j
  simp only [ContinuousLinearMap.pi_apply,zero_apply,Pi.zero_apply]
  rw [fderiv_pi (hd i)]
  simp only [ContinuousLinearMap.pi_apply,hder,zero_apply]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma first_center (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : χ =ᶠ[𝓝 (0 : V)] 1) (q : P) : first a b χ (q,0) = fun j => b j (q,0) := by
  have hd : fderiv ℝ χ 0 = 0 := by simpa using hχ.fderiv_eq (𝕜 := ℝ)
  funext j
  simp [first,cutoffFirst,hχ.eq_of_nhds,hd]

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

end

end OAI
