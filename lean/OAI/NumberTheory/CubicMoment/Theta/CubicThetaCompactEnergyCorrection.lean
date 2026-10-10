import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExteriorEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalGreen

namespace OAI

/-! Compact corrections of the actual energy inclusion. The exterior
inequality gives a numerical-range bound with arbitrary coefficient
strictly larger than one half. -/
noncomputable section
open scoped MatrixGroups InnerProduct
namespace CubicFirstMoment

def cubicThetaEnergyMass : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaGlobalInclusion.adjoint.comp cubicThetaGlobalInclusion

def cubicThetaCompactEnergyCorrection (S R : Finset SL(2,Eisenstein)) (B : ℝ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  (cubicThetaCoreRestriction S 2).adjoint.comp (cubicThetaCoreRestriction S 2)+
    (B:ℂ) • ((cubicThetaCoreRestriction R 2).adjoint.comp (cubicThetaCoreRestriction R 2))

lemma cubicThetaCompactEnergyCorrection_compact (S R : Finset SL(2,Eisenstein)) (B : ℝ) :
    IsCompactOperator (cubicThetaCompactEnergyCorrection S R B) := by
  have hS : IsCompactOperator ((cubicThetaCoreRestriction S 2).adjoint.comp
      (cubicThetaCoreRestriction S 2)) :=
    (cubicThetaCoreRestriction_compact S 2).clm_comp (cubicThetaCoreRestriction S 2).adjoint
  have hR : IsCompactOperator ((cubicThetaCoreRestriction R 2).adjoint.comp
      (cubicThetaCoreRestriction R 2)) :=
    (cubicThetaCoreRestriction_compact R 2).clm_comp (cubicThetaCoreRestriction R 2).adjoint
  exact hS.add (hR.smul (B:ℂ))

lemma cubicThetaEnergyMass_inner (u : cubicThetaGlobalEnergySpace) :
    (inner ℂ (cubicThetaEnergyMass u) u).re=‖cubicThetaGlobalInclusion u‖^2 := by
  rw [cubicThetaEnergyMass,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

lemma cubicThetaCompactEnergyCorrection_inner (S R : Finset SL(2,Eisenstein)) (B : ℝ)
    (u : cubicThetaGlobalEnergySpace) :
    (inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re=
      ‖cubicThetaCoreRestriction S 2 u‖^2+B*‖cubicThetaCoreRestriction R 2 u‖^2 := by
  let P := cubicThetaCoreRestriction S 2
  let Q := cubicThetaCoreRestriction R 2
  have hs : inner ℂ ((B:ℂ) • (Q.adjoint (Q u))) u=
      star (B:ℂ)*inner ℂ (Q.adjoint (Q u)) u :=
    inner_smul_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) (Q.adjoint (Q u)) u (B:ℂ)
  change (inner ℂ (P.adjoint (P u)+(B:ℂ) • (Q.adjoint (Q u))) u).re=_
  have hP := P.adjoint_inner_left u (P u)
  have hQ := Q.adjoint_inner_left u (Q u)
  have ha := inner_add_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)
    (P.adjoint (P u)) ((B:ℂ) • (Q.adjoint (Q u))) u
  have hb : inner ℂ ((B:ℂ) • (Q.adjoint (Q u))) u=(B:ℂ)*inner ℂ (Q u) (Q u) := by
    calc
      _ = star (B:ℂ)*inner ℂ (Q.adjoint (Q u)) u := hs
      _ = _ := by rw [hQ,RCLike.star_def,Complex.conj_ofReal]
  have hh := congrArg Complex.re (ha.trans (congrArg₂ (fun x y : ℂ => x+y) hP hb))
  have hPn : (inner ℂ (P u) (P u)).re=‖P u‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (P u)
  have hQn : (inner ℂ (Q u) (Q u)).re=‖Q u‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (Q u)
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hPn,hQn] at hh
  exact hh

lemma cubicThetaEnergyMass_upper_mod_compact {ε : ℝ} (hε : 0<ε) :
    ∃ (S R : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ u : cubicThetaGlobalEnergySpace,
    (2+ε)*(inner ℂ (cubicThetaEnergyMass u) u).re≤
      (1+ε)*‖u‖^2+(inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re := by
  obtain ⟨S,R,B,hB,h⟩ := cubicThetaExterior_energy hε
  refine ⟨S,R,B,hB,fun u => ?_⟩
  rw [cubicThetaEnergyMass_inner,cubicThetaCompactEnergyCorrection_inner,
    cubicThetaGlobalEnergy_norm_sq]
  nlinarith [h u]

end CubicFirstMoment

end

end OAI
