import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCubeRowWeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedSeries

namespace OAI

/-! Exact reindexing of the Eisenstein constant coefficient Dirichlet
series by the two signed cubes of each nonzero ideal. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaConstantTermWeight (s : ℂ) (c : Eisenstein) : ℂ :=
  if (3:Eisenstein)∣c ∧ c≠0 then
    cubicThetaEisensteinGaussCoefficient c 0*(norm c:ℂ)^(-s) else 0

def cubicThetaConstantDirichlet (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, cubicThetaConstantTermWeight s c

lemma cubicThetaConstantTermWeight_support (s : ℂ) :
    Function.support (cubicThetaConstantTermWeight s) ⊆
      {c : Eisenstein | c≠0 ∧ ∃ j : Eisenstein, j^3=c} := by
  intro c hc
  by_cases h : (3:Eisenstein)∣c ∧ c≠0
  · refine ⟨h.2,?_⟩
    by_contra hcb
    exact hc (by simp [cubicThetaConstantTermWeight,h,
      cubicThetaEisenstein_constant_noncube h.1 h.2 hcb])
  · exact False.elim (hc (by simp [cubicThetaConstantTermWeight,h]))

lemma cubicThetaConstantTermWeight_cube (s : ℂ) (ε : Bool) (ν : EisensteinIdealExponent) :
    cubicThetaConstantTermWeight s (cubicThetaSignedCube ε ν)=
      (3/2:ℂ)*cubicThetaPrimeDensity cubicThetaRamifiedPrime ν*
        (idealExponentNorm ν:ℂ)^(-(3*s-3)) := by
  by_cases hν : 0<ν cubicThetaRamifiedPrime
  · have h3 := (cubicThetaSignedCube_ramified ε ν).mpr hν
    rw [cubicThetaConstantTermWeight,ite_eq_left ⟨h3,cubicThetaSignedCube_ne_zero ε ν⟩,
      cubicThetaSignedCube_constant ε ν hν,cubicThetaSignedCube_norm,cubicThetaPrimeDensity,
      ite_eq_left hν,cubicThetaIdealDensity,Complex.ofReal_pow]
    have hN := Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'
    have hp : ((idealExponentNorm ν:ℂ)^3)^(-s)=
        (idealExponentNorm ν:ℂ)^(-3*s) := by
      rw [←Complex.cpow_nat_mul' (n:=3)
        (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν).le]; nlinarith [Real.pi_pos])
        (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν).le]; nlinarith [Real.pi_pos])]
      congr 1
      ring
    rw [hp,show -(3*s-3)=(3:ℂ)+(-3*s) by ring,Complex.cpow_add _ _ hN]
    rw [show (idealExponentNorm ν:ℂ)^(3:ℂ)=(idealExponentNorm ν:ℂ)^3 from
      Complex.cpow_natCast _ 3]
    field_simp
  · have h3 : ¬(3:Eisenstein)∣cubicThetaSignedCube ε ν :=
      fun h => hν ((cubicThetaSignedCube_ramified ε ν).mp h)
    simp [cubicThetaConstantTermWeight,h3,cubicThetaPrimeDensity,hν]

lemma cubicThetaConstantDirichlet_cube_sum (s : ℂ) :
    cubicThetaConstantDirichlet s=∑' x : Bool × EisensteinIdealExponent,
      cubicThetaConstantTermWeight s (cubicThetaSignedCube x.1 x.2) := by
  calc
    cubicThetaConstantDirichlet s=∑' c : CubicThetaNonzeroCube, cubicThetaConstantTermWeight s c.val :=
      (tsum_subtype_eq_of_support_subset (cubicThetaConstantTermWeight_support s)).symm
    _ = ∑' x : Bool × EisensteinIdealExponent,
        cubicThetaConstantTermWeight s (cubicThetaCubeCoordinates x).val :=
      (cubicThetaCubeCoordinates.tsum_eq _).symm
    _ = _ := rfl

lemma cubicTheta_signed_sum (g : EisensteinIdealExponent → ℂ)
    (hg : Summable (fun ν => ‖g ν‖)) :
    (∑' x : Bool × EisensteinIdealExponent, (3/2:ℂ)*g x.2)=3*(∑' ν, g ν) := by
  have hp : Summable (fun x : Bool × EisensteinIdealExponent => (3/2:ℂ)*g x.2) :=
    summable_mul_of_summable_norm (f:=fun _ : Bool => (3/2:ℂ)) (g:=g)
      (hasSum_fintype _).summable hg
  rw [hp.tsum_prod,tsum_fintype,Fintype.sum_bool]
  rw [tsum_mul_left]
  ring

theorem cubicThetaConstantDirichlet_eq_ramified {s : ℂ} (hs : 4/3<s.re) :
    cubicThetaConstantDirichlet s=3*cubicThetaRamifiedDensitySeries (3*s-3) := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  let g (ν : EisensteinIdealExponent) := cubicThetaPrimeDensity cubicThetaRamifiedPrime ν*
    (idealExponentNorm ν:ℂ)^(-(3*s-3))
  have hg : Summable (fun ν => ‖g ν‖) :=
    idealDirichlet_norm_summable _ (cubicThetaPrimeDensity_norm cubicThetaRamifiedPrime) ht
  calc
    cubicThetaConstantDirichlet s=∑' x : Bool × EisensteinIdealExponent,
        cubicThetaConstantTermWeight s (cubicThetaSignedCube x.1 x.2) :=
      cubicThetaConstantDirichlet_cube_sum s
    _ = ∑' x : Bool × EisensteinIdealExponent, (3/2:ℂ)*g x.2 := by
      apply tsum_congr
      intro x
      simpa only [g,mul_assoc] using cubicThetaConstantTermWeight_cube s x.1 x.2
    _ = 3*cubicThetaRamifiedDensitySeries (3*s-3) := cubicTheta_signed_sum g hg

end CubicFirstMoment

end

end OAI
