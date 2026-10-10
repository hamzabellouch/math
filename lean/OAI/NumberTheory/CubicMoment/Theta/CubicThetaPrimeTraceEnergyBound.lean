import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceRegularity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergySum

namespace OAI

/-! The actual differential of the finite trace has the degree bound
obtained from the sheet isometries and finite Cauchy--Schwarz. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

local instance primeTraceEnergy_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

def cubicThetaPrimeTraceCoordinateTerm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (t : cubicThetaPrimeTransversal hp) (y : ℂ × ℝ) : ℂ :=
  star (cubicThetaKubotaValue t.val)*
    cubicThetaPrimeSectionFunction hp F.val (cubicThetaMobius (cubicThetaPrincipalComplex t.val) y)

lemma cubicThetaPrimeTraceCoordinateTerm_differentiable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (t : cubicThetaPrimeTransversal hp)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    DifferentiableAt ℝ (cubicThetaPrimeTraceCoordinateTerm hp F t) y := by
  have hf := (F.property.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds
    (cubicThetaMobius_height_pos (cubicThetaPrincipalComplex t.val) hy))).differentiableAt
      (by norm_num)
  exact (hf.comp y ((cubicThetaMobius_contDiffAt _ hy).differentiableAt (by simp))).const_mul _

lemma cubicThetaPrimeTraceCoordinateTerm_energy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (t : cubicThetaPrimeTransversal hp) (x : CubicThetaPoint) :
    x.val.2^2*cubicThetaFunctionEnergy (cubicThetaPrimeTraceCoordinateTerm hp F t) x.val=
      cubicThetaPrimeSectionEnergy hp F.val (t.val • x) := by
  let f := fun y => cubicThetaPrimeSectionFunction hp F.val
    (cubicThetaMobius (cubicThetaPrincipalComplex t.val) y)
  have hf := (F.property.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds
    (cubicThetaMobius_height_pos (cubicThetaPrincipalComplex t.val) x.property))).differentiableAt
      (by norm_num)
  have hd : DifferentiableAt ℝ f x.val :=
    hf.comp x.val ((cubicThetaMobius_contDiffAt _ x.property).differentiableAt (by simp))
  have he : fderiv ℝ (cubicThetaPrimeTraceCoordinateTerm hp F t) x.val=
      star (cubicThetaKubotaValue t.val) • fderiv ℝ f x.val :=
    (hd.hasFDerivAt.const_smul (star (cubicThetaKubotaValue t.val))).fderiv
  have hc : cubicThetaFunctionEnergy (cubicThetaPrimeTraceCoordinateTerm hp F t) x.val=
      cubicThetaFunctionEnergy f x.val := by
    unfold cubicThetaFunctionEnergy
    rw [he,ContinuousLinearMap.smul_comp,cubicThetaTangentEnergy_complex_smul,
      norm_star,cubicThetaKubotaValue_norm,one_pow,one_mul]
  rw [hc]
  exact cubicThetaFunctionEnergy_mobius (cubicThetaPrimeSectionFunction hp F.val)
    (cubicThetaPrincipalComplex t.val) x.property hf

theorem cubicThetaPrimeTraceSection_energy_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (x : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaPrimeTraceSection hp F.val) x≤
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*
        ∑ t : cubicThetaPrimeTransversal hp, cubicThetaPrimeSectionEnergy hp F.val (t.val • x) := by
  have he : cubicThetaSectionFunction (cubicThetaPrimeTraceSection hp F.val)=ᶠ[𝓝 x.val]
      (fun y => ∑ t : cubicThetaPrimeTransversal hp, cubicThetaPrimeTraceCoordinateTerm hp F t y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds x.property] with y hy
    exact cubicThetaPrimeTraceSection_function hp F.val hy
  have hs := mul_le_mul_of_nonneg_left
    (cubicThetaFunctionEnergy_sum_le Finset.univ (cubicThetaPrimeTraceCoordinateTerm hp F) x.val
      (fun t _ => cubicThetaPrimeTraceCoordinateTerm_differentiable hp F t x.property))
    (sq_nonneg x.val.2)
  change x.val.2^2*cubicThetaFunctionEnergy
    (cubicThetaSectionFunction (cubicThetaPrimeTraceSection hp F.val)) x.val≤_
  have hd : cubicThetaFunctionEnergy
      (cubicThetaSectionFunction (cubicThetaPrimeTraceSection hp F.val)) x.val=
      cubicThetaFunctionEnergy (fun y => ∑ t : cubicThetaPrimeTransversal hp,
        cubicThetaPrimeTraceCoordinateTerm hp F t y) x.val := by
    unfold cubicThetaFunctionEnergy
    rw [he.fderiv_eq]
  rw [hd]
  calc
    _ ≤ x.val.2^2*((Finset.univ.card:ℝ)*∑ t : cubicThetaPrimeTransversal hp,
        cubicThetaFunctionEnergy (cubicThetaPrimeTraceCoordinateTerm hp F t) x.val) := hs
    _ = _ := by
      rw [mul_left_comm,Finset.mul_sum]
      simp_rw [cubicThetaPrimeTraceCoordinateTerm_energy]
      rw [Finset.card_univ,←Nat.card_eq_fintype_card,
        (cubicThetaPrimeTransversal_complement hp).card_right]

end CubicFirstMoment

end

end OAI
