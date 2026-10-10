import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeRegularity

namespace OAI

/-! The pointwise gradient bound for the actual cubed-prime trace. Its
summands use the hyperbolic isometry identity, not a coordinate estimate. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHeckeCoordinate_energy {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (t : cubicThetaPrimeCubeTransversal p) (x : CubicThetaPoint) :
    x.val.2^2*cubicThetaFunctionEnergy (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val=
      cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x) := by
  let f := fun y => cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaPrimeCubeHeckeMatrix hp t) y)
  have hf := (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds
    (cubicThetaMobius_height_pos (cubicThetaPrimeCubeHeckeMatrix hp t) x.property))).differentiableAt
      (by norm_num)
  have hd : DifferentiableAt ℝ f x.val :=
    hf.comp x.val ((cubicThetaMobius_contDiffAt _ x.property).differentiableAt (by simp))
  have he : fderiv ℝ (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val=
      star (cubicThetaKubotaValue t.val) • fderiv ℝ f x.val :=
    (hd.hasFDerivAt.const_smul (star (cubicThetaKubotaValue t.val))).fderiv
  have hc : cubicThetaFunctionEnergy (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val=
      cubicThetaFunctionEnergy f x.val := by
    unfold cubicThetaFunctionEnergy
    rw [he,ContinuousLinearMap.smul_comp,cubicThetaTangentEnergy_complex_smul,
      norm_star,cubicThetaKubotaValue_norm,one_pow,one_mul]
  rw [hc]
  exact cubicThetaFunctionEnergy_mobius (cubicThetaSectionFunction F)
    (cubicThetaPrimeCubeHeckeMatrix hp t) x.property hf

theorem cubicThetaPrimeCubeHecke_energy_le {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (x : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F) x≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,
          cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have he : cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F)=ᶠ[𝓝 x.val]
      (fun y => ∑ t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeHeckeCoordinate hp F t y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds x.property] with y hy
    simpa only [tsum_fintype] using cubicThetaPrimeCubeHecke_function hp F hy
  have hd (t : cubicThetaPrimeCubeTransversal p) :
      DifferentiableAt ℝ (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val :=
    ((cubicThetaPrimeCubeHeckeCoordinate_c1 hp F hF t).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds x.property)).differentiableAt (by norm_num)
  have hs := mul_le_mul_of_nonneg_left
    (cubicThetaFunctionEnergy_sum_le Finset.univ (cubicThetaPrimeCubeHeckeCoordinate hp F) x.val
      (fun t _ => hd t)) (sq_nonneg x.val.2)
  change x.val.2^2*cubicThetaFunctionEnergy (cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F)) x.val≤_
  have hfun : cubicThetaFunctionEnergy (cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F)) x.val=
      cubicThetaFunctionEnergy (fun y => ∑ t : cubicThetaPrimeCubeTransversal p,
        cubicThetaPrimeCubeHeckeCoordinate hp F t y) x.val := by
    unfold cubicThetaFunctionEnergy
    rw [he.fderiv_eq]
  rw [hfun,tsum_fintype]
  calc
    _ ≤ x.val.2^2*((Finset.univ.card:ℝ)*∑ t : cubicThetaPrimeCubeTransversal p,
        cubicThetaFunctionEnergy (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val) := hs
    _ = _ := by
      rw [mul_left_comm,Finset.mul_sum]
      simp_rw [cubicThetaPrimeCubeHeckeCoordinate_energy hp F hF]
      rw [Finset.card_univ,←Nat.card_eq_fintype_card,
        (cubicThetaPrimeCubeTransversal_complement p).card_right]

end CubicFirstMoment

end

end OAI
