import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFirstCoefficient

namespace OAI

/-! The first character branch has zero horizontal mean. Integer dilation
turns each summand into a translate of the original slice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstPeriodization_dilate {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (b : Eisenstein) (z : ℂ) :
    cubicThetaPrimeCubeFirstTerm p f b ((p:ℂ)*z)=
      cubicSymbol p (3*b)*f (z+3*(b:ℂ)/(p:ℂ)^2) := by
  unfold cubicThetaPrimeCubeFirstTerm
  rw [mul_div_cancel_left₀ z (show (p:ℂ)≠0 from fun he => hp.2.ne_zero (Subtype.ext he))]

lemma cubicThetaPrimeCubeFirstPeriodization_integrable {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) : IntegrableOn (cubicThetaPrimeCubeFirstPeriodization p f) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact ((cubicThetaPrimeCubeFirstPeriodization_continuous hp f).continuousOn.integrableOn_compact hK).mono_set hsub

theorem cubicThetaPrimeCubeFirstPeriodization_mean {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaPrimeCubeFirstPeriodization p f z)=0 := by
  let : Finite (Residues (p^2)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^2)) := Fintype.ofFinite _
  rw [←cubicThetaHorizontal_mul_integral hp.2.ne_zero _
    (cubicThetaPrimeCubeFirstPeriodization_periodic hp f hf)
    (cubicThetaPrimeCubeFirstPeriodization_integrable hp f)]
  unfold cubicThetaPrimeCubeFirstPeriodization
  simp_rw [cubicThetaPrimeCubeFirstPeriodization_dilate hp,tsum_fintype]
  have hi (r : Residues (p^2)) : IntegrableOn
      (fun z => f (z+3*(residueRepresentative (p^2) r:ℂ)/(p:ℂ)^2)) cubicThetaHorizontalCell := by
    simpa only [one_mul] using cubicThetaHorizontal_affine_integrable f 1
      (3*(residueRepresentative (p^2) r:ℂ)/(p:ℂ)^2)
  rw [integral_finsetSum Finset.univ (fun r _ => (hi r).const_mul _)]
  simp_rw [integral_const_mul,cubicThetaHorizontal_translate_integral f hf]
  have hs : (∑ r : Residues (p^2),cubicSymbol p (3*residueRepresentative (p^2) r))=0 := by
    simpa only [tsum_fintype] using cubicThetaPrimeCubeFirstCoefficient_sum hp
  rw [←Finset.sum_mul,hs,zero_mul]

end CubicFirstMoment

end

end OAI
