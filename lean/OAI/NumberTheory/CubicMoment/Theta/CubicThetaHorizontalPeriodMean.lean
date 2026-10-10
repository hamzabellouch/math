import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalPeriodization

namespace OAI

/-! The literal bottom-branch periodization has its exact degree as mean. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaHorizontalPeriodization_mean {a : Eisenstein} (ha : a≠0)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaHorizontalPeriodization a f z)=
      (norm a:ℂ)*(∫ z in cubicThetaHorizontalCell,f z) := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  let : Finite (Residues a) := finite_residues ha
  let : Fintype (Residues a) := Fintype.ofFinite _
  have ht (b : Eisenstein) (z : ℂ) :
      cubicThetaHorizontalFraction a f b ((a:ℂ)*z)=f (z+3*(b:ℂ)/(a:ℂ)) := by
    unfold cubicThetaHorizontalFraction
    congr 1
    field_simp [haC]
  rw [←cubicThetaHorizontal_mul_integral ha _
    (cubicThetaHorizontalPeriodization_periodic ha f hf)
    (cubicThetaHorizontalPeriodization_integrable ha f)]
  unfold cubicThetaHorizontalPeriodization
  simp_rw [ht,tsum_fintype]
  have hi (r : Residues a) : IntegrableOn (fun z => f (z+3*(residueRepresentative a r:ℂ)/(a:ℂ)))
      cubicThetaHorizontalCell := by
    simpa only [one_mul] using cubicThetaHorizontal_affine_integrable f 1
      (3*(residueRepresentative a r:ℂ)/(a:ℂ))
  rw [integral_finsetSum Finset.univ (fun r _ => hi r)]
  simp_rw [cubicThetaHorizontal_translate_integral f hf]
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,residues_card ha,nsmul_eq_mul]
  have hn : (normNat a:ℂ)=(norm a:ℂ) := by exact_mod_cast normNat_cast a
  rw [hn]

end CubicFirstMoment

end

end OAI
