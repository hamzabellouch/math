import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierIntegrability
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalPeriodMean

namespace OAI

/-! The exact nonzero Fourier coefficient of finite lattice periodization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaHorizontalPeriodization_fourier {a : Eisenstein} (ha : a≠0)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalPeriodization a f)=
      (norm a:ℂ)*cubicThetaHorizontalFourierCoefficient (a*h) f := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  let : Finite (Residues a) := finite_residues ha
  let : Fintype (Residues a) := Fintype.ofFinite _
  have ht (b : Eisenstein) (z : ℂ) :
      cubicThetaHorizontalFraction a f b ((a:ℂ)*z)=f (z+3*(b:ℂ)/(a:ℂ)) := by
    unfold cubicThetaHorizontalFraction
    congr 1
    field_simp [haC]
  have hphase (b : Eisenstein) :
      cubicThetaHorizontalCharacter (a*h) (3*(b:ℂ)/(a:ℂ))=1 := by
    rw [cubicThetaHorizontalCharacter_mul_index]
    have he : (a:ℂ)*(3*(b:ℂ)/(a:ℂ))=3*(b:ℂ) := by field_simp [haC]
    rw [he,cubicThetaHorizontalCharacter_three]
  calc
    _ = cubicThetaHorizontalFourierCoefficient (a*h)
        (fun z => cubicThetaHorizontalPeriodization a f ((a:ℂ)*z)) :=
      (cubicThetaHorizontalFourier_dilate _ (cubicThetaHorizontalPeriodization_periodic ha f hf) ha h
        (cubicThetaHorizontalFourier_integrable h _ (cubicThetaHorizontalPeriodization_continuous ha f))).symm
    _ = ∑ r : Residues a,cubicThetaHorizontalFourierCoefficient (a*h)
        (fun z => f (z+3*(residueRepresentative a r:ℂ)/(a:ℂ))) := by
      unfold cubicThetaHorizontalFourierCoefficient cubicThetaHorizontalPeriodization
      simp_rw [ht,tsum_fintype,Finset.mul_sum]
      apply integral_finsetSum
      intro r _
      exact cubicThetaHorizontalFourier_integrable (a*h) _
        (f.continuous.comp (continuous_id.add continuous_const))
    _ = _ := by
      simp_rw [cubicThetaHorizontalFourier_translate (a*h) f hf,hphase,one_mul]
      rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,residues_card ha,nsmul_eq_mul]
      have hn : (normNat a:ℂ)=(norm a:ℂ) := by exact_mod_cast normNat_cast a
      rw [hn]

end CubicFirstMoment

end

end OAI
