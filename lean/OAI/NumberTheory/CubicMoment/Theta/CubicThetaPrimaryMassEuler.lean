import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMassFactorization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryCubes
import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerSeries
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticEulerFactor

namespace OAI

/-! The primary norm series omits exactly the single ideal above three. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryGenerator_iff_unramified (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator ν) ↔ ν cubicThetaRamifiedPrime=0 := by
  constructor
  · intro hp
    apply Nat.eq_zero_of_not_pos
    intro hν
    have hd := (cubicThetaRamifiedPrime_dvd_iff ν).mpr hν
    have hd' : lambdaE ∣ idealPrimaryGenerator ν :=
      hd.trans (primaryNormalize_associated (idealExponentGenerator ν)).dvd
    exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hp).isRelPrime hd' dvd_rfl)
  · intro hν
    exact cubicThetaPrimaryGenerator_primary ⟨ν,hν⟩

lemma cubicThetaPrimaryMass_ideal (t : ℝ) :
    (cubicThetaPrimaryMass t:ℂ)=normDirichletSeries
      (primeIdealRestriction {cubicThetaRamifiedPrime} (fun _ => 1)) idealExponentNorm (t:ℂ) := by
  have h := primary_ideal_tsum (fun a => ((norm a)^(-t):ℝ))
  change (∑' ν, if primary (idealPrimaryGenerator ν) then
    (((norm (idealPrimaryGenerator ν))^(-t):ℝ):ℂ) else 0)=_ at h
  unfold cubicThetaPrimaryMass
  rw [Complex.ofReal_tsum,←h]
  unfold normDirichletSeries
  apply tsum_congr
  intro ν
  rw [cubicThetaPrimaryGenerator_iff_unramified,idealPrimaryGenerator_norm]
  simp only [primeIdealRestriction,Finset.mem_singleton,forall_eq]
  split_ifs
  · rw [one_mul]
    simpa only [Complex.ofReal_neg] using Complex.ofReal_cpow (idealExponentNorm_pos ν).le (-t)
  · rw [zero_mul]

theorem cubicThetaPrimaryMass_euler {t : ℝ} (ht : 1 < t) :
    (cubicThetaPrimaryMass t:ℂ)=(1-(3:ℂ)^(-(t:ℂ)))*principalIdealZeta (t:ℂ) := by
  rw [cubicThetaPrimaryMass_ideal,idealDirichlet_single_exclusion _ _ (by simp)
    (by intros; simp) (by simpa using ht),←principalIdealZeta_right (by simpa using ht)]
  simp only [idealExponentNorm_single,pow_one,cubicThetaRamifiedPrime_norm,Nat.cast_ofNat,
    one_mul,Complex.ofReal_ofNat]

lemma cubicThetaPrimaryMass_pos {t : ℝ} (ht : 1 < t) : 0 < cubicThetaPrimaryMass t := by
  have h := (cubicThetaPrimaryMass_summable ht).le_tsum
    (⟨1,by norm_num [primary]⟩:PrimaryArgument)
    (fun d _ => Real.rpow_nonneg (norm_nonneg d.val) _)
  have he : (norm (1:Eisenstein))^(-t)=1 := by rw [norm_one_eq,Real.one_rpow]
  exact lt_of_lt_of_le (he ▸ zero_lt_one) h

end CubicFirstMoment

end

end OAI
