import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedRamified
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedModel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedReduction

namespace OAI

/-! Remove every ramified and nonprimary frequency from the remaining
coefficient identification problem. This is an equivalence of exact goals,
not an additional analytic input. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNormalizedObservedCoefficient_neg {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient (-h)=cubicThetaNormalizedObservedCoefficient h := by
  have hn : norm (-1:Eisenstein)=1 := by
    change Complex.normSq (-1:ℂ)=1
    norm_num
  have hw := cubicThetaPoleWeight_mul (u:=(-1:Eisenstein)) (by norm_num) hh
  rw [hn] at hw
  simp only [neg_one_mul,Real.one_rpow,one_mul] at hw
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
  rw [cubicThetaArithmeticFourierResidue_neg hh,hw]

lemma cubicThetaPrimaryRepresentative {h : Eisenstein} (hh : ¬lambdaE∣h) :
    ∃ (a : Eisenstein) (e : Eisensteinˣ), primary a ∧ h=a*(e:Eisenstein) := by
  have h0 : h≠0 := fun hz => hh (hz ▸ dvd_zero lambdaE)
  obtain ⟨e,k,a,ha,he⟩ := unit_ramified_primary_decomposition h0
  have hm := congrArg (emultiplicity lambdaE) he
  simp only [emultiplicity_eq_zero.mpr hh,emultiplicity_mul lambdaE_prime,
    unit_lambda_emultiplicity,emultiplicity_pow_self_of_prime lambdaE_prime,
    primary_lambda_emultiplicity ha,zero_add,add_zero] at hm
  have hk : k=0 := by exact_mod_cast hm.symm
  exact ⟨a,e,ha,by simpa only [hk,pow_zero,mul_one,mul_comm] using he⟩

theorem cubicThetaCoefficientAgreement_primary_reduction :
    (∀ h : Eisenstein, h≠0 → cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticCoefficient (-lambdaE*h)) ↔
    (∀ h : Eisenstein, primary h → cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticCoefficient (-lambdaE*h)) := by
  constructor
  · intro H h hh
    exact H h (primary_ne_zero hh)
  · intro H
    apply cubicThetaCoefficientAgreement_ramified_reduction.mpr
    constructor
    · intro h hh
      by_cases hp : primary h
      · exact H h hp
      by_cases hn : primary (-h)
      · have h0 : h≠0 := fun hz => hh (hz ▸ dvd_zero lambdaE)
        calc
          _ = cubicThetaNormalizedObservedCoefficient (-h) :=
            (cubicThetaNormalizedObservedCoefficient_neg h0).symm
          _ = cubicThetaArithmeticCoefficient (-lambdaE*(-h)) := H (-h) hn
          _ = _ := by
            rw [show -lambdaE*(-h)= -(-lambdaE*h) by ring,
              cubicThetaArithmeticCoefficient_even]
      · exact cubicThetaNormalizedObservedCoefficient_primary_support_eq hh hp hn
    · intro h hh
      obtain ⟨a,e,ha,he⟩ := cubicThetaPrimaryRepresentative hh
      rw [he,cubicThetaNormalizedObservedCoefficient_lambda_square_unit ha,
        cubicThetaArithmeticCoefficient_ramified_signed ha,H a ha]

end CubicFirstMoment

end

end OAI
