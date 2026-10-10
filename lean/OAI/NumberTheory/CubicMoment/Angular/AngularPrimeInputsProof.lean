import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeExplicit
import OAI.NumberTheory.CubicMoment.Angular.AngularNumeratorConductor
import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof

namespace OAI

/-! Both literal angular prime inputs follow from the published primitive
angular Hecke completion. Their original conductor majorants are preserved. -/
noncomputable section
namespace CubicFirstMoment

theorem fixedAngularPrimeExplicitEstimate_of_primitive (hpub : PrimitiveAngularHeckeInput) :
    FixedAngularPrimeExplicitEstimate := by
  obtain ⟨B,c,hB,hc,hbound⟩ := angular_prime_explicit_of_primitive hpub
  intro ℓ hℓ
  refine ⟨B,c,hB,hc,?_⟩
  intro a b ha hb hsa hsb _hcop X hX
  have hab : a*b ≠ 0 := mul_ne_zero hsa.ne_zero hsb.ne_zero
  have hq : (3:Eisenstein)*(a*b) ≠ 0 := mul_ne_zero (by norm_num) hab
  have hcontrol := angularConductor_controls ℓ hab
  have hh := hbound (3*(a*b)) hq (dvd_mul_right 3 (a*b))
    (primaryAngularMixedChar ℓ a b ha hb) ℓ hℓ (primaryAngularMixedChar_compatible ℓ ha hb)
    (angularAnalyticConductor ℓ a b) (angularAnalyticConductor_ge_one ℓ hsa hsb)
    hcontrol.1 hcontrol.2 X hX
  have he : primeChebyshev (fun p => primaryAngularMixedChar ℓ a b ha hb
      (Ideal.Quotient.mk (modulus (3*(a*b))) p)*theta ℓ p) X =
      primeChebyshev (angularMixedCubic ℓ a b) X := by
    unfold primeChebyshev
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only
    rw [primaryAngularMixedChar_primary ℓ ha hb (mem_primeCutoff.mp hp).1.1]
    simp only [angularMixedCubic,mul_comm]
  rwa [he] at hh

theorem angularKummerPrimeExplicitEstimate_of_primitive (hpub : PrimitiveAngularHeckeInput) :
    AngularKummerPrimeExplicitEstimate := by
  obtain ⟨B,c,hB,hc,hbound⟩ := angular_prime_explicit_of_primitive hpub
  intro ℓ hℓ
  refine ⟨B,c,hB,hc,?_⟩
  intro v hv _hnc X hX
  have hq : (9:Eisenstein)*v ≠ 0 := mul_ne_zero (by norm_num) hv
  have hcontrol := angularConductor_controls ℓ (mul_ne_zero (by norm_num : (3:Eisenstein)≠0) hv)
  have heq : angularConductorFactor ℓ*norm ((3:Eisenstein)*v) =
      angularKummerAnalyticConductor ℓ v := by
    have h3 : norm (3:Eisenstein)=9 := by change Complex.normSq (3:ℂ)=9; norm_num
    rw [norm_mul_eq,h3]
    unfold angularKummerAnalyticConductor angularKummerConductorFactor
    ring
  have hmod : (3:Eisenstein)*(3*v)=9*v := by ring
  rw [hmod,heq] at hcontrol
  have hh := hbound (9*v) hq (show (3:Eisenstein) ∣ 9*v from ⟨3*v,by ring⟩)
    (angularNumeratorChar cubicSupplementaryPeriodicity_proved v hv ℓ) ℓ hℓ
    (angularNumeratorChar_compatible cubicSupplementaryPeriodicity_proved v hv ℓ)
    (angularKummerAnalyticConductor ℓ v) (angularKummerAnalyticConductor_ge_one ℓ hv)
    hcontrol.1 hcontrol.2 X hX
  have he : primeChebyshev (fun p => angularNumeratorChar cubicSupplementaryPeriodicity_proved v hv ℓ
      (Ideal.Quotient.mk (modulus (9*v)) p)*theta ℓ p) X =
      primeChebyshev (angularKummerCharacter ℓ v) X := by
    unfold primeChebyshev
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only
    rw [angularNumeratorChar_primary cubicSupplementaryPeriodicity_proved v hv ℓ (mem_primeCutoff.mp hp).1.1]
    simp only [angularKummerCharacter,mul_comm]
  rwa [he] at hh

end CubicFirstMoment

end

end OAI
