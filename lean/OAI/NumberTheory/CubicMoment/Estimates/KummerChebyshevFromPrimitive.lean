import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveCubicPrimeEstimate
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimeEstimateTransfer
import OAI.NumberTheory.CubicMoment.Estimates.CubicPrimeConductorScale

namespace OAI

/-! The literal cubic-symbol prime sum for every nonzero noncube numerator,
from the primitive Hecke completion input and proved elementary reciprocity. -/
noncomputable section
namespace CubicFirstMoment

theorem kummer_chebyshev_from_primitive (hpub : PrimitiveResidueHeckeInput)
    (hperiod : CubicSupplementaryPeriodicity) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3=v) →
    ∀ X : ℝ, X0 ≤ X →
      ‖primeChebyshev (fun p => cubicSymbol p v) X‖ ≤
        B*primeCancellationWeight c (810*norm v) X := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := primitive_cubic_prime_ideal_estimate hpub
  let X0 := max Y0 (Real.exp 2)
  refine ⟨B+1,c,X0,by linarith,hc,hc1,hY0.trans_le (le_max_left _ _),?_⟩
  intro v hv hnc X hX
  obtain ⟨d,ψ,hd,hp,_hdiv,hN,h3,hu,hi,_hval⟩ := cubicNumerator_primitive_conductor hperiod hv
  obtain ⟨x,hx,hcop,hne⟩ := (cubicNumeratorChar_ne_one_iff hperiod v hv).mp
    (cubicNumeratorChar_noncube hperiod hv hnc)
  have hψ : ψ ≠ 1 := hi.nonprincipal ⟨x,hcop,by
    rwa [cubicNumeratorChar_primary hperiod v hv hx]⟩
  obtain ⟨hQ,hscale,h7,hqQ⟩ := cubicNumerator_primitive_scale hv hd hN
  have hmain := hbound d hd ψ hp hψ h3 hu (810*norm v) hQ hscale h7 X
    ((le_max_left _ _).trans hX)
  have hXp : 0 < X := (Real.exp_pos 2).trans_le ((le_max_right _ _).trans hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hu0 : AngularUnitCompatible (9*v) (cubicNumeratorChar hperiod v hv) 0 := by
    intro u
    simpa only [theta_zero,mul_one] using cubicNumeratorChar_units hperiod v hv u
  have hh := primary_angular_prime_bound_of_primitive
    (mul_ne_zero (by norm_num : (9:Eisenstein) ≠ 0) hv) hd
    (show (3:Eisenstein) ∣ 9*v from ⟨3*v,by ring⟩)
    (cubicNumeratorChar hperiod v hv) ψ hi 0 hu0 hc.le hc1 hQ hqQ hXp hLX
    (by simpa only [angularResidueIdealChar_zero] using hmain)
  have he : primeChebyshev (fun p => (cubicNumeratorChar hperiod v hv)
      (Ideal.Quotient.mk (modulus (9*v)) p)*theta 0 p) X =
      primeChebyshev (fun p => cubicSymbol p v) X := by
    unfold primeChebyshev
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only
    rw [cubicNumeratorChar_primary hperiod v hv (mem_primeCutoff.mp hp).1.1,theta_zero,mul_one]
  rwa [he] at hh

end CubicFirstMoment

end

end OAI
