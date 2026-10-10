import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExceptionalAlgebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalEnergyResolvent

namespace OAI

/-! Algebra of the finite exceptional block. An invertible correction by
an idempotent gives the exact inverse off its scalar exceptional value. -/
noncomputable section
namespace CubicFirstMoment

variable {A : Type*} [Ring A] [Algebra ℂ A]

omit [Algebra ℂ A] in
private lemma energy_commute_inverse
    {T P : A}
    (hT : IsUnit T) (h : Commute T P) : Commute (Ring.inverse T) P := by
  rw [← hT.unit_spec,Ring.inverse_unit]
  have hh : Commute (↑hT.unit) P := by simpa only [hT.unit_spec] using h
  exact hh.units_inv_left

lemma cubicThetaProjection_inverse_data
    (T P : A) (c : ℂ)
    (hPP : P*P=P) (hTP : T*P=c • P) (hPT : P*T=c • P)
    (hunit : IsUnit (T+P)) (hc : c≠0) :
    IsUnit T ∧ Ring.inverse T=Ring.inverse (T+P)*(1-P)+c⁻¹ • P := by
  let V := Ring.inverse (T+P)
  let L := V*(1-P)+c⁻¹ • P
  have hcomm : Commute T P := hTP.trans hPT.symm
  have hVP : Commute V P := energy_commute_inverse hunit
    (hcomm.add_left (Commute.refl P))
  have hVT : Commute V T := energy_commute_inverse hunit
    ((Commute.refl T).add_left hcomm.symm)
  have hvanish : P*V*(1-P)=0 := by
    rw [← hVP.eq,mul_assoc,mul_sub,mul_one,hPP,sub_self,mul_zero]
  have hTV : T*V=1-P*V := by
    calc
      _ = ((T+P)-P)*V := by congr 1; abel
      _ = (T+P)*V-P*V := sub_mul _ _ _
      _ = _ := by rw [Ring.mul_inverse_cancel _ hunit]
  have hscalar : T*(c⁻¹ • P)=P := by
    rw [mul_smul_comm,hTP,smul_smul,inv_mul_cancel₀ hc,one_smul]
  have hright : T*L=1 := by
    calc
      T*L = T*(V*(1-P))+T*(c⁻¹ • P) := mul_add _ _ _
      _ = (T*V)*(1-P)+P := by rw [← mul_assoc,hscalar]
      _ = (1-P*V)*(1-P)+P := by rw [hTV]
      _ = (1-P)-(P*V)*(1-P)+P := by rw [sub_mul,one_mul]
      _ = 1 := by rw [hvanish]; abel
  have hLT : Commute L T := by
    have ha := hVT.mul_left ((Commute.one_left T).sub_left hcomm.symm)
    have hb : Commute (c⁻¹ • P) T := by
      change (c⁻¹ • P)*T=T*(c⁻¹ • P)
      rw [smul_mul_assoc,mul_smul_comm,hPT,hTP]
    exact ha.add_left hb
  have hleft : L*T=1 := hLT.eq.trans hright
  have hT : IsUnit T := ⟨⟨T,L,hright,hleft⟩,rfl⟩
  refine ⟨hT,?_⟩
  change Ring.inverse T=L
  calc
    _ = Ring.inverse T*(T*L) := by rw [hright,mul_one]
    _ = L := by rw [← mul_assoc,Ring.inverse_mul_cancel _ hT,one_mul]

lemma cubicThetaProjection_inverse
    (T P : A) (c : ℂ)
    (hPP : P*P=P) (hTP : T*P=c • P) (hPT : P*T=c • P)
    (hunit : IsUnit (T+P)) (hc : c≠0) :
    Ring.inverse T=Ring.inverse (T+P)*(1-P)+c⁻¹ • P :=
  (cubicThetaProjection_inverse_data T P c hPP hTP hPT hunit hc).2

end CubicFirstMoment

end

end OAI
