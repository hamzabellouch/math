import OAI.Analysis.Laughlin.Tensor.ExteriorAdjoint

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem headPairAmplitude_readout (n Q : ℕ) (x : Space Q) (p : ℕ)
    (b : Configuration n Q) :
    headPairAmplitude (normalizedTensorReadout (n+2) Q x) p b =
      (((Real.sqrt ((n+2).factorial : ℝ))⁻¹ : ℂ)*(Real.sqrt 2 : ℂ)) *
        occupationInner Q (orderedWedge b) (sourcePairEnd Q p x) := by
  have he (i j : Fin (Q+1)) :
      occupationInner Q (orderedWedge (Fin.cons i (Fin.cons j b))) x =
        occupationInner Q (orderedWedge b) (annihilate j (annihilate i x)) := by
    rw [orderedWedge_cons,orderedWedge_cons,create_annihilate_adjoint,create_annihilate_adjoint]
  simp only [headPairAmplitude,normalizedTensorReadout,he,sourcePairEnd,pairEnd,
    LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    occupationInner_sum_right,occupationInner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt (2 : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp

theorem normalizedTensorReadout_zero_energy (n Q : ℕ) (x : Space Q)
    (hx : sourceFockEnergy Q x=0) :
    energy (normalizedTensorReadout (n+2) Q x)=0 := by
  rw [energy_head_pair n Q _ (normalizedTensorReadout_antisymmetric (n+2) Q x)]
  have hp := (sourceFockEnergy_eq_zero Q x).mp hx
  have hs : (∑ p ∈ Finset.range (2*Q-1), ∑ b : Configuration n Q,
      ‖headPairAmplitude (normalizedTensorReadout (n+2) Q x) p b‖^2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hpr
    simp [headPairAmplitude_readout,hp p hpr,occupationInner]
  rw [hs,mul_zero]

end Laughlin.Fock

end OAI
