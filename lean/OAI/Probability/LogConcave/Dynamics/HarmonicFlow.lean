import Mathlib
import OAI.Probability.LogConcave.Dynamics.FlowRestrict

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

theorem exists_harmonic_flow {d : ℕ} {H : Point d → ℝ} {L : ℝ≥0}
    (hH : ContDiff ℝ 2 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith L (gradient H)) {a b : ℝ} (hab : a≤b) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p a=p ∧ ∀t∈Icc a b,
        HasDerivWithinAt (Ψ p) ((Ψ p t).2,-gradient H (Ψ p t).1) (Icc a b) t) ∧
      (∀t∈Icc a b,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc a b,((gibbs H).prod (stdGaussian (Point d))).map (fun p => Ψ p t)=
        (gibbs H).prod (stdGaussian (Point d))) := by
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] using
      integrable_tilted H hH.continuous continuous_const ht (growth_const (1:ℝ)) 0
  let := probability_gibbs_of_partition (partition_pos_of_continuous hH.continuous).ne'
    (partition_ne_top_of_integrable hi)
  let K : Point d → Point d →L[ℝ] Point d := fun _ => -(ContinuousLinearMap.id ℝ (Point d))
  let m := fun z => -gradient H z
  have hK : ContDiff ℝ 1 K := contDiff_const
  have hm : ContDiff ℝ 1 m := (Trapezoid.contDiff_gradient hH).neg
  have hKb (y : Point d) : ‖K y‖≤(1:ℝ) := by
    dsimp [K]
    rw [norm_neg]
    exact ContinuousLinearMap.norm_id_le
  have hmL : LipschitzWith L m := hL.neg
  have hμ : Integrable (fun z : Point d => ‖z‖) (gibbs H) := by
    simpa only [pow_one] using (ht.hasExpMoments hH.continuous).hasMoments 1
  have hs : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂gibbs H)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂gibbs H := by
    intro u φ hφ hφc
    have hh := compact_gibbs_ibp (hH.of_le (by norm_num)) hi hφ hφc u
    dsimp [K,m]
    simp only [map_neg,ContinuousLinearMap.adjoint_id,
      neg_apply,ContinuousLinearMap.id_apply,
      inner_neg_right,neg_mul,integral_neg]
    simpa only [directional,real_inner_comm] using congrArg Neg.neg hh.symm
  obtain ⟨Ψ,hΨ,hc,hlaw⟩ := exists_skew_centering_flow hK hm (by norm_num : (0:ℝ)≤1) hKb hmL hμ hs
    (by norm_num : (0:ℝ)<1) hab
  refine ⟨Ψ,fun p => ⟨(hΨ p).1,(hΨ p).2.1,fun t ht => ?_⟩,hc,hlaw⟩
  simpa only [skewCenteringField,K,m,inv_one,one_smul,neg_apply,
    ContinuousLinearMap.id_apply,neg_neg,map_neg,ContinuousLinearMap.adjoint_id,neg_smul] using (hΨ p).2.2 t ht
end LogConcaveSampling

end

end

end

end OAI
