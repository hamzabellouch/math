import Mathlib
import OAI.Probability.Ballisticity.Estimates.PastPhaseExtension
import OAI.Probability.Ballisticity.Crossings.CutoffTimeAverages

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_mesh_phase_bound {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 0 < n)
    (hnlarge : ((c:ℝ)*(a^2+b^2)/2)*(((t:ℝ)-s)/n) ≤ 1) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-((((c:ℝ)*(a^2+b^2)/2)*(((t:ℝ)-s)/n):ℝ):ℂ))^n*
        (∫ P, F (pairPastCoordinates v P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *K*(n:ℝ)*Real.exp (-A*ρ^2/(((t:ℝ)-s)/n))+
        jointTaylorCoeff a b*(n:ℝ)*(Real.sqrt ((c:ℝ)*(((t:ℝ)-s)/n)))^3+
        2*|a*b| *(c:ℝ)*(∑ j ∈ Finset.range n, ((t:ℝ)-s)/n*
          cutoffMeanExtension μ ρ (realMesh s t n j))) := by
  let δ := ((t:ℝ)-s)/n
  let r : ℂ := 1-((((c:ℝ)*(a^2+b^2)/2)*δ:ℝ):ℂ)
  let z : ℕ → ℂ := fun j => ∫ P, F (pairPastCoordinates v P)*
      charPhase (pairLinearIncrement a b s (unitMesh s t n j) P) ∂μ
  let D := 2*|a*b| *K*Real.exp (-A*ρ^2/δ)+jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*δ))^3
  let C := 2*|a*b| *(c:ℝ)
  let e : ℕ → ℝ := fun j => ‖F‖*(D+C*δ*cutoffMeanExtension μ ρ (realMesh s t n j))
  have hz0 : z 0=∫ P, F (pairPastCoordinates v P) ∂μ := by
    dsimp [z]
    rw [unitMesh_zero]
    simp only [pairLinearIncrement,pairPathIncrement,ContinuousMap.coe_mk,Bool.false_eq_true,
      ↓reduceIte,sub_self,mul_zero,add_zero,charPhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  have hzn : z n=∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ := by
    simp only [z,unitMesh_last s t hn]
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le)) (Nat.cast_nonneg n)
  have hc : 0 ≤ (c:ℝ)*(a^2+b^2)/2 := by positivity
  have hr : ‖r‖ ≤ 1 := realEulerCoefficient_norm hc hδ hnlarge
  have he : ∀ j < n, ‖z (j+1)-r*z j‖ ≤ e j := by
    intro j hj
    have hju := unitMesh_between s t hst.le hn hj.le
    have hjv := unitMesh_between s t hst.le hn (Nat.succ_le_of_lt hj)
    have hh := normalJointPast_cumulative_phase_step μ c h hK hcross v s
      (unitMesh s t n j) (unitMesh s t n (j+1)) hv hju.1
      (unitMesh_step_lt s t hst hn hj) (lt_of_le_of_lt hjv.2 ht) F a b hρ
    rw [unitMesh_sub s t hst.le hn hj] at hh
    have hcoef : 1-((((c:ℝ)*δ*(a^2+b^2)/2):ℝ):ℂ)=r := by
      dsimp [r]
      congr 1
      ring_nf
    change ‖z (j+1)-(1-((((c:ℝ)*δ*(a^2+b^2)/2):ℝ):ℂ))*z j‖ ≤ _ at hh
    rw [hcoef] at hh
    have hcut : (∫ P : RealPathPair, nearDiagonalCutoff ρ
      (P.1 (unitMesh s t n j)-P.2 (unitMesh s t n j)) ∂μ)=
      cutoffMeanExtension μ ρ (realMesh s t n j) := rfl
    rw [hcut] at hh
    convert hh using 1
  have hh := contraction_recurrence_error z r e n hr he
  rw [hz0,hzn] at hh
  calc
    _ ≤ ∑ j ∈ Finset.range n, e j := hh
    _ = _ := by
      simp only [e,mul_add,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_range,nsmul_eq_mul]
      dsimp [D,C,δ]
      ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma complexEuler_tendsto (lam L : ℝ) :
    Tendsto (fun n : ℕ => (1-((lam*(L/n):ℝ):ℂ))^n) atTop
      (𝓝 (Complex.exp ((-lam*L:ℝ):ℂ))) := by
  convert Complex.tendsto_one_add_div_pow_exp (((-lam*L:ℝ):ℂ)) using 1
  funext n
  congr 1
  push_cast
  ring

lemma normalJointPast_phase_bound {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      Complex.exp ((-((c:ℝ)*(a^2+b^2)/2)*((t:ℝ)-s):ℝ):ℂ)*
        (∫ P, F (pairPastCoordinates v P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *(c:ℝ)*(∫ u in (s:ℝ)..t, cutoffMeanExtension μ ρ u)) := by
  let lam := (c:ℝ)*(a^2+b^2)/2
  let L := (t:ℝ)-s
  have hL : 0 < L := sub_pos.mpr hst
  have hEu := complexEuler_tendsto lam L
  have hleft := ((tendsto_const_nhds.sub (hEu.mul_const
    (∫ P, F (pairPastCoordinates v P) ∂μ))).norm :
    Tendsto (fun n : ℕ => ‖(∫ P, F (pairPastCoordinates v P)*
      charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-((lam*(L/n):ℝ):ℂ))^n*(∫ P, F (pairPastCoordinates v P) ∂μ)‖) atTop
      (𝓝 ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      Complex.exp ((-lam*L:ℝ):ℂ)*(∫ P, F (pairPastCoordinates v P) ∂μ)‖))
  have hex := (scaled_exp_tendsto_zero (mul_pos hA (sq_pos_of_pos hρ)) hL).const_mul (2*|a*b| *K)
  have hcu := (scaled_sqrt_cube_tendsto_zero c.coe_nonneg hL.le).const_mul (jointTaylorCoeff a b)
  have hri := (cutoff_riemann_tendsto μ ρ hst).const_mul (2*|a*b| *(c:ℝ))
  have hr := ((hex.add hcu).add hri).const_mul ‖F‖
  simp only [mul_zero,zero_add] at hr
  have hnlarge : ∀ᶠ n : ℕ in atTop, lam*(L/n) ≤ 1 := by
    have hh : Tendsto (fun n : ℕ => lam*(L/n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => L/(n:ℝ)) atTop (𝓝 0)).const_mul lam
    exact (hh.eventually_lt_const zero_lt_one).mono (fun n hn => hn.le)
  apply le_of_tendsto_of_tendsto hleft hr
  filter_upwards [eventually_gt_atTop 0,hnlarge] with n hn hnl
  have hh := normalJointPast_mesh_phase_bound μ c h hK hcross v s t hv hst ht F a b hρ hn hnl
  simpa only [lam,L,neg_mul,mul_assoc] using hh

lemma normalJointPast_joint_characteristic {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)=
      Complex.exp ((-((c:ℝ)*(a^2+b^2)/2)*((t:ℝ)-s):ℝ):ℂ)*
        (∫ P, F (pairPastCoordinates v P) ∂μ) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hh := ((diagonal_zero_subinterval_cutoff_tendsto μ hz s t hst.le).const_mul
    (2*|a*b| *(c:ℝ))).const_mul ‖F‖
  simp only [mul_zero] at hh
  apply ge_of_tendsto hh
  filter_upwards [] with n
  exact normalJointPast_phase_bound μ c h hA hK hcross v s t hv hst ht F a b
    (by positivity : 0 < 1/((n:ℝ)+1))

end DirectionalTransience

end

end

end OAI
