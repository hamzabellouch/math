import Mathlib
import OAI.Probability.SKGap.Stability.GaugeStabilityLaw
import OAI.Probability.SKGap.Stability.TapFieldE

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

lemma stable_hessian_coercive {n : ℕ} {j A ε c ρ : ℝ}
    {J : Matrix (Fin n) (Fin n) ℝ} {h y a : Field n}
    (hbad : ¬rootBad j A ε c ρ J h)
    (hy : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ))
    (ha : ∀ i,a i∈Icc 0 A) (hd : (∑ i,(a i-spinVariance y i)^2)≤ε^2*(n:ℝ)) :
    ∀ v : Field n,c*vectorSqNorm v ≤ quadraticForm (fieldHessian j J y a) v := by
  intro v
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  let H := fieldHessian j J y a
  have hunit : ∀ z : EuclideanSpace ℝ (Fin n),‖z‖=1 → c < matrixQuad H z := by
    intro z hz
    exact lt_of_not_ge (fun hh=>hbad ⟨y,hy,a,ha,hd,z,hz,hh⟩)
  by_cases hx : x=0
  · have hv : v=0 := congrArg WithLp.ofLp hx
    simp [hv,vectorSqNorm,quadraticForm]
  · have hx0 : 0<‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖(‖x‖⁻¹:ℝ) • x‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hx0),inv_mul_cancel₀ hx0.ne']
    have hh := (hunit (‖x‖⁻¹ • x) hu).le
    rw [matrixQuad_smul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖x‖)
    have he : ‖x‖^2*((‖x‖⁻¹)^2*matrixQuad H x)=matrixQuad H x := by
      field_simp
    rw [he] at hmul
    have hn : ‖x‖^2=vectorSqNorm v := vectorNorm_sq v
    rw [hn,mul_comm] at hmul
    exact hmul

theorem stable_field_root_and_inverse {n : ℕ} (hn : 0 < n)
    {j A K ε c ρ : ℝ} (hj : 0≤j) (hA : 1≤A) (hK : 0≤K) (hc : 0<c) (hρ : 0<ρ)
    (J : Disorder n) (h : Field n)
    (hop : operatorBound K (coupling J)) (hbad : ¬rootBad j A ε c ρ (coupling J) h) :
    ∃ r : Field n,tapField j (coupling J) h r=0 ∧
      (∀ y,tapField j (coupling J) h y=0 → y=r) ∧
      ∀ y,vectorNorm (tapField j (coupling J) h y)<ρ*sqrt (n:ℝ) →
        vectorNorm (y-r)≤(1+(K+3*j)/c)*vectorNorm (tapField j (coupling J) h y) := by
  apply tap_root_and_distance hn hj hK hc (mul_pos hρ (sqrt_pos.mpr (Nat.cast_pos.mpr hn)))
    (J := coupling J) (by ext i k; exact coupling_symm J k i) h hop
  intro y hy
  apply stable_hessian_coercive hbad hy
  · intro i
    exact ⟨(spinVariance_pos y i).le,(spinVariance_le_one y i).trans hA⟩
  · simp only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    positivity
end SKGap.ObservationBridge

end
end

end OAI
