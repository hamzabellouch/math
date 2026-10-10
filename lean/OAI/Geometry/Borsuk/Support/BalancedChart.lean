import Mathlib
import OAI.Geometry.Borsuk.Support.PurityChart

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section BalancedChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma split_unit_of_fibre_unit {u : E} (hu : ‖u‖ = 1) {Q : M} (hQ : 0 ≤ Q)
    (hQu : op Q u = 0) {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu)
    (hunit : IsUnit (rankOne u + Q)) : IsUnit (lam • rankOne u - mu • Q) := by
  apply (isUnit_map_iff (op) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective (op (lam • rankOne u - mu • Q)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : op (lam • rankOne u - mu • Q) v = 0 := hv
    have hi := congrArg (fun b : E => ⟪u,b⟫) hv0
    have hQv : ⟪u,op Q v⟫ = 0 := matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu v
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      rankOne_action,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,
      mul_one,hQv,mul_zero,sub_zero,inner_zero_right] at hi
    have huv : ⟪u,v⟫ = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt hl)
    have hzero : op Q v = 0 := by
      simp only [map_sub,map_smul,sub_apply,smul_apply,
        rankOne_action,huv,zero_smul,smul_zero,zero_sub,neg_eq_zero] at hv0
      exact (smul_eq_zero.mp hv0).resolve_left (ne_of_gt hm)
    have huop := ContinuousLinearMap.isUnit_iff_bijective.mp (hunit.map (op).toMonoidHom)
    apply huop.1
    change op (rankOne u + Q) v = op (rankOne u + Q) 0
    simp only [map_add,add_apply,rankOne_action,huv,zero_smul,hzero,add_zero,map_zero]
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩

omit [Nonempty ν] in
lemma lineRepresentative_split {u w : E} (hu : ‖u‖ = 1) {A : M} {lam : ℝ}
    (hl : 0 < lam) (he : A⁺ = lam • rankOne u) (hwu : 0 < ⟪w,u⟫) :
    lineRepresentative w A = u := by
  have hp : 0 < lam * ⟪u,w⟫ := mul_pos hl (by simpa only [real_inner_comm] using hwu)
  have hop : op A⁺ w = (lam * ⟪u,w⟫) • u := by
    rw [he,map_smul,smul_apply,rankOne_action,smul_smul]
  rw [lineRepresentative,hop,norm_smul,Real.norm_eq_abs,abs_of_pos hp,hu,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt hp),one_smul]

lemma balancedFibre_chart {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {I : Finset ι}
    {w c u : E} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫)
    (huc : u ∈ commonPositiveCone f I)
    (hch : u ∈ interior (signChamber (activeVectors f I) c)) {Q : M}
    (hQ : Q ∈ matrixFibre u) (hunit : IsUnit (rankOne u + Q)) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ purityChart f I w c := by
  have hp : (0:ℝ) < 1/2 := by norm_num
  obtain ⟨he,hn⟩ := rankOne_split_parts hQ.1 hQ.2.2 hp.le hp.le
  have hline : HasPositiveLine ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) := ⟨u,hu,1/2,hp,he⟩
  have hrep := lineRepresentative_split hu hp he hwu
  refine ⟨split_unit_of_fibre_unit hu hQ.1 hQ.2.2 hp hp hunit,hline,
    unit_rankOne_inner_nonzero hline hu hp he (ne_of_gt hwu),?_,?_,?_⟩
  · rw [hn,Matrix.trace_smul,hQ.2.1,smul_eq_mul,mul_one]; exact hp
  · rwa [hrep]
  · rwa [hrep]

end BalancedChart
end BorsukNine

end OAI
