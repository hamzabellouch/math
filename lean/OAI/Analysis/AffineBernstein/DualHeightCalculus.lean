import Mathlib
import OAI.Analysis.AffineBernstein.LogBarrierCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualHeightCalculus
open Filter
open scoped Topology

/-- Legendre tangent height pulled back by the actual gradient. No global
Legendre transform or assumed dual regularity is needed for these identities. -/
def dualHeight {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ := tangentHeight u x 0

def positionEnergy {n : ℕ} (x : Space n) : ℝ := (1/2:ℝ) * ∑ k, (x k)^2

def positionSquared {n : ℕ} (x : Space n) : ℝ := ∑ k, (x k)^2

lemma dualHeight_expansion {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    dualHeight u x = (∑ k, x k * dirDeriv (coordinateVector n k) u x) + u 0 - u x := by
  simp only [dualHeight,tangentHeight,zero_sub,map_neg,sub_neg_eq_add]
  rw [clm_coordinate_sum]
  simp only [dirDeriv]
  ring

lemma contDiffOn_dualHeight {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) : ContDiffOn ℝ ∞ (dualHeight u) Ω := by
  have he : dualHeight u = fun x => (∑ k, x k * dirDeriv (coordinateVector n k) u x) + u 0 - u x :=
    funext (dualHeight_expansion u)
  rw [he]
  exact ((ContDiffOn.sum fun k _ => (coordinateProjection n k).contDiff.contDiffOn.mul
    (contDiffOn_dirDeriv hΩ hu _)).add contDiffOn_const).sub hu

lemma dirDeriv_coordinate {n : ℕ} (i k : Fin n) (x : Space n) :
    dirDeriv (coordinateVector n i) (fun y : Space n => y k) x = if i=k then 1 else 0 := by
  change (fderiv ℝ (coordinateProjection n k) x) _ = _
  rw [ContinuousLinearMap.fderiv]
  simp [coordinateVector,eq_comm]

lemma dirDeriv_dualHeight {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (dualHeight u) x =
      ∑ k, x k * hessian u x i k := by
  have he : dualHeight u = fun y => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0 - u y :=
    funext (dualHeight_expansion u)
  rw [he]
  have hk (k : Fin n) := (contDiffAt_dirDeriv hu (coordinateVector n k)).differentiableAt (by simp)
  have hd := hu.differentiableAt (by simp)
  have hc (k : Fin n) : DifferentiableAt ℝ (fun y : Space n => y k) x := (coordinateProjection n k).differentiableAt
  have hs : DifferentiableAt ℝ (fun y : Space n => ∑ k, y k * dirDeriv (coordinateVector n k) u y) x :=
    DifferentiableAt.fun_sum (u := Finset.univ) fun k _ => (hc k).mul (hk k)
  rw [dirDeriv_sub (hs.add_const _) hd]
  have ha : dirDeriv (coordinateVector n i)
      (fun y : Space n => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0) x =
      dirDeriv (coordinateVector n i) (fun y => ∑ k, y k * dirDeriv (coordinateVector n k) u y) x := by
    unfold dirDeriv
    rw [fderiv_add_const]
  rw [ha,dirDeriv_sum (fun (k : Fin n) (y : Space n) => y k * dirDeriv (coordinateVector n k) u y)
    (fun k => (coordinateProjection n k).differentiableAt.mul (hk k))]
  have hterm (k : Fin n) :
      dirDeriv (coordinateVector n i) (fun y : Space n => y k * dirDeriv (coordinateVector n k) u y) x =
        (if i=k then 1 else 0) * dirDeriv (coordinateVector n k) u x + x k * hessian u x i k := by
    rw [dirDeriv_mul (hc k) (hk k),dirDeriv_coordinate]
    rfl
  simp only [hterm,Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq]

lemma contDiff_positionEnergy {n : ℕ} : ContDiff ℝ ∞ (@positionEnergy n) :=
  contDiff_const.mul (ContDiff.sum fun k _ => (coordinateProjection n k).contDiff.pow 2)

lemma dirDeriv_positionEnergy {n : ℕ} (x : Space n) (i : Fin n) :
    dirDeriv (coordinateVector n i) positionEnergy x = x i := by
  change dirDeriv _ (fun y : Space n => (1/2:ℝ)*∑ k, (y k)^2) x = _
  have hs : ContDiffAt ℝ ∞ (fun y : Space n => ∑ k, (y k)^2) x :=
    ContDiffAt.sum fun k _ => (coordinateProjection n k).contDiff.contDiffAt.pow 2
  rw [dirDeriv_const_mul (hs.differentiableAt (by simp)),
    dirDeriv_sum (fun (k : Fin n) (y : Space n) => (y k)^2)
      (fun k => (coordinateProjection n k).differentiableAt.pow 2)]
  have hc (k : Fin n) : DifferentiableAt ℝ (fun y : Space n => y k) x := (coordinateProjection n k).differentiableAt
  have ht (k : Fin n) : dirDeriv (coordinateVector n i) (fun y : Space n => (y k)^2) x =
      2*x k*(if i=k then 1 else 0) := by
    simp only [pow_two]
    rw [dirDeriv_mul (hc k) (hc k),dirDeriv_coordinate]
    ring
  simp only [ht]
  simp [mul_ite,Finset.sum_ite_eq]

lemma hessian_positionEnergy {n : ℕ} (x : Space n) : hessian positionEnergy x = 1 := by
  ext i j
  change dirDeriv _ (dirDeriv _ positionEnergy) x = _
  rw [show dirDeriv (coordinateVector n j) positionEnergy = (fun y : Space n => y j) from
    funext (fun y => dirDeriv_positionEnergy y j),dirDeriv_coordinate]
  rfl

lemma inverseHessianTrace_positionEnergy {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    inverseHessianTrace u positionEnergy x = (hessian u x)⁻¹.trace := by
  simp [inverseHessianTrace,hessian_positionEnergy,Matrix.one_apply,Matrix.trace,Matrix.diag_apply]

lemma inverseHessianPair_dualHeight {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (f : Space n → ℝ) :
    inverseHessianPair u (dualHeight u) f x =
      ∑ k, x k * dirDeriv (coordinateVector n k) f x := by
  unfold inverseHessianPair
  simp_rw [dirDeriv_dualHeight hu]
  have hs := Matrix.isHermitian_iff_isSymm.mp hp.isHermitian
  have he (i : Fin n) : (∑ k, x k * hessian u x i k) = ∑ k, x k * hessian u x k i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hs.apply k i]
  simp only [he]
  exact inverse_radial_contraction hp _ _

lemma inverseHessianTrace_dualHeight {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (dualHeight u) x = (n:ℝ) +
      ∑ k, x k * dirDeriv (coordinateVector n k) (logHessianDet u) x := by
  have hk (k : Fin n) := contDiffOn_dirDeriv hΩ hu (coordinateVector n k)
  have hc (k : Fin n) : ContDiffOn ℝ ∞ (fun y : Space n => y k) Ω :=
    (coordinateProjection n k).contDiff.contDiffOn
  have he : dualHeight u = fun y => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0 - u y :=
    funext (dualHeight_expansion u)
  rw [he]
  have hsum : ContDiffOn ℝ ∞ (fun y : Space n => ∑ k, y k * dirDeriv (coordinateVector n k) u y) Ω :=
    ContDiffOn.sum (fun k _ => (hc k).mul (hk k))
  have hm (i j : Fin n) : hessian (fun y => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0 - u y) x i j =
      (∑ k, hessian (fun y => y k * dirDeriv (coordinateVector n k) u y) x i j) - hessian u x i j := by
    rw [hessian_sub_on hΩ (hsum.add contDiffOn_const) hu hx,hessian_add_constant]
    simp only [Matrix.sub_apply,hessian_sum_on hΩ (fun k => (hc k).mul (hk k)) hx]
  change (∑ i, ∑ j, (hessian u x)⁻¹ i j * _) = _
  simp only [hm,mul_sub,Finset.sum_sub_distrib]
  have ht (k : Fin n) : (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      hessian (fun y => y k * dirDeriv (coordinateVector n k) u y) x i j) =
        x k * dirDeriv (coordinateVector n k) (logHessianDet u) x + 2 := by
    rw [hessian_product_trace hΩ (hc k) (hk k) hx (inverseHessian_isSymm hp)]
    change dirDeriv (coordinateVector n k) u x * inverseHessianTrace u (fun y => y k) x +
      x k * inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x +
      2 * inverseHessianPair u (fun y => y k) (dirDeriv (coordinateVector n k) u) x = _
    rw [inverseHessianTrace_dirDeriv hΩ hu hx hp]
    have hz : inverseHessianTrace u (fun y => y k) x = 0 := by
      simp [inverseHessianTrace,hessian_coordinate]
    have hq : inverseHessianPair u (fun y => y k) (dirDeriv (coordinateVector n k) u) x = 1 := by
      unfold inverseHessianPair
      simp only [dirDeriv_coordinate]
      simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      change (∑ j, (hessian u x)⁻¹ k j * hessian u x j k) = 1
      have HH := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k k)
        (Matrix.nonsing_inv_mul (hessian u x) (isUnit_iff_ne_zero.mpr (ne_of_gt hp.det_pos)))
      simpa only [Matrix.mul_apply,Matrix.one_apply_eq] using HH
    rw [hz,hq]
    ring
  have hex : (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      ∑ k, hessian (fun y => y k * dirDeriv (coordinateVector n k) u y) x i j) =
      ∑ k, (x k * dirDeriv (coordinateVector n k) (logHessianDet u) x + 2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm,ht]
  rw [hex]
  change (∑ k, (_+2)) - inverseHessianTrace u u x = _
  rw [inverseHessianTrace_self hp,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end DualHeightCalculus


end
end AffineBernstein
end

end OAI
