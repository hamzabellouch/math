import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalOperator
import OAI.Geometry.PrescribedPotential.WirtingerCalculus

namespace OAI

/-! Matrix Wirtinger. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}
local instance matrixWirtingerCS (n : ℕ) : ContinuousSMul ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → Fin n → ℂ))

lemma wderiv_sum {α : Type*} (s : Finset α) {f : α → V n → ℂ} {z : V n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (a : ℂ) (v : V n) :
    wderiv a v (fun y => ∑ i ∈ s, f i y) z = ∑ i ∈ s, wderiv a v (f i) z := by
  classical
  simp only [wderiv, fderiv_fun_sum hf, _root_.sum_apply,
    Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

 
def mderiv (a : ℂ) (v : V n) (M : V n → Matrix (Fin n) (Fin n) ℂ) (z : V n) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => wderiv a v (fun y => M y i j) z

lemma entry_smooth {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (i j : Fin n) : ContDiffAt ℝ ∞ (fun y => M y i j) z :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hM i) j

lemma matrix_smooth_mul {M N : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (hN : ContDiffAt ℝ ∞ N z) :
    ContDiffAt ℝ ∞ (fun y => M y*N y) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ∞ (fun y => ∑ k, M y i k*N y k j) z
  exact ContDiffAt.sum (fun k _ => (entry_smooth hM i k).mul (entry_smooth hN k j))

lemma mderiv_add {M N : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (hN : ContDiffAt ℝ ∞ N z) (a : ℂ) (v : V n) :
    mderiv a v (fun y => M y+N y) z = mderiv a v M z+mderiv a v N z := by
  ext i j
  exact wderiv_add ((entry_smooth hM i j).differentiableAt (by simp))
    ((entry_smooth hN i j).differentiableAt (by simp)) a v

lemma mderiv_neg {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (a : ℂ) (v : V n) :
    mderiv a v (fun y => -M y) z = -mderiv a v M z := by
  ext i j
  change wderiv a v (fun y => -(M y i j)) z = -wderiv a v (fun y => M y i j) z
  have h := wderiv_const_mul ((entry_smooth hM i j).differentiableAt (by simp)) a (-1) v
  simpa only [neg_one_mul] using h

lemma mderiv_smooth {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (a : ℂ) (v : V n) :
    ContDiffAt ℝ ∞ (mderiv a v M) z := by
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    wderiv_smooth (entry_smooth hM i j) a v))

lemma mderiv_congr {M N : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (he : M =ᶠ[𝓝 z] N) (a : ℂ) (v : V n) : mderiv a v M z = mderiv a v N z := by
  ext i j
  exact wderiv_congr (he.mono (fun y hy => congrFun (congrFun hy i) j)) a v

lemma mderiv_const (C : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (v z : V n) :
    mderiv a v (fun _ => C) z = 0 := by
  ext i j
  exact wderiv_const a _ v z

lemma mderiv_mul {M N : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (hN : ContDiffAt ℝ ∞ N z) (a : ℂ) (v : V n) :
    mderiv a v (fun y => M y*N y) z = mderiv a v M z*N z+M z*mderiv a v N z := by
  ext i j
  change wderiv a v (fun y => ∑ k, M y i k*N y k j) z = _
  rw [wderiv_sum Finset.univ (fun k _ => ((entry_smooth hM i k).differentiableAt (by simp)).fun_mul
    ((entry_smooth hN k j).differentiableAt (by simp)))]
  simp only [wderiv_mul ((entry_smooth hM _ _).differentiableAt (by simp))
    ((entry_smooth hN _ _).differentiableAt (by simp)), Finset.sum_add_distrib,
    Matrix.add_apply,Matrix.mul_apply,mderiv]

lemma mderiv_mul_differentiable {M N : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : DifferentiableAt ℝ M z) (hN : DifferentiableAt ℝ N z) (a : ℂ) (v : V n) :
    mderiv a v (fun y => M y*N y) z = mderiv a v M z*N z+M z*mderiv a v N z := by
  have hm (i j : Fin n) := differentiableAt_pi.mp (differentiableAt_pi.mp hM i) j
  have hn (i j : Fin n) := differentiableAt_pi.mp (differentiableAt_pi.mp hN i) j
  ext i j
  change wderiv a v (fun y => ∑ k, M y i k*N y k j) z = _
  rw [wderiv_sum Finset.univ (fun k _ => (hm i k).fun_mul (hn k j))]
  simp only [wderiv_mul (hm _ _) (hn _ _),Finset.sum_add_distrib,
    Matrix.add_apply,Matrix.mul_apply,mderiv]

lemma mderiv_trace_differentiable {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : DifferentiableAt ℝ M z) (a : ℂ) (v : V n) :
    wderiv a v (fun y => (M y).trace) z = (mderiv a v M z).trace := by
  exact wderiv_sum Finset.univ (fun i _ =>
    differentiableAt_pi.mp (differentiableAt_pi.mp hM i) i) a v

lemma mderiv_inverse {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hn : ∀ y ∈ U, (M y).det ≠ 0) {z : V n} (hz : z ∈ U) (a : ℂ) (v : V n) :
    mderiv a v (fun y => (M y)⁻¹) z = -(M z)⁻¹*mderiv a v M z*(M z)⁻¹ := by
  have hi := (MatrixSmoothGeneral.inverse hM hn).contDiffAt (hU.mem_nhds hz)
  have hs := hM.contDiffAt (hU.mem_nhds hz)
  have he : (fun y => M y*(M y)⁻¹) =ᶠ[𝓝 z] (fun _ => 1) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hn y hy))
  have hh := mderiv_congr he a v
  rw [mderiv_mul hs hi,mderiv_const] at hh
  have hm := congrArg (fun B => (M z)⁻¹*B) hh
  rw [mul_add, ← mul_assoc (M z)⁻¹ (M z),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hn z hz)),one_mul,mul_zero] at hm
  apply eq_neg_of_add_eq_zero_right at hm
  simpa only [neg_mul, mul_assoc] using hm

lemma mderiv_trace {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (a : ℂ) (v : V n) :
    wderiv a v (fun y => (M y).trace) z = (mderiv a v M z).trace := by
  exact wderiv_sum Finset.univ (fun i _ => (entry_smooth hM i i).differentiableAt (by simp)) a v

lemma mderiv_comm {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (a b : ℂ) (u v : V n) :
    mderiv a u (mderiv b v M) z = mderiv b v (mderiv a u M) z := by
  ext i j
  exact wderiv_comm (entry_smooth hM i j) a b u v
end KaehlerCalculus

end
end

end OAI
