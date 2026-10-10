import Mathlib
import OAI.Analysis.AffineBernstein.LogDetGradientEnergy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogBarrierCalculus
open Filter
open scoped Topology

lemma dirDeriv_real_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hne : f x ≠ 0) (v : E) :
    dirDeriv v (fun y => Real.log (f y)) x = dirDeriv v f x / f x := by
  unfold dirDeriv
  rw [(hf.hasFDerivAt.log hne).fderiv]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

lemma second_dirDeriv_log_of_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (hneg : ∀ y ∈ Ω, f y < 0) {x : E} (hx : x ∈ Ω) (v w : E) :
    dirDeriv v (dirDeriv w (fun y => Real.log (f y))) x =
      dirDeriv v (dirDeriv w f) x / f x - dirDeriv v f x * dirDeriv w f x / (f x)^2 := by
  have hn : f x ≠ 0 := ne_of_lt (hneg x hx)
  have hfn : ContDiffOn ℝ ∞ (fun y => -1 * f y) Ω := contDiffOn_const.mul hf
  have hpn : ∀ y ∈ Ω, 0 < (-1:ℝ)*f y := by intro y hy; nlinarith [hneg y hy]
  have he : (fun y => Real.log ((-1:ℝ)*f y)) = (fun y => Real.log (f y)) := by
    funext y
    simp only [neg_one_mul,Real.log_neg_eq_log]
  have hh := log_second_identity hΩ hfn hpn hx v w
  rw [he,second_dirDeriv_const_mul hΩ hf hx,
    dirDeriv_real_log ((hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) hn,
    dirDeriv_real_log ((hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) hn] at hh
  linear_combination (norm := (field_simp [hn]; ring_nf)) ((f x)⁻¹) * hh

lemma inverseHessianTrace_self {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) : inverseHessianTrace u u x = n := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hp.isHermitian
  have hh := matrix_inverse_contraction_self (ne_of_gt hp.det_pos)
  rw [Finset.sum_comm] at hh
  simpa only [inverseHessianTrace,hs.apply,Fintype.card_fin] using hh

lemma inverseHessianTrace_add {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u f g : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {x : Space n} (hx : x ∈ Ω) :
    inverseHessianTrace u (fun y => f y + g y) x =
      inverseHessianTrace u f x + inverseHessianTrace u g x := by
  simp only [inverseHessianTrace,hessian_add_on hΩ hf hg hx,Matrix.add_apply,
    mul_add,Finset.sum_add_distrib]

lemma inverseHessianTrace_const_mul {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) {x : Space n} (hx : x ∈ Ω) (c : ℝ) :
    inverseHessianTrace u (fun y => c * f y) x = c * inverseHessianTrace u f x := by
  simp only [inverseHessianTrace,hessian_const_mul hΩ hf c hx,Matrix.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma inverseHessianTrace_log {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hneg : ∀ y ∈ Ω, u y < 0)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (fun y => Real.log (u y)) x =
      (n:ℝ) / u x - inverseHessianPair u u u x / (u x)^2 := by
  have he (i j : Fin n) : hessian (fun y => Real.log (u y)) x i j =
      hessian u x i j / u x -
        dirDeriv (coordinateVector n i) u x * dirDeriv (coordinateVector n j) u x / (u x)^2 :=
    second_dirDeriv_log_of_neg hΩ hu hneg hx _ _
  have hh : inverseHessianTrace u (fun y => Real.log (u y)) x =
      inverseHessianTrace u u x / u x - inverseHessianPair u u u x / (u x)^2 := by
    simp only [inverseHessianTrace,inverseHessianPair,he,mul_sub,Finset.sum_sub_distrib,
      Finset.sum_div,mul_div_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hh,inverseHessianTrace_self hp]

lemma inverseHessianPair_symm {n : ℕ} {u f g : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) : inverseHessianPair u f g x = inverseHessianPair u g f x := by
  unfold inverseHessianPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [(inverseHessian_isSymm hp).apply i j]
  ring

lemma inverseHessianPair_self_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (f : Space n → ℝ) : 0 ≤ inverseHessianPair u f f x := by
  have hh := inverseMatrixPair_self_nonneg hp (fun i => dirDeriv (coordinateVector n i) f x)
  unfold inverseHessianPair inverseMatrixPair at *
  rw [Finset.sum_comm] at hh
  simpa only [mul_right_comm] using hh

/-- Literal log-determinant barrier. On a negative section its logarithmic
cutoff is exactly `log (-u)`, because the real logarithm uses absolute value. -/
def affineDetBarrier {n : ℕ} (u : Space n → ℝ) (β γ : ℝ) (x : Space n) : ℝ :=
  logHessianDet u x + β * Real.log (u x) + γ * gradientEnergy u x

lemma contDiffOn_affineDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hneg : ∀ x ∈ Ω, u x < 0) (β γ : ℝ) :
    ContDiffOn ℝ ∞ (affineDetBarrier u β γ) Ω :=
  ((contDiffOn_logHessianDet hΩ hu hp).add
    (contDiffOn_const.mul (hu.log (fun x hx => ne_of_lt (hneg x hx))))).add
      (contDiffOn_const.mul (contDiffOn_gradientEnergy hΩ hu))

lemma dirDeriv_affineDetBarrier {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (i : Fin n) :
    dirDeriv (coordinateVector n i) (affineDetBarrier u β γ) x =
      dirDeriv (coordinateVector n i) (logHessianDet u) x +
        β * dirDeriv (coordinateVector n i) u x / u x +
        γ * dirDeriv (coordinateVector n i) (gradientEnergy u) x := by
  have hd := hu.differentiableAt (by simp)
  have hφ := (contDiffAt_logHessianDet hu hp).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (gradientEnergy u) x :=
    (contDiffAt_const.mul (ContDiffAt.sum fun k _ => (contDiffAt_dirDeriv hu _).pow 2)).differentiableAt (by simp)
  have hh := ((hφ.hasFDerivAt.add ((hd.log hn).hasFDerivAt.const_mul β)).add
    (hG.hasFDerivAt.const_mul γ)).fderiv
  change (fderiv ℝ (fun y => logHessianDet u y + β * Real.log (u y) + γ * gradientEnergy u y) x) _ = _
  change (fderiv ℝ (fun y => logHessianDet u y + β * Real.log (u y) + γ * gradientEnergy u y) x) = _ at hh
  rw [hh]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change dirDeriv _ (logHessianDet u) x + β * dirDeriv _ (fun y => Real.log (u y)) x + _ = _
  rw [dirDeriv_real_log hd hn]
  simp only [dirDeriv]
  ring

lemma inverseHessianTrace_affineDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω) (β γ : ℝ) :
    inverseHessianTrace u (affineDetBarrier u β γ) x =
      (((n:ℝ)+1)/((n:ℝ)+2)) * inverseHessianPair u (logHessianDet u) (logHessianDet u) x +
      β * ((n:ℝ)/u x - inverseHessianPair u u u x / (u x)^2) +
      γ * ((hessian u x).trace + ∑ k, dirDeriv (coordinateVector n k) u x *
        dirDeriv (coordinateVector n k) (logHessianDet u) x) := by
  have hφ := contDiffOn_logHessianDet hΩ hu hp
  have hl := hu.log (fun y hy => ne_of_lt (hneg y hy))
  have hG := contDiffOn_gradientEnergy hΩ hu
  unfold affineDetBarrier
  rw [inverseHessianTrace_add hΩ (hφ.add (contDiffOn_const.mul hl)) (contDiffOn_const.mul hG) hx,
    inverseHessianTrace_add hΩ hφ (contDiffOn_const.mul hl) hx,
    inverseHessianTrace_const_mul hΩ hl hx, inverseHessianTrace_const_mul hΩ hG hx,
    affineMaximal_logHessianDet_equation hΩ hu hp hm hx,
    inverseHessianTrace_log hΩ hu hneg hx (hp x hx),
    inverseHessianTrace_gradientEnergy hΩ hu hx (hp x hx)]

end LogBarrierCalculus


end
end AffineBernstein
end

end OAI
