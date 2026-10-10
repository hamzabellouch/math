import Mathlib
import OAI.Analysis.AffineBernstein.PositiveMatrixTraceBound
import OAI.Analysis.AffineBernstein.DualHeightCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualDetBarrier
open Filter
open scoped Topology

def dualCutoff {n : ℕ} (u : Space n → ℝ) (h : ℝ) (x : Space n) : ℝ := dualHeight u x - h

def dualDetBarrier {n : ℕ} (u : Space n → ℝ) (h β γ : ℝ) (x : Space n) : ℝ :=
  (-1:ℝ)*logHessianDet u x + β*Real.log (dualCutoff u h x) + γ*positionEnergy x

lemma dirDeriv_dualCutoff {n : ℕ} (u : Space n → ℝ) (h : ℝ) (x : Space n) (i : Fin n) :
    dirDeriv (coordinateVector n i) (dualCutoff u h) x =
      dirDeriv (coordinateVector n i) (dualHeight u) x := by
  unfold dirDeriv dualCutoff
  rw [fderiv_sub_const]

lemma hessian_dualCutoff {n : ℕ} (u : Space n → ℝ) (h : ℝ) (x : Space n) :
    hessian (dualCutoff u h) x = hessian (dualHeight u) x := by
  have he : dualCutoff u h = fun y => dualHeight u y + (-h) := by funext y; simp [dualCutoff,sub_eq_add_neg]
  rw [he,hessian_add_constant]

lemma contDiffOn_dualCutoff {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (h : ℝ) :
    ContDiffOn ℝ ∞ (dualCutoff u h) Ω := (contDiffOn_dualHeight hΩ hu).sub contDiffOn_const

lemma inverseHessianPair_dualCutoff {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (h : ℝ) (f : Space n → ℝ) :
    inverseHessianPair u (dualCutoff u h) f x =
      ∑ k, x k * dirDeriv (coordinateVector n k) f x := by
  have he : inverseHessianPair u (dualCutoff u h) f x = inverseHessianPair u (dualHeight u) f x := by
    simp only [inverseHessianPair,dirDeriv_dualCutoff]
  rw [he,inverseHessianPair_dualHeight hu hp]

lemma inverseHessianTrace_log_function {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hneg : ∀ y ∈ Ω, f y < 0)
    {x : Space n} (hx : x ∈ Ω) :
    inverseHessianTrace u (fun y => Real.log (f y)) x =
      inverseHessianTrace u f x / f x - inverseHessianPair u f f x / (f x)^2 := by
  have he (i j : Fin n) : hessian (fun y => Real.log (f y)) x i j =
      hessian f x i j / f x -
        dirDeriv (coordinateVector n i) f x * dirDeriv (coordinateVector n j) f x / (f x)^2 :=
    second_dirDeriv_log_of_neg hΩ hf hneg hx _ _
  simp only [inverseHessianTrace,inverseHessianPair,he,mul_sub,Finset.sum_sub_distrib,
    Finset.sum_div,mul_div_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma contDiffOn_dualDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (h β γ : ℝ)
    (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) : ContDiffOn ℝ ∞ (dualDetBarrier u h β γ) Ω :=
  ((contDiffOn_const.mul (contDiffOn_logHessianDet hΩ hu hp)).add
    (contDiffOn_const.mul ((contDiffOn_dualCutoff hΩ hu h).log (fun x hx => ne_of_lt (hneg x hx))))).add
      (contDiffOn_const.mul contDiff_positionEnergy.contDiffOn)

lemma dualDetBarrier_critical_gradient {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (hp : (hessian u x).PosDef) (h β γ : ℝ) (hn : dualCutoff u h x ≠ 0)
    (hm : IsLocalMax (dualDetBarrier u h β γ) x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (logHessianDet u) x =
      (β/dualCutoff u h x)*dirDeriv (coordinateVector n i) (dualCutoff u h) x +
        γ*dirDeriv (coordinateVector n i) positionEnergy x := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hφ := (contDiffAt_logHessianDet hu' hp).differentiableAt (by simp)
  have hv := ((contDiffOn_dualCutoff hΩ hu h).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have hP := contDiff_positionEnergy.differentiable (by simp) x
  have hd := (((hφ.hasFDerivAt.const_mul (-1)).add
    ((hv.log hn).hasFDerivAt.const_mul β)).add (hP.hasFDerivAt.const_mul γ)).fderiv
  have hz : dirDeriv (coordinateVector n i) (dualDetBarrier u h β γ) x = 0 := by
    simp only [dirDeriv,hm.fderiv_eq_zero,zero_apply]
  change (fderiv ℝ (fun y => (-1:ℝ)*logHessianDet u y + β*Real.log (dualCutoff u h y) +
    γ*positionEnergy y) x) (coordinateVector n i) = 0 at hz
  change fderiv ℝ (fun y => (-1:ℝ)*logHessianDet u y + β*Real.log (dualCutoff u h y) +
    γ*positionEnergy y) x = _ at hd
  rw [hd] at hz
  simp only [add_apply,smul_apply,smul_eq_mul] at hz
  change (-1:ℝ)*dirDeriv _ (logHessianDet u) x +
    β*dirDeriv _ (fun y => Real.log (dualCutoff u h y)) x + γ*dirDeriv _ positionEnergy x = 0 at hz
  rw [dirDeriv_real_log hv hn] at hz
  linear_combination (norm := ring_nf) -hz

lemma inverseHessianTrace_dualDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω) (β γ : ℝ) :
    inverseHessianTrace u (dualDetBarrier u h β γ) x =
      -(((n:ℝ)+1)/((n:ℝ)+2))*inverseHessianPair u (logHessianDet u) (logHessianDet u) x +
      β*(((n:ℝ) + ∑ k, x k * dirDeriv (coordinateVector n k) (logHessianDet u) x)/dualCutoff u h x -
        inverseHessianPair u (dualCutoff u h) (dualCutoff u h) x/(dualCutoff u h x)^2) +
      γ*(hessian u x)⁻¹.trace := by
  have hφ := contDiffOn_logHessianDet hΩ hu hp
  have hl := (contDiffOn_dualCutoff hΩ hu h).log (fun x hx => ne_of_lt (hneg x hx))
  unfold dualDetBarrier
  rw [inverseHessianTrace_add hΩ ((contDiffOn_const.mul hφ).add (contDiffOn_const.mul hl))
      (contDiffOn_const.mul contDiff_positionEnergy.contDiffOn) hx,
    inverseHessianTrace_add hΩ (contDiffOn_const.mul hφ) (contDiffOn_const.mul hl) hx,
    inverseHessianTrace_const_mul hΩ hφ hx,inverseHessianTrace_const_mul hΩ hl hx,
    inverseHessianTrace_const_mul hΩ contDiff_positionEnergy.contDiffOn hx,
    affineMaximal_logHessianDet_equation hΩ hu hp hm hx,
    inverseHessianTrace_log_function hΩ (contDiffOn_dualCutoff hΩ hu h) hneg hx,
    inverseHessianTrace_positionEnergy]
  have he : inverseHessianTrace u (dualCutoff u h) x = inverseHessianTrace u (dualHeight u) x := by
    simp only [inverseHessianTrace,hessian_dualCutoff]
  rw [he,inverseHessianTrace_dualHeight hΩ hu hx (hp x hx)]
  ring

lemma inverseHessianPair_position_le_trace {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) :
    inverseHessianPair u positionEnergy positionEnergy x ≤ (hessian u x)⁻¹.trace * positionSquared x := by
  have he : inverseHessianPair u positionEnergy positionEnergy x =
      (fun i => x i) ⬝ᵥ (hessian u x)⁻¹.mulVec (fun i => x i) := by
    simp only [inverseHessianPair,dirDeriv_positionEnergy,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact posSemidef_quadratic_le_trace_mul_sq hp.posSemidef.inv _

/-- Exact pulled-back dual equation at a critical point. The Q term cancels
for β=n+2, retaining the original (n+1)/(n+2) exponent. -/
lemma dualDetBarrier_peak_identity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω) (γ : ℝ)
    (hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) x) :
    inverseHessianTrace u (dualDetBarrier u h ((n:ℝ)+2) γ) x =
      γ*(hessian u x)⁻¹.trace - (((n:ℝ)+1)/((n:ℝ)+2))*γ^2 *
        inverseHessianPair u positionEnergy positionEnergy x +
      ((n:ℝ)*((n:ℝ)+2) - γ*(n:ℝ)*positionSquared x)/dualCutoff u h x := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hn : dualCutoff u h x ≠ 0 := ne_of_lt (hneg x hx)
  have hcrit := dualDetBarrier_critical_gradient hΩ hu hx (hp x hx) h ((n:ℝ)+2) γ hn hmax
  have hpair := inverseHessianPair_grad_linear (hp x hx) (((n:ℝ)+2)/dualCutoff u h x) γ hcrit
  have hcross : inverseHessianPair u positionEnergy (dualCutoff u h) x = positionSquared x := by
    rw [inverseHessianPair_symm (hp x hx),inverseHessianPair_dualCutoff hu' (hp x hx)]
    simp only [dirDeriv_positionEnergy,positionSquared,pow_two]
  rw [hcross] at hpair
  have hrad : (∑ k, x k * dirDeriv (coordinateVector n k) (logHessianDet u) x) =
      (((n:ℝ)+2)/dualCutoff u h x)*inverseHessianPair u (dualCutoff u h) (dualCutoff u h) x +
        γ*positionSquared x := by
    rw [inverseHessianPair_dualCutoff hu' (hp x hx)]
    simp only [hcrit,Finset.mul_sum,← Finset.sum_add_distrib,positionSquared,dirDeriv_positionEnergy,pow_two]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [inverseHessianTrace_dualDetBarrier hΩ hu hp hm h hneg hx,hpair,hrad]
  have hd : (n:ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

end DualDetBarrier


end
end AffineBernstein
end

end OAI
