import Mathlib
import OAI.Analysis.AffineBernstein.EntireAndDoubling
import OAI.Analysis.AffineBernstein.LocalMaximumSecond

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LocalMaximumHessian
open Filter
open scoped Topology MatrixOrder

lemma deriv_affineLine_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (x v : E) (t : ℝ) (hf : DifferentiableAt ℝ f (x+t • v)) :
    deriv (fun s : ℝ => f (x+s • v)) t = dirDeriv v f (x+t • v) := by
  have hd : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1 <;> simp
    rfl
  exact (hf.hasFDerivAt.comp_hasDerivAt t hd).deriv

lemma localMax_second_fderiv_nonpos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hm : IsLocalMax f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let α : ℝ → E := fun t => x+t • v
  have hα : ContDiff ℝ ∞ α := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hα0 : α 0 = x := by simp [α]
  have hc : ContDiffAt ℝ ∞ (fun t => f (α t)) 0 := by
    exact (hα0 ▸ hf).comp 0 hα.contDiffAt
  have hl : IsLocalMax (fun t => f (α t)) 0 := by
    apply IsLocalMax.comp_continuous (g := α) (hα0 ▸ hm) hα.continuous.continuousAt
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have hn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (h1.eventually (by simp)).mono (fun y hy => hy.differentiableAt (by simp))
  have hnl : Tendsto α (𝓝 0) (𝓝 x) := hα0 ▸ hα.continuous.continuousAt
  have he : deriv (fun t => f (α t)) =ᶠ[𝓝 0] (fun t => dirDeriv v f (α t)) := by
    filter_upwards [hnl.eventually hn] with t ht
    exact deriv_affineLine_comp x v t ht
  have h2 := localMax_second_deriv_nonpos (hc.of_le (by decide)) hl
  rw [he.deriv_eq] at h2
  have hd := deriv_affineLine_comp (f := dirDeriv v f) x v 0
    (by simpa only [zero_smul,add_zero] using
      (contDiffAt_dirDeriv hf v).differentiableAt (by simp))
  simp only [zero_smul,add_zero] at hd
  have hh : dirDeriv v (dirDeriv v f) x = fderiv ℝ (fderiv ℝ f) x v v :=
    dirDeriv_eq_second hf v v
  change deriv (fun t : ℝ => dirDeriv v f (x+t • v)) 0 ≤ 0 at h2
  rwa [hd,hh] at h2

lemma hessian_neg_posSemidef_of_localMax {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ ∞ f x) (hm : IsLocalMax f x) : (- hessian f x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.isHermitian_iff_isSymm.mpr (hessian_isSymm hf)).neg
  intro p
  let v : Space n := (WithLp.equiv 2 (Fin n → ℝ)).symm p
  have hn := localMax_second_fderiv_nonpos hf hm v
  rw [second_fderiv_eq_sum hf] at hn
  simpa [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,v] using neg_nonneg.mpr hn

lemma trace_mul_posSemidef_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let S := CFC.sqrt A
  have hS : Matrix.conjTranspose S = S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : S*S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have hh := (hB.mul_mul_conjTranspose_same S).trace_nonneg
  rw [hS,Matrix.trace_mul_cycle,hSS] at hh
  exact hh

/-- A local maximum of a smooth test has nonpositive actual linearized
Monge--Ampère trace at every positive Hessian point. -/
lemma inverseHessianTrace_nonpos_of_localMax {n : ℕ} {u f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ ∞ f x) (hp : (hessian u x).PosDef) (hm : IsLocalMax f x) :
    inverseHessianTrace u f x ≤ 0 := by
  have hh := trace_mul_posSemidef_nonneg hp.posSemidef.inv (hessian_neg_posSemidef_of_localMax hf hm)
  have hs := hessian_isSymm hf
  have he : ((hessian u x)⁻¹ * (-hessian f x)).trace = - inverseHessianTrace u f x := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.neg_apply,
      mul_neg,Finset.sum_neg_distrib,inverseHessianTrace]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs.apply i j]
  rw [he] at hh
  linarith

end LocalMaximumHessian


end
end AffineBernstein
end

end OAI
