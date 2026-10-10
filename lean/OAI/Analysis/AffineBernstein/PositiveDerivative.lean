import Mathlib
import OAI.Analysis.AffineBernstein.CapCovariance

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem contDiffAt_gradient {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e) :
    ContDiffAt ℝ ∞ (gradient H) e :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
    e (hh.fderiv_right (by simp))

theorem inner_fderiv_gradient {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e)
    (v w : E) : inner ℝ (fderiv ℝ (gradient H) e v) w =
      fderiv ℝ (fderiv ℝ H) e v w := by
  have hd := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt.comp
    e ((hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  change inner ℝ (fderiv ℝ (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ H x)) e v) w = _
  change HasFDerivAt (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ H x)) _ e at hd
  rw [hd.fderiv]
  simp

end
section PositiveDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive-definiteness of the derivative makes a map injective on a convex
set, by strict monotonicity along every segment. -/
lemma injOn_of_positive_derivative {S : Set E} (hS : Convex ℝ S) {G : E → E}
    (hG : ∀ x ∈ S, DifferentiableAt ℝ G x)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < inner ℝ (fderiv ℝ G x v) v) :
    Set.InjOn G S := by
  intro x hx y hy he
  by_contra hxy
  let v := y-x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  let γ := fun t : ℝ => x+t • v
  let f := fun t : ℝ => inner ℝ (G (γ t)) v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const v).const_add x
  have hγS (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : γ t ∈ S :=
    hS.add_smul_sub_mem hx hy ht
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt f (inner ℝ (fderiv ℝ G (γ t) v) v) t := by
    simpa [f] using ((hG (γ t) (hγS t ht)).hasFDerivAt.comp_hasDerivAt t (hγ t)).inner ℝ
      (hasDerivAt_const t v)
  have hmono : StrictMonoOn f (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · intro t ht
      exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hf t ht').deriv]
      exact hpos (γ t) (hγS t ht') v hv
  have hh := hmono (show (0:ℝ) ∈ Icc 0 1 by norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0:ℝ)<1)
  have h0 : f 0 = inner ℝ (G x) v := by simp [f,γ]
  have h1 : f 1 = inner ℝ (G y) v := by simp [f,γ,v]
  rw [h0,h1,he] at hh
  exact lt_irrefl _ hh
end PositiveDerivative

/-- The actual gradient of a strictly positive-Hessian function is injective;
in particular this applies to every principal-coordinate slice in the source. -/
lemma gradient_injOn_of_hessian_posDef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) :
    Set.InjOn (gradient u) Ω := by
  apply injOn_of_positive_derivative hcv
  · intro x hx
    exact (contDiffAt_gradient (hu.contDiffAt (hΩ.mem_nhds hx))).differentiableAt (by simp)
  · intro x hx v hv
    rw [inner_fderiv_gradient (hu.contDiffAt (hΩ.mem_nhds hx))]
    exact second_fderiv_pos (hu.contDiffAt (hΩ.mem_nhds hx)) (hp x hx) hv

/-- The true Euclidean gradient has Jacobian determinant equal to the
coordinate Hessian determinant, including dimension zero. -/
lemma det_fderiv_gradient_eq_hessian {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    (fderiv ℝ (gradient u) x).det = (hessian u x).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he : LinearMap.toMatrix b b (fderiv ℝ (gradient u) x).toLinearMap =
      (hessian u x).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change (OrthonormalBasis.repr (EuclideanSpace.basisFun (Fin n) ℝ)
      (fderiv ℝ (gradient u) x ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i = _
    rw [OrthonormalBasis.repr_apply_apply,real_inner_comm,
      inner_fderiv_gradient hu,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_apply]
    exact (hessian_eq_second hu j i).symm
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,he,Matrix.det_transpose]

/-- Exact change of variables for the convex gradient map. This is the
principal-minor argument used in bounds.tex; applying this result on each
coordinate slice gives the claimed integral bound for that minor. -/
lemma integral_hessian_det_eq_gradient_volume {n : ℕ}
    {μ : Measure (Space n)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKO : K ⊆ Ω) :
    (∫ x in K, (hessian u x).det ∂μ) = μ.real (gradient u '' K) := by
  have hd (x : Space n) (hx : x ∈ K) :=
    (contDiffAt_gradient (hu.contDiffAt (hΩ.mem_nhds (hKO hx)))).differentiableAt (by simp)
  have hj := integral_image_eq_integral_abs_det_fderiv_smul μ hK
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt)
    ((gradient_injOn_of_hessian_posDef hΩ hcv hu hp).mono hKO) (fun _ : Space n => (1:ℝ))
  rw [setIntegral_const,smul_eq_mul,mul_one] at hj
  rw [hj]
  apply setIntegral_congr_fun hK
  intro x hx
  change (hessian u x).det = |(fderiv ℝ (gradient u) x).det| * 1
  rw [det_fderiv_gradient_eq_hessian (hu.contDiffAt (hΩ.mem_nhds (hKO hx))),
    abs_of_pos (hp x (hKO hx)).det_pos]
  simp

/-- A uniformly bounded gradient image gives a uniformly bounded Hessian
Jacobian integral. No bound on the Hessian itself is needed. -/
lemma integral_hessian_det_le_image_bound {n : ℕ}
    {μ : Measure (Space n)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {K B : Set (Space n)} (hK : MeasurableSet K) (hKO : K ⊆ Ω)
    (hB : μ B ≠ ⊤) (hbound : ∀ x ∈ K, gradient u x ∈ B) :
    (∫ x in K, (hessian u x).det ∂μ) ≤ μ.real B := by
  rw [integral_hessian_det_eq_gradient_volume hΩ hcv hu hp hK hKO]
  exact measureReal_mono (by rintro _ ⟨x,hx,rfl⟩; exact hbound x hx) hB

end AffineBernstein

end

end OAI
