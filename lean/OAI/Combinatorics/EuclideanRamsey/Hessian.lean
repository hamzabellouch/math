import OAI.Combinatorics.EuclideanRamsey.SmoothingKernel

namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hessianB (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y) x

lemma hessianB_eq (f : E → ℝ) (x v w : E) :
    hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v,w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rfl

lemma hessianB_linear_comp {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (x v w : E) :
    hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by
  have hG : (fun y => fderiv ℝ (f ∘ L) y) =
      (fun y => (fderiv ℝ f (L y)).comp L) := by
    funext y
    exact ((hf.differentiable (by simp) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  have hd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have h := (((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).clm_comp
    (hasFDerivAt_const L x))
  dsimp only [Function.comp_def] at h
  unfold hessianB
  rw [hG, h.fderiv]
  simp

lemma hessianB_mul {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v w : E) :
    hessianB (fun y => f y*g y) x v w =
      f x*hessianB g x v w + g x*hessianB f x v w +
      fderiv ℝ f x v*fderiv ℝ g x w + fderiv ℝ g x v*fderiv ℝ f x w := by
  have hf' (x : E) := (hf.differentiable (by simp) x).hasFDerivAt
  have hg' (x : E) := (hg.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (fun z => f z*g z) y) =
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    funext y
    exact ((hf' y).mul (hg' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hgd : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hd := ((hf' x).smul (hgd x).hasFDerivAt).add
    ((hg' x).smul (hfd x).hasFDerivAt)
  unfold hessianB
  rw [hG]
  change ((fderiv ℝ ((f • fun y => fderiv ℝ g y) + g • fun y => fderiv ℝ f y) x) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

lemma hessianB_prod_horizontal {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E × F) (v w : E) :
    hessianB (fun x : E × F => f x.1*g x.2) x (v,0) (w,0) =
      g x.2*hessianB f x.1 v w := by
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => f x.1) := hf.comp contDiff_fst
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => g x.2) := hg.comp contDiff_snd
  rw [hessianB_mul hf1 hg2]
  rw [show (fun x : E×F => f x.1) = f ∘ ContinuousLinearMap.fst ℝ E F from rfl,
    show (fun x : E×F => g x.2) = g ∘ ContinuousLinearMap.snd ℝ E F from rfl,
    hessianB_linear_comp hf, hessianB_linear_comp hg]
  have hfg := ((hg.differentiable (by simp) x.2).hasFDerivAt.comp x
    (ContinuousLinearMap.snd ℝ E F).hasFDerivAt).fderiv
  change fderiv ℝ (_ ∘ ⇑(ContinuousLinearMap.snd ℝ E F)) x = _ at hfg
  rw [hfg]
  simp

lemma hessianB_prod_vertical {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E × F) (v w : F) :
    hessianB (fun x : E × F => f x.1*g x.2) x (0,v) (0,w) =
      f x.1*hessianB g x.2 v w := by
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => f x.1) := hf.comp contDiff_fst
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => g x.2) := hg.comp contDiff_snd
  rw [hessianB_mul hf1 hg2]
  rw [show (fun x : E×F => f x.1) = f ∘ ContinuousLinearMap.fst ℝ E F from rfl,
    show (fun x : E×F => g x.2) = g ∘ ContinuousLinearMap.snd ℝ E F from rfl,
    hessianB_linear_comp hf, hessianB_linear_comp hg]
  have hfg := ((hf.differentiable (by simp) x.1).hasFDerivAt.comp x
    (ContinuousLinearMap.fst ℝ E F).hasFDerivAt).fderiv
  change fderiv ℝ (_ ∘ ⇑(ContinuousLinearMap.fst ℝ E F)) x = _ at hfg
  rw [hfg]
  simp

lemma hessianB_continuous {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (hessianB f) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous_fderiv (by simp)

lemma hessianB_compact {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (hessianB f) := (hf.fderiv ℝ).fderiv ℝ

lemma hessianB_apply_continuous {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v w : E) : Continuous (fun x => hessianB f x v w) :=
  ((hessianB_continuous hf).clm_apply continuous_const).clm_apply continuous_const

lemma hessianB_apply_compact {f : E → ℝ} (hf : HasCompactSupport f)
    (v w : E) : HasCompactSupport (fun x => hessianB f x v w) := by
  apply (hessianB_compact hf).comp_left (g := fun B => B v w)
  simp

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

lemma bilinear_orthonormal_trace (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ E) :
    ∑ i, B (e i) (e i) = ∑ j, B (f j) (f j) := by
  classical
  have hex (x y : E) : B x y = ∑ j, ∑ l,
      (inner ℝ (f j) x * inner ℝ (f l) y) * B (f j) (f l) := by
    conv_lhs => rw [← f.sum_repr x, ← f.sum_repr y]
    simp only [map_sum, map_smul, _root_.sum_apply,
      _root_.smul_apply, OrthonormalBasis.repr_apply_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  conv_lhs => arg 2; intro i; rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hsum (l : κ) : ∑ i, inner ℝ (f j) (e i) * inner ℝ (f l) (e i) =
      if j=l then 1 else 0 := by
    simpa only [real_inner_comm (f l), f.inner_eq_ite, eq_comm] using e.sum_inner_mul_inner (f j) (f l)
  simp_rw [hsum]
  simp

end Trace

section MatrixContraction

lemma pi_basis_expansion {n : ℕ} (v : Fin n → ℝ) :
    v = ∑ j, v j • Pi.single j (1:ℝ) := by
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single v).symm

lemma bilinear_matrix_pushforward {k n : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, ∑ l, (M*D*M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by
  have hex (v w : Fin k → ℝ) : B v w = ∑ j, ∑ l,
      (v j*w l)*B (Pi.single j 1) (Pi.single l 1) := by
    conv_lhs => rw [pi_basis_expansion v, pi_basis_expansion w]
    simp only [map_sum, map_smul, _root_.sum_apply,
      _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  conv_rhs => arg 2; intro a; arg 2; intro b; rw [hex]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro b; rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

def rightInverseSplit (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E)
    (hUR : U.comp R = LinearMap.id) : E ≃ₗ[ℝ] H × LinearMap.ker U where
  toFun x := (U x, ⟨x-R (U x), by
    change U (x-R (U x)) = 0
    simp only [map_sub, show U (R (U x)) = U x from LinearMap.congr_fun hUR (U x), sub_self]⟩)
  invFun v := R v.1 + v.2
  left_inv x := by simp
  right_inv v := by
    ext
    · simp only [map_add, show U (R v.1) = v.1 from LinearMap.congr_fun hUR v.1,
        LinearMap.map_coe_ker, add_zero]
    · change R v.1 + (v.2:E) - R (U (R v.1 + v.2)) = v.2
      simp only [map_add, show U (R v.1) = v.1 from LinearMap.congr_fun hUR v.1,
        LinearMap.map_coe_ker, add_zero]
      abel
  map_add' v w := by ext <;> simp [map_add] ; abel
  map_smul' c x := by ext <;> simp [map_smul, smul_sub]

@[simp] lemma rightInverseSplit_fst (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E)
    (hUR : U.comp R = LinearMap.id) (x : E) : (rightInverseSplit U R hUR x).1 = U x := rfl

@[simp] lemma rightInverseSplit_apply_R (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E)
    (hUR : U.comp R = LinearMap.id) (y : H) : (rightInverseSplit U R hUR (R y)) = (y,0) := by
  have h : U (R y) = y := LinearMap.congr_fun hUR y
  apply Prod.ext
  · exact h
  · apply Subtype.ext
    change R y - R (U (R y)) = 0
    rw [h, sub_self]

end Split

end EuclideanRamsey

end

end OAI
