import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalJet : List E → (E → F) → E → F
  | [], f => f
  | v :: l, f => fun x => fderiv ℝ (directionalJet l f) x v

@[simp] theorem directionalJet_nil (f : E → F) : directionalJet [] f = f := rfl
@[simp] theorem directionalJet_cons (v : E) (l : List E) (f : E → F) :
    directionalJet (v :: l) f = fun x => fderiv ℝ (directionalJet l f) x v := rfl

lemma contDiff_directionalJet {f : E → F} (hf : ContDiff ℝ ∞ f) (l : List E) :
    ContDiff ℝ ∞ (directionalJet l f) := by
  induction l with
  | nil => exact hf
  | cons v l ih =>
    exact (ih.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const

lemma directionalJet_swap {f : E → F} (hf : ContDiff ℝ ∞ f)
    (a b : E) (l : List E) :
    directionalJet (a :: b :: l) f = directionalJet (b :: a :: l) f := by
  have hg := contDiff_directionalJet hf l
  have hgd := hg.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  ext x
  have ha := fderiv_clm_apply (hgd.differentiable (by simp) x) (differentiableAt_const (c := b))
  have hb := fderiv_clm_apply (hgd.differentiable (by simp) x) (differentiableAt_const (c := a))
  simp only [directionalJet_cons, ha, hb, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  simpa using (hg.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))) a b

lemma directionalJet_perm {f : E → F} (hf : ContDiff ℝ ∞ f)
    {l₁ l₂ : List E} (h : l₁.Perm l₂) : directionalJet l₁ f = directionalJet l₂ f := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [directionalJet_cons, ih]
  | swap a b l => exact directionalJet_swap hf b a l
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma iteratedFDeriv_eq_directionalJet {f : E → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → E) (x : E) :
    iteratedFDeriv ℝ n f x v = directionalJet (List.ofFn v) f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hd := hf.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x
    rw [hd.iteratedFDeriv_succ_apply_left', List.ofFn_succ, directionalJet_cons]
    congr 2
    funext y
    exact ih (Fin.tail v) y

theorem smooth_iteratedFDeriv_comp_perm {f : E → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) (x : E) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  rw [iteratedFDeriv_eq_directionalJet hf, iteratedFDeriv_eq_directionalJet hf,
    directionalJet_perm hf (σ.ofFn_comp_perm v)]

def finiteTaylorFunction (f : E → F) (N : ℕ) (x : E) : F :=
  ∑ j ∈ Finset.range N, (j.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ j f 0 (fun _ => x)

lemma contDiff_finiteTaylorFunction (f : E → F) (N : ℕ) :
    ContDiff ℝ ∞ (finiteTaylorFunction f N) := by
  apply ContDiff.sum
  intro j _
  exact ((iteratedFDeriv ℝ j f 0).contDiff.comp
    (contDiff_pi.mpr fun _ => contDiff_id)).const_smul _

theorem iteratedFDeriv_finiteTaylorFunction [CompleteSpace F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (N k : ℕ) (hk : k < N) :
    iteratedFDeriv ℝ k (finiteTaylorFunction f N) 0 = iteratedFDeriv ℝ k f 0 := by
  classical
  let p : FormalMultilinearSeries ℝ E F := fun j => if j < N then
    (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f 0 else 0
  have hp : HasFiniteFPowerSeriesOnBall (finiteTaylorFunction f N) p 0 N ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk'
    · intro j hj
      simp [p, not_lt.mpr hj]
    · simp
    · intro y _
      simp only [finiteTaylorFunction, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      simp [p, Finset.mem_range.mp hj]
  ext v
  rw [hp.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
  have heq (σ : Equiv.Perm (Fin k)) : p k (fun i => v (σ i)) =
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 v := by
    simp only [p, ite_eq_left hk, smul_apply]
    rw [show (fun i => v (σ i)) = v ∘ σ from rfl,
      smooth_iteratedFDeriv_comp_perm hf]
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero k

theorem finiteTaylorFunction_remainder_jet [CompleteSpace F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (N k : ℕ) (hk : k < N) :
    iteratedFDeriv ℝ k (fun x => f x - finiteTaylorFunction f N x) 0 = 0 := by
  have hle : (k : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  change iteratedFDeriv ℝ k (f - finiteTaylorFunction f N) 0 = 0
  rw [iteratedFDeriv_sub_apply (hf.of_le hle).contDiffAt
    ((contDiff_finiteTaylorFunction f N).of_le hle).contDiffAt,
    iteratedFDeriv_finiteTaylorFunction hf N k hk, sub_self]


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

open MvPolynomial
variable {σ : Type*}

def realPolyEval (p : MvPolynomial σ ℂ) (x : σ → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ)) p

@[simp] theorem realPolyEval_C (c : ℂ) (x : σ → ℝ) : realPolyEval (C c) x = c := by
  simp [realPolyEval]
@[simp] theorem realPolyEval_X (i : σ) (x : σ → ℝ) :
    realPolyEval (X i) x = (x i : ℂ) := by simp [realPolyEval]
@[simp] theorem realPolyEval_add (p q : MvPolynomial σ ℂ) (x : σ → ℝ) :
    realPolyEval (p + q) x = realPolyEval p x + realPolyEval q x := by simp [realPolyEval]
@[simp] theorem realPolyEval_mul (p q : MvPolynomial σ ℂ) (x : σ → ℝ) :
    realPolyEval (p * q) x = realPolyEval p x * realPolyEval q x := by simp [realPolyEval]
@[simp] theorem realPolyEval_zero (x : σ → ℝ) :
    realPolyEval (0 : MvPolynomial σ ℂ) x = 0 := by simp [realPolyEval]
@[simp] theorem realPolyEval_one (x : σ → ℝ) :
    realPolyEval (1 : MvPolynomial σ ℂ) x = 1 := by simp [realPolyEval]

variable [Fintype σ]

theorem contDiff_realPolyEval (p : MvPolynomial σ ℂ) : ContDiff ℝ ∞ (realPolyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c by funext x; exact realPolyEval_C c x]
    exact contDiff_const
  | add p q hp hq =>
    rw [show realPolyEval (p + q) = fun x => realPolyEval p x + realPolyEval q x by funext x; exact realPolyEval_add p q x]
    exact hp.add hq
  | mul_X p i hp =>
    have hx : ContDiff ℝ ∞ (fun x : σ → ℝ => (x i : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff
    rw [show realPolyEval (p * X i) = fun x => realPolyEval p x * (x i : ℂ) by funext x; simp]
    exact hp.mul hx

theorem fderiv_realPolyEval (p : MvPolynomial σ ℂ) (x v : σ → ℝ) :
    fderiv ℝ (realPolyEval p) x v =
      ∑ i, (v i : ℂ) * realPolyEval (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    have heq : realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c := by ext x; exact realPolyEval_C c x
    rw [heq]
    simp
  | add p q hp hq =>
    have h := fderiv_add ((contDiff_realPolyEval p).differentiable (by simp) x)
      ((contDiff_realPolyEval q).differentiable (by simp) x)
    rw [show realPolyEval (p + q) = realPolyEval p + realPolyEval q by ext; simp, h]
    simp only [add_apply, hp, hq, map_add,
      realPolyEval_add, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have hcoord : HasFDerivAt (fun x : σ → ℝ => (x j : ℂ))
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply j x)
    rw [show realPolyEval (p * X j) = fun x => realPolyEval p x * (x j : ℂ) by ext; simp,
      fderiv_fun_mul ((contDiff_realPolyEval p).differentiable (by simp) x)
        hcoord.differentiableAt, hcoord.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
      smul_eq_mul, hp, pderiv_mul, realPolyEval_add, realPolyEval_mul, realPolyEval_X,
      pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib]
    have hif (i : σ) : realPolyEval (if j = i then 1 else 0) x =
        if j = i then 1 else 0 := by split_ifs <;> simp
    simp only [hif, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring

def realPolyDerivEmbed (i : σ) : ℂ →L[ℝ] ((σ → ℝ) →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (σ → ℝ) ℂ (ContinuousLinearMap.proj i)

@[simp] theorem realPolyDerivEmbed_apply (i : σ) (c : ℂ) (v : σ → ℝ) :
    realPolyDerivEmbed i c v = (v i : ℂ) * c := by
  simp [realPolyDerivEmbed, Complex.real_smul]

theorem fderiv_realPolyEval_eq (p : MvPolynomial σ ℂ) :
    fderiv ℝ (realPolyEval p) =
      ∑ i, realPolyDerivEmbed i ∘ realPolyEval (pderiv i p) := by
  classical
  ext x v
  simp [fderiv_realPolyEval]

theorem realPolyEval_jet_zero_of_coeff (k : ℕ) (p : MvPolynomial σ ℂ)
    (hp : ∀ d : σ →₀ ℕ, d.degree < k + 1 → p.coeff d = 0) :
    iteratedFDeriv ℝ k (realPolyEval p) 0 = 0 := by
  classical
  induction k generalizing p with
  | zero =>
    have h₀ : constantCoeff p = 0 := hp 0 (by simp)
    ext v
    simpa [realPolyEval] using h₀
  | succ k ih =>
    have hp' (i : σ) : ∀ d : σ →₀ ℕ, d.degree < k + 1 → (pderiv i p).coeff d = 0 := by
      intro d hd
      rw [coeff_pderiv, hp (d + Finsupp.single i 1), zero_mul]
      simpa only [map_add, Finsupp.degree_single, Nat.add_lt_add_iff_right] using hd
    have hz (i : σ) := ih (pderiv i p) (hp' i)
    have hcont (i : σ) : ContDiff ℝ (k : ℕ∞ω)
        (realPolyDerivEmbed i ∘ realPolyEval (pderiv i p)) :=
      ((realPolyDerivEmbed i).contDiff.comp (contDiff_realPolyEval _)).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
    have hf : iteratedFDeriv ℝ k (fderiv ℝ (realPolyEval p)) 0 = 0 := by
      rw [fderiv_realPolyEval_eq, iteratedFDeriv_sum_apply (fun i _ => (hcont i).contDiffAt)]
      apply Finset.sum_eq_zero
      intro i _
      rw [(realPolyDerivEmbed i).iteratedFDeriv_comp_left
        (contDiff_realPolyEval _).contDiffAt
          (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))), hz i]
      ext m v
      simp
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hf, norm_zero]


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def multilinearPolynomial {n : ℕ} (B : (σ → ℝ) [×n]→L[ℝ] ℂ) : MvPolynomial σ ℂ :=
  ∑ a : Fin n → σ, C (B fun i => Pi.single (a i) 1) * ∏ i, X (a i)

theorem realPolyEval_multilinearPolynomial {n : ℕ}
    (B : (σ → ℝ) [×n]→L[ℝ] ℂ) (x : σ → ℝ) :
    realPolyEval (multilinearPolynomial B) x = B (fun _ => x) := by
  classical
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hB : B (fun _ => x) = ∑ a : Fin n → σ,
      (∏ i, x (a i)) • B (fun i => Pi.single (a i) 1) := by
    conv_lhs => rw [hx]
    rw [B.map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact B.map_smul_univ _ _
  rw [hB]
  simp only [multilinearPolynomial, realPolyEval, map_sum, map_mul, eval_C, map_prod, eval_X]
  apply Finset.sum_congr rfl
  intro a _
  rw [Complex.real_smul, Complex.ofReal_prod]
  exact mul_comm _ _

def realTaylorPolynomial (f : (σ → ℝ) → ℂ) (N : ℕ) : MvPolynomial σ ℂ :=
  ∑ j ∈ Finset.range N,
    C ((j.factorial : ℂ)⁻¹) * multilinearPolynomial (iteratedFDeriv ℝ j f 0)

theorem realPolyEval_realTaylorPolynomial (f : (σ → ℝ) → ℂ) (N : ℕ) (x : σ → ℝ) :
    realPolyEval (realTaylorPolynomial f N) x = finiteTaylorFunction f N x := by
  simp only [realTaylorPolynomial, realPolyEval, map_sum, map_mul, eval_C,
    finiteTaylorFunction]
  apply Finset.sum_congr rfl
  intro j _
  rw [show MvPolynomial.eval (fun i => (x i : ℂ))
    (multilinearPolynomial (iteratedFDeriv ℝ j f 0)) =
      realPolyEval (multilinearPolynomial (iteratedFDeriv ℝ j f 0)) x from rfl,
    realPolyEval_multilinearPolynomial, Complex.real_smul]
  simp

theorem realTaylorPolynomial_jet {f : (σ → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (N k : ℕ) (hk : k < N) :
    iteratedFDeriv ℝ k (realPolyEval (realTaylorPolynomial f N)) 0 =
      iteratedFDeriv ℝ k f 0 := by
  rw [show realPolyEval (realTaylorPolynomial f N) = finiteTaylorFunction f N from
    funext (realPolyEval_realTaylorPolynomial f N)]
  exact iteratedFDeriv_finiteTaylorFunction hf N k hk



end YauCounterexamples
end

end OAI
