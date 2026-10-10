import Mathlib
import OAI.Analysis.MatrixSigning.Potential.IteratedDerivCompScale

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Set Matrix
open scoped BigOperators ContDiff

variable {N : ℕ}

def rationalBasis (i : Fin N) : Fin N → ℚ := Pi.single i 1
noncomputable def realBasis (i : Fin N) : Fin N → ℝ := Pi.single i 1

def pointCast (x : Fin N → ℚ) : Fin N → ℝ := fun i => (x i:ℝ)

lemma pointCast_step (x v : Fin N → ℚ) (h : ℚ) :
    pointCast (x+h • v)=pointCast x+(h:ℝ) • pointCast v := by
  funext i
  simp [pointCast]

lemma pointCast_basis (i : Fin N) : pointCast (rationalBasis i)=realBasis i := by
  funext j
  by_cases he : j=i <;> simp [pointCast,rationalBasis,realBasis,he]

lemma pointCast_add (u v : Fin N → ℚ) : pointCast (u+v)=pointCast u+pointCast v := by
  funext i
  simp [pointCast]

lemma pointCast_neg (u : Fin N → ℚ) : pointCast (-u) = -pointCast u := by
  funext i
  simp [pointCast]

lemma realBasis_bound (i : Fin N) : ‖realBasis i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases he : j=i <;> simp [realBasis,he]

def stencilValue (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ)
    (v : Fin N → ℚ) : ℚ := query (x+h • v)

def stencilGradient (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ) (i : Fin N) : ℚ :=
  (stencilValue query x h (rationalBasis i)-stencilValue query x h (-rationalBasis i))/(2*h)

def stencilHessian (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => if i=j then
    (stencilValue query x h (rationalBasis i)-2*query x+stencilValue query x h (-rationalBasis i))/h^2
  else
    (stencilValue query x h (rationalBasis i+rationalBasis j)-
     stencilValue query x h (rationalBasis i-rationalBasis j)-
     stencilValue query x h (-rationalBasis i+rationalBasis j)+
     stencilValue query x h (-rationalBasis i-rationalBasis j))/(4*h^2)

lemma stencilHessian_symm (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ) :
    (stencilHessian query x h).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  dsimp [stencilHessian]
  by_cases hij : i=j
  · subst j; rfl
  · rw [ite_eq_right hij,ite_eq_right (Ne.symm hij)]
    have h1 : rationalBasis j+rationalBasis i=rationalBasis i+rationalBasis j := add_comm _ _
    have h2 : rationalBasis j-rationalBasis i = -rationalBasis i+rationalBasis j := sub_eq_neg_add _ _
    have h3 : -rationalBasis j+rationalBasis i=rationalBasis i-rationalBasis j := (sub_eq_neg_add _ _).symm
    have h4 : -rationalBasis j-rationalBasis i = -rationalBasis i-rationalBasis j := by
      simp only [sub_eq_add_neg,add_comm]
    rw [h1,h2,h3,h4]
    ring

lemma ball_remainder_unit (f : (Fin N → ℝ) → ℝ) (x v : Fin N → ℝ) {h M : ℝ}
    (hh : 0<h) (hv : ‖v‖ ≤ 1)
    (hf : ∀ y,‖y-x‖ ≤ 2*h → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-x‖ ≤ 2*h → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M) :
    |f (x+h • v)-(f x+h*(fderiv ℝ f x v)+
      h^2/2*(fderiv ℝ (fderiv ℝ f) x v v))| ≤ M*h^3/6 := by
  have he := ball_quadratic_remainder f x v hh (by norm_num : (0:ℝ)<1) hv
    (fun y hy => hf y (by linarith)) (fun y hy => hM y (by linarith))
  simpa only [one_pow,mul_one] using he

theorem stencilGradient_error (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℚ) (h : ℚ) (i : Fin N) {M e : ℝ} (hh : 0<h) (he : 0 ≤ e)
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) → |(query y:ℝ)-f (pointCast y)| ≤ e) :
    |(stencilGradient query x h i:ℝ)-fderiv ℝ f (pointCast x) (realBasis i)| ≤
      M*(h:ℝ)^2/6+e/(h:ℝ) := by
  have hhr : (0:ℝ)<h := by exact_mod_cast hh
  have hp := ball_remainder_unit f (pointCast x) (realBasis i) hhr (realBasis_bound i) hf hM
  have hm := ball_remainder_unit f (pointCast x) (-realBasis i) hhr
    (by simpa only [norm_neg] using realBasis_bound i) hf hM
  simp only [map_neg,_root_.neg_apply,neg_neg,smul_neg,mul_neg,← sub_eq_add_neg] at hm
  have hq (v : Fin N → ℚ) (hv : ‖pointCast v‖ ≤ 1) :
      |(stencilValue query x h v:ℝ)-f (pointCast x+(h:ℝ) • pointCast v)| ≤ e := by
    have ht : ‖pointCast (x+h • v)-pointCast x‖ ≤ 2*(h:ℝ) := by
      rw [pointCast_step]
      exact (segment_in_ball hhr.le zero_le_one hv ⟨hhr.le,le_rfl⟩).trans (by linarith)
    simpa only [stencilValue,pointCast_step] using hquery (x+h • v) ht
  have hpq := hq (rationalBasis i) (by simpa only [pointCast_basis] using realBasis_bound i)
  have hmq := hq (-rationalBasis i) (by simpa only [pointCast_neg,pointCast_basis,norm_neg] using realBasis_bound i)
  simp only [pointCast_basis,pointCast_neg,smul_neg,← sub_eq_add_neg] at hpq hmq
  have ht := gradient_error hhr he hp hm hpq hmq
  simpa only [stencilGradient,Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat] using ht

theorem stencilHessian_diagonal_error (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℚ) (h : ℚ) (i : Fin N) {M e : ℝ} (hh : 0<h) (he : 0 ≤ e)
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) → |(query y:ℝ)-f (pointCast y)| ≤ e) :
    |(stencilHessian query x h i i:ℝ)-fderiv ℝ (fderiv ℝ f) (pointCast x) (realBasis i) (realBasis i)| ≤
      M*(h:ℝ)/3+4*e/(h:ℝ)^2 := by
  have hhr : (0:ℝ)<h := by exact_mod_cast hh
  have hp := ball_remainder_unit f (pointCast x) (realBasis i) hhr (realBasis_bound i) hf hM
  have hm := ball_remainder_unit f (pointCast x) (-realBasis i) hhr
    (by simpa only [norm_neg] using realBasis_bound i) hf hM
  simp only [map_neg,_root_.neg_apply,neg_neg,smul_neg,mul_neg,← sub_eq_add_neg] at hm
  have hq (v : Fin N → ℚ) (hv : ‖pointCast v‖ ≤ 1) :
      |(stencilValue query x h v:ℝ)-f (pointCast x+(h:ℝ) • pointCast v)| ≤ e := by
    have ht : ‖pointCast (x+h • v)-pointCast x‖ ≤ 2*(h:ℝ) := by
      rw [pointCast_step]
      exact (segment_in_ball hhr.le zero_le_one hv ⟨hhr.le,le_rfl⟩).trans (by linarith)
    simpa only [stencilValue,pointCast_step] using hquery (x+h • v) ht
  have hpq := hq (rationalBasis i) (by simpa only [pointCast_basis] using realBasis_bound i)
  have hmq := hq (-rationalBasis i) (by simpa only [pointCast_neg,pointCast_basis,norm_neg] using realBasis_bound i)
  simp only [pointCast_basis,pointCast_neg,smul_neg,← sub_eq_add_neg] at hpq hmq
  have h0 := hquery x (by simp only [sub_self,norm_zero]; positivity)
  have ht := diagonal_error hhr he hp hm hpq hmq h0
  simpa only [stencilHessian,ite_true,Rat.cast_div,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,
    Rat.cast_pow,Rat.cast_ofNat] using ht

lemma pointCast_sub (u v : Fin N → ℚ) : pointCast (u-v)=pointCast u-pointCast v := by
  funext i
  simp [pointCast]

lemma realBasis_pair_bound (i j : Fin N) (si sj : ℝ) (hsi : |si| ≤ 1) (hsj : |sj| ≤ 1) :
    ‖si • realBasis i+sj • realBasis j‖ ≤ 2 := by
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
  have hi := mul_le_mul hsi (realBasis_bound i) (norm_nonneg _) zero_le_one
  have hj := mul_le_mul hsj (realBasis_bound j) (norm_nonneg _) zero_le_one
  linarith

theorem stencilHessian_mixed_error (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℚ) (h : ℚ) (i j : Fin N) (hij : i ≠ j) {M e : ℝ} (hh : 0<h)
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) → |(query y:ℝ)-f (pointCast y)| ≤ e) :
    |(stencilHessian query x h i j:ℝ)-fderiv ℝ (fderiv ℝ f) (pointCast x) (realBasis i) (realBasis j)| ≤
      (4/3:ℝ)*M*(h:ℝ)+e/(h:ℝ)^2 := by
  have hhr : (0:ℝ)<h := by exact_mod_cast hh
  have ht (v : Fin N → ℝ) (hv : ‖v‖ ≤ 2) :=
    ball_quadratic_remainder f (pointCast x) v hhr (by norm_num : (0:ℝ)<2) hv hf hM
  have hsym := (hf (pointCast x) (by simp only [sub_self,norm_zero]; positivity)).isSymmSndFDerivAt
    (by norm_num : minSmoothness ℝ 2 ≤ (3:WithTop ℕ∞))
  have hji := hsym (realBasis j) (realBasis i)
  have hpp := ht (realBasis i+realBasis j) (by
    simpa only [one_smul] using realBasis_pair_bound i j 1 1 (by norm_num) (by norm_num))
  have hpm := ht (realBasis i-realBasis j) (by
    simpa only [one_smul,neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j 1 (-1) (by norm_num) (by norm_num))
  have hmp := ht (-realBasis i+realBasis j) (by
    simpa only [one_smul,neg_one_smul] using realBasis_pair_bound i j (-1) 1 (by norm_num) (by norm_num))
  have hmm := ht (-realBasis i-realBasis j) (by
    simpa only [neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j (-1) (-1) (by norm_num) (by norm_num))
  simp only [map_add,map_sub,map_neg,_root_.add_apply,
    _root_.sub_apply,_root_.neg_apply,hji] at hpp hpm hmp hmm
  have hlin : ∀ a b c : ℝ, a+b+(b+c)=a+c+2*b := by intros; ring
  have hlin2 : ∀ a b c : ℝ, a-b-(b-c)=a+c-2*b := by intros; ring
  have hlin3 : ∀ a b c : ℝ, -(-a+b)+(-b+c)=a+c-2*b := by intros; ring
  have hlin4 : ∀ a b c : ℝ, -(-a-b)-(-b-c)=a+c+2*b := by intros; ring
  rw [hlin] at hpp
  rw [hlin2] at hpm
  rw [hlin3] at hmp
  rw [hlin4] at hmm
  have hq (v : Fin N → ℚ) (hv : ‖pointCast v‖ ≤ 2) :
      |(stencilValue query x h v:ℝ)-f (pointCast x+(h:ℝ) • pointCast v)| ≤ e := by
    have hb : ‖pointCast (x+h • v)-pointCast x‖ ≤ 2*(h:ℝ) := by
      rw [pointCast_step]
      exact segment_in_ball hhr.le (by norm_num) hv ⟨hhr.le,le_rfl⟩
    simpa only [stencilValue,pointCast_step] using hquery (x+h • v) hb
  have hqpp := hq (rationalBasis i+rationalBasis j) (by
    rw [pointCast_add,pointCast_basis,pointCast_basis]
    simpa only [one_smul] using realBasis_pair_bound i j 1 1 (by norm_num) (by norm_num))
  have hqpm := hq (rationalBasis i-rationalBasis j) (by
    rw [pointCast_sub,pointCast_basis,pointCast_basis]
    simpa only [one_smul,neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j 1 (-1) (by norm_num) (by norm_num))
  have hqmp := hq (-rationalBasis i+rationalBasis j) (by
    rw [pointCast_add,pointCast_neg,pointCast_basis,pointCast_basis]
    simpa only [one_smul,neg_one_smul] using realBasis_pair_bound i j (-1) 1 (by norm_num) (by norm_num))
  have hqmm := hq (-rationalBasis i-rationalBasis j) (by
    rw [pointCast_sub,pointCast_neg,pointCast_basis,pointCast_basis]
    simpa only [neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j (-1) (-1) (by norm_num) (by norm_num))
  simp only [pointCast_add,pointCast_sub,pointCast_neg,pointCast_basis] at hqpp hqpm hqmp hqmm
  have hm := mixed_error hhr hpp hpm hmp hmm hqpp hqpm hqmp hqmm
  have heq : ((M*(2:ℝ)^3)*(h:ℝ)^3/6+e)/(h:ℝ)^2 = (4/3:ℝ)*M*(h:ℝ)+e/(h:ℝ)^2 := by
    field_simp
    ring
  rw [heq] at hm
  simpa only [stencilHessian,ite_eq_right hij,Rat.cast_div,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,
    Rat.cast_pow,Rat.cast_ofNat] using hm

end CurrentKS.Difference

end OAI
