import OAI.Combinatorics.HadwigerCounterexample.FiniteAffineLaws
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! # Walsh Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

def wsign (x : F) : ℝ := if x = 0 then 1 else -1

@[simp] theorem wsign_zero : wsign 0=1 := by simp [wsign]
@[simp] theorem wsign_one : wsign 1=-1 := by simp [wsign]
theorem wsign_add (x y : F) : wsign (x+y) = wsign x * wsign y := by
  rcases bit_cases x with h|h <;> rcases bit_cases y with g|g <;>
    simp [h,g,char_two]

@[simp] theorem wsign_abs (x) : |wsign x|=1 := by rcases bit_cases x with h|h <;> simp [h]

variable {A B V W : Type} [Fintype A] [Fintype B]

theorem avg_prod (w f g : Wgt A) :
    avg w f * avg w g = avg (pairW w w) (fun x => f x.1*g x.2) := (pairW_separate ..).symm

theorem avg_CS {w : Wgt A} (h : ∀ x, 0 ≤ w x) (f g : Wgt A) :
    (avg w (fun x => f x*g x))^2 ≤ avg w (fun x => f x^2)*avg w (fun x => g x^2) := by
  let F (f : Wgt A) (x) := Real.sqrt (w x)*f x
  have hg (f : Wgt A) (x) : (F f x)^2=w x*f x^2 := by
    unfold F; rw [mul_pow, Real.sq_sqrt (h x)]
  have hx (x) : F f x*F g x=w x*(f x*g x) := by
    unfold F; rw [mul_mul_mul_comm,← pow_two,Real.sq_sqrt (h _)]
  have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (F f) (F g)
  simp_rw [hg,hx] at he
  exact he

variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [Fintype V] [Fintype W]

/-- Walsh orthogonality via a translation of the uniform measure. -/
theorem wsign_lin (b : V →ₗ[F] F) : avg unif (fun x => wsign (b x)) = ind (b=0) := by
  classical
  by_cases h : b = 0
  · simp only [h,LinearMap.zero_apply,wsign_zero]
    simpa using unif_law.avg_const _
  obtain ⟨x,hx⟩ : ∃ x, b x=1 := by
    by_contra! hg
    exact h (LinearMap.ext fun x => (bit_cases _).resolve_right (hg x))
  let E : V ≃ V := ⟨(·+x),(·+x),add_polar x,add_polar x⟩
  have he := avg_bij E unif (fun x => wsign (b x))
  change avg unif (fun z => wsign (b (z+x))) = _ at he
  simp_rw [map_add,wsign_add,hx,wsign_one] at he
  rw [avg_mul] at he
  rw [ind_zero h]
  linarith only [he]

/-- A bilinear signs mean. -/
theorem wsign_bilin (b : V →ₗ[F] W →ₗ[F] F) :
    avg (pairW unif unif) (fun x => wsign (b x.1 x.2)) = bp (-(rk b:ℝ)) := by
  classical
  rw [pairW_avg]
  simp_rw [wsign_lin]
  have : Finite (W →ₗ[F] F) := Finite.of_injective _ DFunLike.coe_injective
  let := Fintype.ofFinite (W →ₗ[F] F)
  change pr unif _ = _
  rw [pr_unif_lin b 0,ind_one (LinearMap.range b).zero_mem,one_mul]

omit [Fintype V] in
theorem avg_ws (b : V →ₗ[F] W →ₗ[F] F) (x z : V) :
    avg unif (fun w => wsign (b x w)*wsign (b z w)) = ind (b x=b z) := by
  simp_rw [← wsign_add]
  change avg unif (fun w => wsign ((b x+b z) w)) = _
  rw [wsign_lin]
  apply congrArg ind
  exact propext (by rw [← ZModModule.sub_eq_add,sub_eq_zero])

/-- Unnormalized inner mean square identity. -/
theorem avg_wsq (b : V →ₗ[F] W →ₗ[F] F) (v f : Wgt V) :
    avg unif (fun w => (avg v (fun x => f x*wsign (b x w)))^2) =
      avg (pairW v v) (fun x => f x.1 * f x.2 * ind (b x.1=b x.2)) := by
  simp_rw [pow_two,avg_prod]
  rw [avg_avg]
  refine avg_congr fun ⟨x,z⟩ _ => ?_
  simp_rw [mul_mul_mul_comm (f x) _ (f z)]
  rw [avg_mul',avg_ws]

private theorem bp_half_le {x a : ℝ} (h : x^2 ≤ bp a) : |x| ≤ bp (a/2) := by
  have hh : bp (a/2)^2 = bp a := by rw [pow_two,←bp_add]; congr 1; ring
  exact le_of_pow_le_pow_left₀ (show (2:ℕ) ≠ 0 by decide) (bp_pos _).le (by rwa [sq_abs,hh])

/-- Correlation with arbitrary bounded unary tests. -/
theorem walsh_bound (b : V →ₗ[F] W →ₗ[F] F) (f : Wgt V) (g : Wgt W)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) :
    |avg unif (fun w => g w * avg unif (fun x => f x*wsign (b x w)))| ≤ bp (-(rk b:ℝ)/2) := by
  classical
  have : Finite (W →ₗ[F] F) := Finite.of_injective _ DFunLike.coe_injective
  let := Fintype.ofFinite (W →ₗ[F] F)
  apply bp_half_le
  let F w := avg unif (fun x => f x*wsign (b x w))
  have h1 :
      avg unif (fun w => g w^2) ≤ 1 := unif_law.avg_le (fun x => by
    have h := abs_le.mp (hg x); nlinarith [h.1,h.2])
  have h2 :
      avg unif (fun w => (F w)^2) ≤ bp (-(rk b:ℝ)) := by
    unfold F; rw [avg_wsq]
    have hx : avg (pairW unif unif) (fun (x : V × V) => ind (b x.1 = b x.2))
        = bp (-(rk b:ℝ)) := by
      rw [pairW_avg]
      have hh x :
          avg unif (fun z => ind (b x = b z)) = bp (-(rk b:ℝ)) := by
        have h' : b x ∈ LinearMap.range b := ⟨x,rfl⟩
        have heq := pr_unif_lin b (b x)
        rw [ind_one h',one_mul] at heq
        change pr unif _ = _
        simp_rw [eq_comm (a:=b x)]
        exact heq
      simp_rw [hh]
      exact unif_law.avg_const _
    rw [← hx]
    refine avg_mono (pairW_law unif_law unif_law).nz fun ⟨x,y⟩ => ?_
    have hh : f x*f y ≤ 1 := by
      have hh := mul_le_mul (hf x) (hf y) (abs_nonneg _) (by norm_num : 0 ≤ (1:ℝ))
      rw [← abs_mul,one_mul] at hh
      exact (le_abs_self _).trans hh
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (ind_nonneg (b x=b y))
  apply le_trans (avg_CS unif_law.nz _ F)
  exact (mul_le_mul h1 h2 (avg_nonneg unif_law.nz fun _ => sq_nonneg _) (by norm_num)).trans_eq
    (one_mul _)

/-- Min-entropy form, squared. -/
theorem walsh_mass (b : V →ₗ[F] W →ₗ[F] F) (hb : Function.Injective b) (u : Wgt V) (v : Wgt W)
    (f : Wgt V) (g : Wgt W)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) (hu : SubLaw u) (hv : SubLaw v)
    {p q : ℝ} (hp : ∀ x, u x ≤ p) (hq : ∀ x, v x ≤ q) :
    (avg v (fun w => g w * avg u (fun x => f x*wsign (b x w))))^2 ≤
      (Fintype.card W : ℝ)*p*q := by
  classical
  let F w := avg u (fun x => f x*wsign (b x w))
  have hi {A : Type} [Fintype A] {p : ℝ} (h : 0 ≤ p) (v f : Wgt A) (hw : SubLaw v)
      (hh : ∀ x, v x ≤ p) (hg : ∀ x, |f x|≤1) : ∑ x, (v x*f x)^2 ≤ p := by
    have hr x : (v x*f x)^2 ≤ v x*p := calc
      _ = v x^2*f x^2 := mul_pow _ _ _
      _ ≤ v x^2*1 := by
        have he := abs_le.mp (hg x)
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [he.1,he.2]
      _ ≤ _ := by rw [mul_one,pow_two]; exact mul_le_mul_of_nonneg_left (hh x) (hw.nz x)
    exact (Finset.sum_le_sum (fun x _ => hr x)).trans (hw.avg_le h (f:=fun _ => p) (fun _ => le_rfl))
  have hh1 := hi ((hv.nz 0).trans (hq 0)) v g hv hq hg
  have hh2 := hi ((hu.nz 0).trans (hp 0)) u f hu hp hf
  have heq : avg (pairW u u) (fun x : V×V => f x.1*f x.2*ind (b x.1=b x.2)) =
      ∑ x, (u x*f x)^2 := by
    rw [pairW_avg]; unfold avg
    refine Finset.sum_congr rfl fun x _ => ?_
    have h z : (b x=b z) ↔ x=z := hb.eq_iff
    simp [h,ind]
    ring
  have hW : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh3 : ∑ w, F w^2 ≤ (Fintype.card W : ℝ)*p := by
    rw [mul_comm]
    apply (div_le_iff₀ hW).mp
    calc _ = avg unif (fun w => F w^2) := by simp only [avg,unif_apply,← Finset.mul_sum];
                                              rw [div_eq_mul_inv,mul_comm]
         _ ≤ _ := (avg_wsq b u f).le.trans (heq.le.trans hh2)
  calc
    _ = (∑ w, (v w*g w)*F w)^2 := by simp only [mul_assoc]; rfl
    _ ≤ (∑ w, (v w*g w)^2) * ∑ w, (F w)^2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ _ := by rw [mul_comm _ q]; exact mul_le_mul hh1 hh3
                  (Finset.sum_nonneg fun _ _ => sq_nonneg _) ((hv.nz 0).trans (hq 0))

end HadwigerCounterexample

end

end OAI
