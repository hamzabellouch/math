import OAI.Geometry.Convex.GeneralMahler.TestFun

namespace OAI
/-! Hermite modes and Gaussian averages via TestF. Probabilists'
convention, orthonormal scaling. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Layers
def ga (f:ℝ→ℝ) := ∫ x,phi x*f x
lemma ga_i {f:ℝ→ℝ} (hf:TestF f) : Integrable (fun x=>phi x*f x) :=
  (rapid_phi.product hf.poly).integrable_real (c_phi.mul hf.cont).measurable
lemma ga_add {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=>f x+g x)=ga f+ga g := by
  unfold ga; simp_rw [mul_add]; exact integral_add (ga_i hf) (ga_i hg)
lemma ga_sub {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=>f x-g x)=ga f-ga g := by
  unfold ga; simp_rw [mul_sub]; exact integral_sub (ga_i hf) (ga_i hg)
lemma ga_mul (f:ℝ→ℝ) (a:ℝ) : ga (fun x=>a*f x)=a*ga f := by
  unfold ga
  rw [← integral_const_mul]
  congr 1; ext; ring
lemma ga_parts {f:ℝ→ℝ} (hf:TestF f) :
    ga (fun x=>x*f x) = ga (deriv f) := by
  let g := fun x=>phi x*f x
  have he := rapid_phi.product hf.poly
  have hd (x:ℝ) : HasDerivAt g (phi x*deriv f x-phi x*(x*f x)) x := by
    convert (d_phi x).fun_mul (hf.diff x).hasDerivAt using 1
    all_goals first | rfl | ring
  have hi := ga_i hf.der
  have h₁ := ga_i (TestF.id.mul hf)
  have hh := integral_of_hasDerivAt_of_tendsto hd (hi.sub h₁) he.tail_limit_bot he.tail_limit
  rw [integral_sub hi h₁] at hh
  unfold ga; linarith
lemma ga_pair {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    ga (fun x=>(x*f x-deriv f x)*g x) = ga (fun x=>f x*deriv g x) := by
  have h := ga_parts (hf.mul hg)
  rw [funext (show ∀ x,deriv (fun x=>f x*g x) x=_ from
    fun x=> ((hf.diff x).hasDerivAt.fun_mul (hg.diff x).hasDerivAt).deriv)] at h
  have he : (fun x=>(x*f x-deriv f x)*g x)=
      fun x=>x*(f x*g x)-deriv f x*g x := by ext; ring
  have hi := hf.der.mul hg
  have hj := hf.mul hg.der
  rw [ga_add hi hj] at h
  rw [he,ga_sub (TestF.id.mul (hf.mul hg)) hi,h]; ring

lemma gamma_area (f : ℝ→ℝ) :
    (∫ x,f x ∂GeneralMahler.gamma)=ga f := by
  unfold gamma
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]; rfl

namespace HMode
def sn (n:ℕ) := √((n:ℝ))
lemma snsq (n:ℕ) : sn n^2=n := Real.sq_sqrt (Nat.cast_nonneg _)
lemma sn_succ (n:ℕ) : 0 < sn (n+1) := by unfold sn; positivity

def H : ℕ→ℝ→ℝ
 | 0=>fun _=>1
 | n+1=>fun x=>(sn (n+1))⁻¹*(x*H n x - deriv (H n) x)
lemma ht (n:ℕ) : TestF (H n) := by
  induction n with
  | zero=>exact TestF.const _
  | succ n ih=> exact (TestF.const _).mul ((TestF.id.mul ih).sub ih.der)
lemma raise (x:ℝ) (n:ℕ) : sn (n+1)*H (n+1) x=x*H n x-deriv (H n) x := by
  rw [H,← mul_assoc,mul_inv_cancel₀ (sn_succ n).ne',one_mul]
lemma lower (n:ℕ) :
    deriv (H (n+1)) = fun x=>sn (n+1)*H n x := by
  induction n with
  | zero=>
    have h : H 1=fun x=> x := by ext; simp [H,sn]
    rw [h]
    ext; simp [H,sn]
  | succ n ih=>
    ext x
    have hi := sn_succ n
    have hp := sn_succ (n+1)
    have hh : H (n+2)=fun x=>(sn (n+2))⁻¹*(x*H (n+1) x-sn (n+1)*H n x) := by
      funext x; rw [H,ih]
    have he := ((((hasDerivAt_id' x).fun_mul ((ht (n+1)).diff x).hasDerivAt).fun_sub
      (((ht n).diff x).hasDerivAt.const_mul (sn (n+1)))).const_mul ((sn (n+2))⁻¹)).deriv
    rw [hh,he,ih]
    rw [one_mul]
    rw [show (H (n+1) x+x*(sn (n+1)*H n x)-sn (n+1)*deriv (H n) x) =
      sn (n+2)^2*H (n+1) x from ?_]
    field_simp
    calc
      _ = H (n+1) x+sn (n+1)*(x*H n x-deriv (H n) x) := by ring
      _ = _ := by rw [← raise,← mul_assoc,← pow_two,snsq,snsq]; push_cast; ring

lemma Hder (n:ℕ) (x:ℝ) : deriv (H n) x=sn n*H (n-1) x := by
  cases n
  · simp [H,sn]
  rw [lower]; rfl

lemma avg_succ (f:ℝ→ℝ) (hf:TestF f) (n:ℕ) :
    ga (fun x=>H (n+1) x*f x)=(sn (n+1))⁻¹*ga (fun x=>H n x*deriv f x) := by
  have he : (fun x=>H (n+1) x*f x)=fun x=>(sn (n+1))⁻¹*((x*H n x-deriv (H n) x)*f x) := by
    ext; rw [H,mul_assoc]
  rw [he,ga_mul,ga_pair (ht n) hf]

lemma avg_z (n:ℕ) : ga (H (n+1))=0 := by
  simpa [H,ga] using avg_succ (fun _=>1) (TestF.const 1) n
lemma avg_o (n k:ℕ) : ga (fun x=>H n x*H k x)=(if n=k then 1 else 0) := by
  induction n generalizing k with
  | zero=>
    cases k with
    | zero=>simp [H,ga,e_phi]
    | succ k=> simpa only [H,one_mul,Nat.zero_ne_add_one,↓reduceIte] using avg_z k
  | succ n ih=>
    cases k with
    | zero=> simpa only [H,mul_one,Nat.add_one_ne_zero,↓reduceIte] using avg_z n
    | succ k=>
      rw [avg_succ _ (ht _) n,lower k]
      simp_rw [mul_left_comm (H n _),ga_mul,ih]
      split_ifs with h h' <;> first | omega | skip
      · subst k
        rw [mul_one,inv_mul_cancel₀ (sn_succ n).ne']
      · ring
end HMode
end GeneralMahler

end

end OAI
