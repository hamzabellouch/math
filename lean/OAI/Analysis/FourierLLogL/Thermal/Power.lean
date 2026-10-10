import OAI.Analysis.FourierLLogL.Thermal.GridFreq
import OAI.Analysis.FourierLLogL.Compress.Phase
import OAI.Analysis.FourierLLogL.Compress.Variational

/-! # Moment calculation on the snapped spectrum -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period

variable {M l : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Fintype Γ]

/-- Polynomial evaluated at points of the full grid. -/
def ply (hl : l ≤ M) (p : Law (Grid l)) (f : Grid l → ℂ) (y : Grid M) :=
    p.Cx (fun x => f x * chi (raise hl x) y)
def HeatM (hl : l ≤ M) (A : Form M) (p : Law (Grid l)) (T : ℕ) :=
    (label A).Ex fun y => ‖ply hl p 1 y‖^(2*T)
def levelCost (hl : l ≤ M) (A : Form M) (p : Law (Grid l)) (T : ℕ) :=
    -log (HeatM hl A p T)

lemma ply_unit (hl : l ≤ M) (p : Law (Grid l)) (f : Grid l → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (y) :
    ‖ply hl p f y‖ ≤ 1 := norm_Cx_unit _ _ fun x => by rw [norm_mul,norm_chi,mul_one]; exact hf _

lemma ply_one_zero (hl : l ≤ M) (p : Law (Grid l)) : ply hl p 1 0 = 1 := by
  unfold ply; simp_rw [chi_zero_right, mul_one,Pi.one_apply]
  rw [show (fun _ : Grid l => (1:ℂ)) = fun _ => (↑(1:ℝ):ℂ) by simp, Cx_ofReal,Ex_const]
  rfl

lemma HeatM_bounds (hl : l ≤ M) (A : Form M) (p : Law (Grid l)) (T : ℕ) :
    0 < HeatM hl A p T ∧ HeatM hl A p T ≤ 1 := by
  constructor
  · unfold HeatM Ex
    apply lt_of_lt_of_le (b:=label A 0 * ‖ply hl p 1 0‖^(2*T))
    · rw [ply_one_zero,norm_one,one_pow,mul_one]; exact label_pos _ _
    refine Finset.single_le_sum (f:=fun y => label A y * ‖ply hl p 1 y‖^(2*T))
      (fun i _ => mul_nonneg (label_pos _ _).le (by positivity)) (Finset.mem_univ _)
  · unfold HeatM
    refine le_trans (b:=(label A).Ex fun _ => 1) (Ex_mono _ fun x => ?_) (by rw [Ex_const])
    exact pow_le_one₀ (norm_nonneg _) (ply_unit hl p 1 (fun _ => by simp) _)

lemma heat_exp (hl : l ≤ M) (A : Form M) (p : Law (Grid l)) (T : ℕ) :
    exp (-levelCost hl A p T) = HeatM hl A p T := by
  rw [levelCost,neg_neg, exp_log (HeatM_bounds _ _ _ _).1]

lemma heat_nonneg (hl : l ≤ M) (A : Form M) (p : Law (Grid l)) (T : ℕ) :
    0 ≤ levelCost hl A p T := neg_nonneg.mpr (log_nonpos
      (HeatM_bounds _ _ _ _).1.le (HeatM_bounds _ _ _ _).2)

lemma Cx_send (P : Law Γ) (X : Γ → Grid l) (f : Grid l → ℂ) :
    (P.send X).Cx f = P.Cx fun i => f (X i) := by
  unfold Cx
  classical
  simp_rw [send_apply,prob_eq,Complex.ofReal_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (X i),ite_eq_left rfl]
  · intro j _ hj
    rw [ite_eq_right hj.symm, Complex.ofReal_zero,zero_mul]
  simp

lemma pack_ply_expand (T : ℕ) (hl : l ≤ M) (p : Law Γ) (tag : Γ → Grid l)
    (f : Grid l → ℂ) (y : Grid M) :
    let Q : Law (Fin T → Γ) := pack fun _ => p
    let W (X : Fin T → Γ) := ∏ i, f (tag (X i))
    let t := Compress.tot tag (ι:=Fin T)
    ‖ply hl (p.send tag) f y‖^(2*T) = Q.Ex fun X => Q.Ex fun X' =>
        (W X * conj (W X') * chi (raise hl (t X-t X')) y).re := by
  classical
  intro Q W t
  let u := fun x : Grid l => chi (raise hl x) y
  let g := fun x : Γ => f (tag x)*u (tag x)
  have hu (X : Fin T → Γ) :
      ∏ i, g (X i) = W X * u (t X) := by
    unfold g W; rw [Finset.prod_mul_distrib]
    have H (x : Grid l) : u x = raiseChar hl y x := (raiseChar_eq hl _ _).symm
    simp_rw [H, t,Compress.tot,Compress.char_sum]
  have he : ply hl (p.send tag) f y ^ T = Q.Cx fun X => W X * u (t X) := by

    have HX : ply hl (p.send tag) f y = p.Cx g := Cx_send _ _ _
    simp only [HX]
    unfold Q
    simp_rw [← hu, Cx_prod (fun _ : Fin T => p) (fun _ => g)]
    simp
  have hn (X X' : Fin T → Γ) : W X* conj (W X')*chi (raise hl (t X-t X')) y =
      (W X * u (t X)) * conj (W X'*u (t X')) := by
    unfold u; simp_rw [map_sub,map_mul,sub_eq_add_neg,chi_add',chi_neg']
    ring
  rw [mul_comm 2 _,pow_mul,← norm_pow,he,sq_norm_Cx]; simp_rw [hn]

lemma selected_heat (T : ℕ) (hl : l ≤ M) (A : Form M)
    (hA : ∀ i : Grid M, 0 < cred A i) (p : Law Γ) (tag : Γ → Grid l) :
    Compress.heatMoment (Fin T) p tag (fq_cost hl A) = HeatM hl A (p.send tag) T := by
  let Q : Law (Fin T → Γ) := pack fun _ => p
  let t (f : Fin T → Γ) := Compress.tot tag f
  change (Q.Ex fun X => Q.Ex fun X' => exp ( -fq_cost hl A (t X-t X'))) = _
  unfold HeatM
  have h (y : Grid M) : ‖ply hl (p.send tag) 1 y‖^(2*T) = Q.Ex (fun X => Q.Ex
    fun X' => wave (raise hl (t X-t X')) y) := by
    simp only [pack_ply_expand,Finset.prod_const_one,Pi.one_apply,map_one,one_mul]
    rfl
  simp_rw [h,Ex_swap (label A) Q,wave]
  have he (i : Grid l) : exp ( -fq_cost hl A i) = (label A).Ex fun y => (chi (raise hl i) y).re := by
    rw [fq_cost,neg_neg,exp_log (hA _),cred_ex]; rfl
  simp_rw [he]

lemma weighted_envelope (T : ℕ) (hl : l ≤ M) (A : Form M) (p : Law (Grid l))
    (f : Grid l → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (W : Grid M → ℝ) (c : ℝ)
    (H : ∀ i, ‖expU (fun y => (W y:ℂ)*chi i y)‖ ≤ c*cred A i) :
    expU (fun y => W y * ‖ply hl p f y‖^(2*T)) ≤ c * HeatM hl A p T := by
  let P := label A
  let Q := pack fun _ : Fin T => p
  let t (X : Fin T → Grid l) := ∑ i, X i
  let v (X X' : Fin T → Grid l) := raise hl (t X-t X')
  let V (X : Fin T → Grid l) := ∏ i, f (X i)
  have hp : p.send (fun x => x) = p := send_id _
  have he (y : Grid M) : ‖ply hl p f y‖^(2*T)= Q.Ex fun X => Q.Ex fun X' =>
      (V X * conj (V X') * chi (v X X') y).re := by
    have hi := pack_ply_expand T hl p (fun x => x) f y
    rw [hp] at hi
    exact hi
  have he' (y : Grid M) : ‖ply hl p 1 y‖^(2*T)= Q.Ex fun X => Q.Ex fun X' =>
      wave (v X X') y := by
    have hi := pack_ply_expand T hl p (fun x => x) 1 y
    simp only [hp, Pi.one_apply,Finset.prod_const_one,map_one,one_mul] at hi
    exact hi
  have hV (X : Fin T → Grid l) : ‖V X‖ ≤ 1 := by
    unfold V; rw [Complex.norm_prod]
    apply le_trans (b:=∏ _i : Fin T, (1:ℝ)) (Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)) (by simp)
    · positivity
    · exact hf _
  let L := Law.uniform (Grid M)
  have hX (X X' : Fin T → Grid l) : L.Ex (fun y => W y * (V X*conj (V X')*chi (v X X') y).re) ≤
      c * P.Ex (wave (v X X')) := by
    let Z := V X * conj (V X')
    let s := v X X'
    change L.Ex (fun y => W y * (Z*chi s y).re) ≤ c*P.Ex (wave s)
    have he : L.Ex (fun y => W y * (Z*chi s y).re) = (Z * expU (fun y => (W y:ℂ)*chi s y)).re := by
      rw [expU_cx,← Cx_lmul,re_Cx]
      refine congrArg _ (funext fun y => ?_); rw [mul_left_comm,Complex.re_ofReal_mul]
    rw [he, show P.Ex (wave s)=cred A s from (cred_ex _ _).symm]
    apply le_trans (le_abs_self _)
    apply le_trans (Complex.abs_re_le_norm _)
    rw [norm_mul]
    have hZ : ‖Z‖ ≤ 1 := by
      unfold Z; rw [norm_mul,Complex.norm_conj]
      calc
        ‖V X‖ * ‖V X'‖ ≤ 1 * ‖V X'‖ :=
          mul_le_mul_of_nonneg_right (hV X) (norm_nonneg _)
        _ ≤ 1 := by simpa using hV X'
    exact (mul_le_of_le_one_left (norm_nonneg _) hZ).trans (H s)
  unfold HeatM
  simp_rw [he,he',expU_ex]

  simp_rw [← Ex_lmul Q, Ex_swap (label A) Q,Ex_swap (uniform (Grid M)) Q]
  simp_rw [← Ex_lmul Q]
  exact Q.Ex_mono fun X => Q.Ex_mono fun X' => hX X X'

end FourierLLogL.Dyadic.Thermal

end OAI
