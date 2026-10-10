import OAI.Analysis.FourierLLogL.Dyadic.Grid
import OAI.Analysis.FourierLLogL.Finite.Complex

/-! # Cyclic grid, characters and averaged Fourier coefficients -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate

noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic
open Period Law

variable {M : ℕ}

lemma card_side (M : ℕ) : side M = (Fintype.card (Grid M):ℝ)⁻¹ := by
  unfold Grid
  rw [ZMod.card]
  simp [side]

lemma uniform_side (x : Grid M) : uniform (Grid M) x = side M :=
  (uniform_apply x).trans (card_side M).symm

lemma side_pow_two (M : ℕ) : side M = ((2:ℝ)^M)⁻¹ := by simp [side]

lemma expU_ex (f : Grid M → ℝ) : expU f = (uniform _).Ex f := by
  unfold expU Ex
  simp_rw [uniform_side,← Finset.mul_sum]; rfl

lemma expU_cx (f : Grid M → ℂ) : expU f = (uniform _).Cx f := by
  unfold expU Cx
  simp_rw [uniform_side,← Finset.mul_sum]
  rw [Complex.real_smul]

lemma expU_prod {E : Type*} [AddCommMonoid E] [DistribMulAction ℝ E]
    (f : Grid M → Grid M → E) :
    expU (fun y => expU (f y)) = expU fun x => expU fun y => f y x := by
  unfold expU
  simp_rw [← Finset.smul_sum]
  rw [Finset.sum_comm]

lemma expU_sum {E : Type*} [AddCommMonoid E] [DistribMulAction ℝ E]
    {ι : Type*} (s : Finset ι) (f : ι → Grid M → E) :
    expU (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, expU (f i) := by
  unfold expU; rw [Finset.sum_comm, Finset.smul_sum]

lemma expU_add {E : Type*} [AddCommMonoid E] [DistribMulAction ℝ E]
    (f g : Grid M → E) :
    expU (fun x => f x+g x) = expU f+expU g := by
  unfold expU; rw [Finset.sum_add_distrib, smul_add]

lemma expU_translate {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (f : Grid M → E) (a : Grid M) :
    expU (fun x => f (a+x)) = expU f := by
  unfold expU
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ => rfl)

lemma expU_reflect {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (f : Grid M → E) :
    expU (fun x => f (-x)) = expU f := by
  unfold expU; congr 1
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)

lemma expU_lmul (a : ℂ) (f : Grid M → ℂ) :
    expU (fun x => a*f x) = a*expU f := by rw [expU_cx, expU_cx, Cx_lmul]

lemma expU_real (f : Grid M → ℝ) :
    expU (fun x => (f x:ℂ)) = (expU f:ℝ) := by rw [expU_cx, expU_ex, Cx_ofReal]

/-- Wrap grid characters as an AddChar. -/
def phaseChar (u : Grid M) : AddChar (Grid M) ℂ := ZMod.stdAddChar.mulShift u

@[simp] lemma phaseChar_apply (u x : Grid M) : phaseChar u x = chi u x := rfl

lemma chi_comm (x y : Grid M) : chi x y = chi y x := by
  unfold chi; rw [mul_comm]

lemma chi_zero_right (u : Grid M) : chi u 0 = 1 := (phaseChar u).map_zero_eq_one
lemma chi_zero_left (u : Grid M) : chi 0 u = 1 := by rw [chi_comm,chi_zero_right]

lemma chi_add (u x y : Grid M) : chi u (x+y) = chi u x * chi u y :=
  (phaseChar u).map_add_eq_mul _ _

lemma chi_add' (x y u : Grid M) : chi (x+y) u = chi x u * chi y u := by
  rw [chi_comm _ u,chi_add,chi_comm u x,chi_comm u y]

lemma chi_neg (u x : Grid M) : chi u (-x) = conj (chi u x) := by
  have H1 : chi u x * chi u (-x) = 1 := by rw [← chi_add, add_neg_cancel, chi_zero_right]
  have H2 := Complex.mul_conj (chi u x)
  rw [← Complex.sq_norm,norm_chi] at H2
  simp only [one_pow,Complex.ofReal_one] at H2
  exact mul_left_cancel₀ (by rintro H; rw [H] at H1; simp at H1) (H1.trans H2.symm)

lemma chi_neg' (x u : Grid M) : chi (-x) u = conj (chi x u) := by rw [chi_comm,chi_neg,chi_comm u x]
lemma chi_sub (u x y : Grid M) : chi u (x-y) = chi u x * conj (chi u y) := by
  rw [sub_eq_add_neg,chi_add,chi_neg]

lemma chi_nsmul (u x : Grid M) (n : ℕ) : chi (n • u) x = (chi u x)^n := by
  induction n with
  | zero => simp [chi_zero_left]
  | succ n ih =>
    rw [add_smul,one_smul,chi_add',ih,pow_succ]

lemma expU_chi (u : Grid M) :
    expU (chi u) = if u=0 then 1 else 0 := by
  by_cases H : u=0
  · subst u
    rw [expU_cx, funext chi_zero_left]
    norm_num [Cx,← Complex.ofReal_sum, uniform_apply, ZMod.card,Grid]
  · rw [ite_eq_right H]
    unfold expU chi
    rw [show ∑ x : Grid M, ZMod.stdAddChar (u*x) = 0 from
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar _ H), smul_zero]

/-- Averages against conj character. Evaluation form instead of linear notation. -/
def fc (f : Grid M → ℂ) (u : Grid M) : ℂ := expU fun x => f x * chi (-u) x

lemma fc_lmul (f : Grid M → ℂ) (a : ℂ) (u : Grid M) :
    fc (fun x => a*f x) u = a*fc f u := by
  simp_rw [fc,mul_assoc]
  exact expU_lmul _ _

lemma fc_add (f g : Grid M → ℂ) (u : Grid M) :
    fc (fun x => f x+g x) u = fc f u+fc g u := by
  simp_rw [fc,add_mul]
  exact expU_add _ _

lemma fc_sum {ι : Type*} (s : Finset ι) (f : ι → Grid M → ℂ) (u : Grid M) :
    fc (fun x => ∑ i ∈ s, f i x) u = ∑ i ∈ s, fc (f i) u := by
  simp_rw [fc,Finset.sum_mul]
  exact expU_sum _ _

lemma fc_chi (u v : Grid M) : fc (chi v) u = if v=u then 1 else 0 := by
  simp_rw [fc,← chi_add', ← sub_eq_add_neg, expU_chi, sub_eq_zero]

lemma expU_coeff (f : Grid M → ℂ) (u : Grid M) :
    expU (fun x => f x*chi u x) = fc f (-u) := by rw [fc]; simp

lemma fc_neg_even (f : Grid M → ℂ) (h : f.Even) (u : Grid M) :
    fc f (-u) = fc f u := by
  unfold fc
  rw [← expU_reflect (fun x => f x*chi (-u) x)]
  simp_rw [neg_neg, h _, chi_neg',chi_neg, RingHomCompTriple.comp_apply]
  rfl

lemma fc_neg_real (f : Grid M → ℝ) (u : Grid M) :
    fc (fun x => (f x:ℂ)) (-u) = conj (fc (fun x => (f x:ℂ)) u) := by
  unfold fc
  simp_rw [expU_cx, ← Cx_conj, map_mul, chi_neg', Complex.conj_ofReal]

lemma real_fc_even (f : Grid M → ℝ) (h : f.Even) (u : Grid M) :
    (↑(fc (fun x => (f x:ℂ)) u).re:ℂ) = fc (fun x => (f x:ℂ)) u := by
  rw [← fc_neg_even (fun x => (f x:ℂ)) (fun x => by simp [h x]) u]
  have H := fc_neg_even (fun x => (f x:ℂ)) (fun x => by simp [h x]) u
  have he := fc_neg_real f u
  rw [H]
  have hi := congrArg Complex.im (H.symm.trans he)
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · simp
  · simp; linarith

lemma invert_fc (f : Grid M → ℂ) (x : Grid M) :
    ∑ u : Grid M, fc f u * chi u x = f x := by
  unfold fc expU
  simp only [Complex.real_smul, Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  have heq (y : Grid M) :
      ∑ u : Grid M, ↑(side M)*(f y*chi (-u) y)*chi u x =
        f y * expU fun u : Grid M => chi (x-y) u := by
    unfold expU; simp only [Complex.real_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u hu
    rw [chi_comm (x-y) u,chi_sub,chi_neg']
    ring
  simp_rw [heq,expU_chi,sub_eq_zero,mul_ite,mul_one,mul_zero]
  simp

lemma fc_mul_chi (f : Grid M → ℂ) (u v : Grid M) :
    fc (fun y => f y * chi v y) u = fc f (u-v) := by
  simp_rw [fc, mul_assoc, ← chi_add', neg_sub, ← sub_eq_add_neg]

lemma fc_prod (f g : Grid M → ℂ) (u : Grid M) :
    fc (fun y => f y * g y) u = ∑ v : Grid M, fc f v * fc g (u-v) := by
  calc
    _ = fc (fun y => ∑ v : Grid M, fc f v * (g y*chi v y)) u := by
      congr 1; funext y; rw [← invert_fc f y,Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by simp_rw [fc_sum,fc_lmul,fc_mul_chi]

lemma fc_right_translate (f : Grid M → ℂ) (a u : Grid M) :
    fc (fun y => f (y-a)) u = chi (-u) a * fc f u := by
  unfold fc; rw [← expU_translate (fun y => f (y-a)*chi (-u) y) a]
  simp_rw [add_sub_cancel_left,chi_add]
  rw [← expU_lmul]
  congr 1; funext y; ring

lemma fc_parseval (f : Grid M → ℂ) :
    ∑ u, ‖fc f u‖^2 = expU fun y => ‖f y‖^2 := by
  have hc (u : Grid M) :
      fc (fun y => conj (f y)) (-u) = conj (fc f u) := by
    unfold fc
    simp_rw [expU_cx,← Cx_conj,map_mul, chi_neg']
  have H := fc_prod f (fun y => conj (f y)) 0
  simp_rw [zero_sub,hc,Complex.mul_conj,← Complex.sq_norm] at H
  unfold fc at H
  rw [neg_zero] at H
  simp_rw [chi_zero_left,mul_one,expU_real,← Complex.ofReal_sum] at H
  exact Complex.ofReal_inj.mp H.symm

end FourierLLogL.Dyadic

end OAI
