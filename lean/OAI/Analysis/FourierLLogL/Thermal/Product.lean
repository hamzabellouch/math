import OAI.Analysis.FourierLLogL.Thermal.Side
import OAI.Analysis.FourierLLogL.Dyadic.Span
import OAI.Analysis.FourierLLogL.Compress.Thinning

/-! # Side-labeled greedy logarithmic sumset bound -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period

variable {M l : ℕ}
open scoped Classical

lemma log_shift_bound (s : ℝ) (h : |s| ≤ 1/2) : s-2*s^2 ≤ log (1+s) := by
  obtain ⟨hx,hx'⟩ := abs_le.mp h
  have hh : 0 < 1+s := by linarith
  have H := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
  rw [Real.log_inv] at H
  apply le_trans (b:= -( (1+s)⁻¹-1))
  · apply le_of_mul_le_mul_right _ hh
    rw [neg_mul,sub_mul,sub_mul,inv_mul_cancel₀ hh.ne',one_mul]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (2*s+1)) (sq_nonneg s)]
  linarith

private def factorQ (c : ℝ) (v : ℂ) (i x : Grid l) : ℝ :=
    1 + c*(v*chi i x).re

private lemma test_abs (v : ℂ) (i x : Grid l) (h : ‖v‖ ≤ 1) :
    |(v * chi i x).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (by rw [norm_mul,norm_chi,mul_one]; exact h)

private lemma factor_bounds (β : ℝ) (v : ℂ) (i x : Grid l) (hp : 0 ≤ β) (hh : β ≤ 1)
    (hv : ‖v‖ ≤ 1) :
    0 < factorQ (β/4) v i x ∧
      β/4 * (v*chi i x).re - β^2/8 ≤ log (factorQ (β/4) v i x) := by
  have he := test_abs v i x hv
  let t := β/4 * (v*chi i x).re
  have hi : |t| ≤ β/4 := by
    unfold t; rw [abs_mul,abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) he
  have hX := abs_le.mp hi
  unfold factorQ
  change 0 < 1+t ∧ t-_ ≤ _
  have hl := log_shift_bound t (hi.trans (by linarith))
  constructor
  · linarith [hX.1]
  apply le_trans _ hl
  nlinarith [sq_abs t,abs_nonneg t]

private def Qp (s : Finset (Grid l)) (c : ℝ) (v : Grid l → Grid M → ℂ)
    (i : Grid l) (z : Grid M) := ∏ j∈s, factorQ c (v j z) j i

private lemma q_exp_constant {f : Grid l → ℝ} :
    (↑(expU f):ℂ) = fc (fun i => (↑(f i):ℂ)) 0 := by
  rw [fc,← expU_real]; simp_rw [neg_zero,chi_zero_left,mul_one]

private lemma q_step {s : Finset (Grid l)} {c : ℝ} {v : Grid l → Grid M → ℂ} {x : Grid l}
    (hx : ¬ enclosed s 1 x) {z : Grid M}
    (h : spanned s (fun i => (↑(Qp s c v i z):ℂ)))
    (h' : expU (fun i => Qp s c v i z) = 1) :
    spanned (insert x s) (fun i => (↑(Qp (insert x s) c v i z):ℂ)) ∧
      expU (fun i => Qp (insert x s) c v i z) = 1 := by
  have HE (i : Grid l) :
      (↑(Qp (insert x s) c v i z):ℂ) =
        (↑(Qp s c v i z):ℂ) * (1+ (↑(((c:ℂ)*v x z*chi x i).re):ℂ)) := by
    unfold Qp
    rw [Finset.prod_insert (fun hh => hx (enclosed_mem s hh)),mul_comm]
    push_cast
    rw [mul_assoc,Complex.re_ofReal_mul,factorQ]; push_cast; rfl
  obtain ⟨ht,ht'⟩ := span_augment h ((c:ℂ)*v x z) x hx

  constructor
  · simp_rw [HE]; exact ht
  apply Complex.ofReal_inj.mp
  rw [q_exp_constant]
  simp_rw [HE]
  rw [ht',← q_exp_constant,h']

private lemma span_collection (s : Finset (Grid l)) (c : ℝ) (v : Grid l → Grid M → ℂ) :
    ∃ t ⊆ s, (∀ x∈s, enclosed t 1 x) ∧ ∀ z, expU (fun i => Qp t c v i z)=1 := by
  let R := fun t : Finset (Grid l) => ∀ z, spanned t (fun i => (↑(Qp t c v i z):ℂ)) ∧
    expU (fun i => Qp t c v i z)=1
  suffices HH : ∀ k : ℕ, ∀ t ⊆ s, s.card-t.card=k → R t →
      ∃ t ⊆ s, (∀ x∈s, enclosed t 1 x) ∧ ∀ z, expU (fun i => Qp t c v i z)=1 by
    refine HH _ ∅ (by simp) rfl fun z => ⟨?_,?_⟩
    · simp only [Qp,Finset.prod_empty, Complex.ofReal_one]; exact spanned_one _
    simp only [Qp,Finset.prod_empty,expU_ex,Ex_const]
  intro k; induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t ht hk hr
    by_cases H : ∀ x∈s, enclosed t 1 x
    · exact ⟨t,ht,H,fun z => (hr z).2⟩
    push Not at H
    obtain ⟨x,hx,H⟩ := H
    have hh : insert x t ⊆ s := Finset.insert_subset hx ht
    refine ih (s.card-(insert x t).card) ?_ _ hh rfl fun z => q_step H (hr z).1 (hr z).2
    have he := Finset.card_le_card hh
    rw [Finset.card_insert_of_notMem (fun hh => H (enclosed_mem t hh))] at *
    omega

lemma conditional_if_ex {α β : Type} [Fintype α] [Fintype β]
    (P : Law α) (k : α → Law β) (Q : α → Prop) (f : α → β → ℝ) :
    (P.withNext k).Ex (fun i => if Q i.1 then f i.1 i.2 else 0) =
      P.Ex (fun a => if Q a then (k a).Ex (f a) else 0) := by
  rw [Ex_withNext]; refine congrArg _ (funext fun a => ?_)
  by_cases h : Q a <;> simp only [h,ite_false,ite_true,Ex_const]

private lemma append_cost {p : Node} {P : Law (Grid M)} {B : Bool} {A : Form M}
    {hl : l ≤ M} {s : Finset (Grid l)} {v : Grid l → Grid M → ℂ} {β : ℝ} (h0 : 0 ≤ β) (hb : β ≤ 1)
    (H : biases P p A hl s B v β) (i : Grid l) (hi : i∈s) :
    let C (x : Grid M) : Prop := x∈(p.child B).block M
    β^2/8 ≤ (P.withNext (channel A)).Ex fun xz =>
      if C xz.1 then log (factorQ (β/4) (v i xz.2) i (cut hl xz.1)) else 0 := by
  intro C; let L := channel A; let T := P.withNext L
  let f (xz : Grid M × Grid M) := if C xz.1 then (v i xz.2 * chi i (cut hl xz.1)).re else 0
  have H' : β ≤ T.Ex f := by
    unfold T f; rw [conditional_if_ex P L C (fun y z => (v i z * chi i (cut hl y)).re)]; have he := H.2 i hi
    simp_rw [cut_chi] at he
    exact he
  calc
    _ ≤ (β/4)* T.Ex f - β^2/8 := by nlinarith
    _ = T.Ex (fun xz => β/4*f xz - β^2/8) := by
      rw [Ex_sub,Ex_const,Ex_lmul]
    _ ≤ _ := Ex_mono T fun x => by
      unfold f
      split_ifs
      · exact (factor_bounds β _ _ _ h0 hb (H.1 _ _)).2
      nlinarith

lemma cheap_span {p p' : Node} {a : Grid M → ℝ} (hp : p.ok M) (hv : p.below p')
    {n : ℕ} {h err : ℝ} {A : Form M} (H : Certified h err n p' A)
    {P : Law (Grid M)} (ht : PieceLaw p a P) (hl : l ≤ M) (hh : M-l ≤ p.lev)
    {d : ℝ} (h1 : ∀ x, a x ≤ exp d) (hm : exp (-d) ≤ p.avg a) {B : Bool}
    {s : Finset (Grid l)} {v : Grid l → Grid M → ℂ} {β : ℝ} (h0 : 0 ≤ β) (hb : β ≤ 1)
    (HG : biases P p A hl s B v β) :
    ∃ t : Finset (Grid l), (∀ x∈s, enclosed t 1 x) ∧
      t.card*(β^2/8) ≤ 2*d + log p.invlen - log ((2:ℝ)^(M-l)) + F A - log p'.invlen + 301 := by
  obtain ⟨t,htt,hE,hq⟩ := span_collection s (β/4) v
  let Q := Qp t (β/4) v
  let C (x : Grid M) : Prop := x∈(child p B).block M
  let U := P.withNext (channel A)
  have hQ (i z) : 0 < Q i z := Finset.prod_pos fun x _ => (factor_bounds _ _ _ _ h0 hb (HG.1 _ _)).1
  let f (i : Grid l) (x : Grid M × Grid M) := if C x.1 then
    log (factorQ (β/4) (v i x.2) i (cut hl x.1)) else 0
  refine ⟨t,hE,le_trans ?_ (product_entropy_bound hp hv H ht hl hh h1 hm B Q hQ fun z => (hq z).le)⟩
  change _ ≤ U.Ex (fun x => if C x.1 then _ else _)
  have HE (x : Grid M × Grid M) : (if C x.1 then log (Q (cut hl x.1) x.2) else 0) = ∑ i∈t, f i x := by
    unfold Q Qp f
    split_ifs with hh
    · rw [Real.log_prod]
      exact fun i _ => (factor_bounds _ _ _ _ h0 hb (HG.1 _ _)).1.ne'
    · simp
  simp_rw [HE,Ex_finset_sum]
  calc
    _ = ∑ _i∈t, β^2/8 := by simp
    _ ≤ _ := Finset.sum_le_sum fun i hi => append_cost h0 hb HG i (htt hi)

lemma sumset_est {s t : Finset (Grid l)} (h : ∀ x∈s, enclosed t 1 x) (n : ℕ) :
    Compress.lnS (Fin n) (fun x : s => (x:Grid l)) ≤ t.card * log (2*(n:ℝ)+1) := by
  let S := Compress.sums (Fin n) (fun x : s => (x:Grid l))
  have Hi : S ⊆ palace t n := by
    intro i hi
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    simpa [Compress.tot] using enclosed_sum t (fun i => (f i:Grid l)) (fun i => h _ (f i).property)
  have HE := (Finset.card_le_card Hi).trans (palace_size _ _)
  change log (S.card:ℝ) ≤ _
  by_cases H : S.card=0
  · simp only [H,Nat.cast_zero,log_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by have H := Nat.cast_nonneg (α:=ℝ) n; linarith))
  · have Hh : 0 < (S.card:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero H
    have HE' := log_le_log Hh (by exact_mod_cast HE : (S.card:ℝ) ≤ (2*(n:ℝ)+1)^t.card)
    rwa [log_pow] at HE'

end FourierLLogL.Dyadic.Thermal

end OAI
