import OAI.Analysis.FourierLLogL.Thermal.Update

/-! # Past observation profiles and posterior lower bound -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

variable {M : ℕ}
open scoped Classical

abbrev Profile (M : ℕ) := List (Form M × Grid M)

/-- Energy of a history against test input. -/
def sumE (s : Profile M) (x : Grid M) : ℝ := (s.map fun t => form t.1 (t.2-x)).sum
def mixForm (s : Profile M) : Form M := (s.map Prod.fst).sum
def tune (s : Profile M) (x : Grid M) := exp (-sumE s x)

def admissible (s : Profile M) (p : Node) (r : ℝ) :=
    ∃ x, x ∈ p.block M ∧ sumE s x ≤ r

def prefixE (s : Profile M) (p : Node) (x : Grid M) := if x∈p.block M then tune s x else 0

lemma tune_pos (s : Profile M) (x : Grid M) : 0 < tune s x := exp_pos _
lemma prefixE_nonneg (s : Profile M) (p : Node) (x : Grid M) : 0 ≤ prefixE s p x := by
  unfold prefixE; split_ifs
  exact (tune_pos _ _).le
  exact le_rfl

lemma tune_cons (s : Profile M) (A : Form M) (x y : Grid M) :
    tune ((A,x)::s) y = boltz A (x-y)*tune s y := by
  simp only [tune,sumE,List.map_cons,List.sum_cons,boltz, ← exp_add]
  congr 1; ring

lemma mix_cons (s : Profile M) (A : Form M) (x : Grid M) :
    mixForm ((A,x)::s) = A+mixForm s := by simp [mixForm]

lemma mix_bound {s : Profile M} {A : Form M} (h : ∀ i∈s, i.1 ≤ A) (x : Grid M) :
    mixForm s x ≤ s.length*A x := by
  induction s with
  | nil =>
    unfold mixForm
    simp
  | cons i s ih =>
    obtain ⟨a,y⟩ := i
    rw [mix_cons]
    have hx := ih (by intro i hi; exact h i (List.mem_cons_of_mem _ hi))
    have hh := h (a,y) List.mem_cons_self x
    simp only [Pi.add_apply,List.length_cons]
    change a x ≤ _ at hh
    push_cast; linarith

lemma mix_nonneg {s : Profile M} (h : ∀ i∈s, 0 ≤ i.1) :
    0 ≤ mixForm s := by
  induction s with
  | nil => simp [mixForm]
  | cons i s ih =>
    obtain ⟨a,y⟩ := i; rw [mix_cons]
    exact add_nonneg (h (a,y) List.mem_cons_self) (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

lemma sumE_compare {s : Profile M} (x y : Grid M) (h : ∀ i∈s, 0 ≤ i.1) :
    sumE s y ≤ 2*(sumE s x + form (mixForm s) (x-y)) := by
  induction s with
  | nil => simp [mixForm,sumE,form_zero]
  | cons i s ih =>
    obtain ⟨a,z⟩ := i
    have hh := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have hx : 0 ≤ a := h (a,z) List.mem_cons_self
    simp only [mix_cons, sumE, List.map_cons, List.sum_cons, form_add]
    unfold sumE at hh
    have H := form_triangle hx (z-x) (x-y)
    rw [sub_add_sub_cancel] at H
    linarith

lemma profile_envelope {s : Profile M} (h : ∀ i∈s, 0 ≤ i.1) (x : Grid M) :
    ‖fc (fun y => (↑(tune s y):ℂ)) x‖ ≤ q (mixForm s) x := by
  induction s generalizing x with
  | nil =>
    rw [show mixForm ([]:Profile M)=0 from by simp [mixForm]]
    apply le_of_eq
    convert norm_fc_translate_boltz (M:=M) (le_refl (0:Form M)) 0 x using 1
    simp [boltz,tune,sumE,form_zero]
  | cons i s ih =>
    obtain ⟨a,y⟩ := i
    simp_rw [mix_cons,tune_cons,Complex.ofReal_mul,fc_prod,q_add]
    apply le_trans (norm_sum_le _ _)
    refine Finset.sum_le_sum fun i _ => ?_
    have hx : 0 ≤ a := h (a,y) List.mem_cons_self
    have hh := ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) (x-i)
    rw [norm_mul,norm_fc_translate_boltz hx]
    exact mul_le_mul_of_nonneg_left hh (q_nonneg hx _)

private lemma close_kept {p : Node} (hp : p.ok M) {x v : Grid M} (hx : x ∈ p.block M)
    (h : Dyadic.diam v < p.len/2) :
    x+v ∈ p.block M ∨ x-v ∈ p.block M := by
  have he (v : Grid M) (hv : pos v < p.len/2) :
      x+v ∈ p.block M ∨ x-v ∈ p.block M := by
    have hh1 : p.idx M ≤ x.val ∧ x.val < p.idx M+p.wid M := by
      rw [mem_block_iff hp.2] at hx; unfold idx wid; rw [add_mul,one_mul] at hx; exact hx
    have hh2 : 2*v.val < p.wid M := by
      have H := side_pos M
      have he : p.len = (p.wid M : ℝ)*side M := by
        unfold wid; rw [descale hp.2]; push_cast; ring
      rw [he,pos] at hv
      have hi : 2*(v.val : ℝ)< p.wid M := by nlinarith
      exact_mod_cast hi
    have heq (x : Grid M) :
        x∈p.block M ↔ p.idx M ≤ x.val ∧ x.val < p.idx M+p.wid M := by
      unfold idx wid; rw [mem_block_iff hp.2,add_mul,one_mul]
    rw [heq,heq]
    by_cases H : x.val+v.val < p.idx M+p.wid M
    · left; rw [ZMod.val_add_of_lt (H.trans_le (p.fitting hp.1 hp.2))]
      omega
    right; rw [ZMod.val_sub (by omega : v.val ≤ x.val)]
    omega
  rw [diam_min,min_lt_iff] at h
  rcases h with h|h
  · exact he v h
  · simpa only [sub_neg_eq_add,← sub_eq_add_neg] using (he (-v) h).symm

private lemma even_prob (A : Form M) (p : Grid M → Prop) :
    (label A).prob (fun x => p (-x)) = (label A).prob p := by
  rw [prob_eq,prob_eq]
  apply Fintype.sum_equiv (Equiv.neg (Grid M))
  intro i
  simp only [Equiv.neg_apply,label_apply,K_even _ _]

private lemma label_node_inside {p : Node} (hp : p.ok M) {A : Form M}
    (hA : S M (1000*p.invlen) ≤ A) (h : 1000*p.invlen ≤ 2^M)
    (x : Grid M) (hx : x∈p.block M) :
    1/4 ≤ (label A).prob (fun z => x+z ∈ p.block M) := by
  let R := p.invlen; let r := p.len/2; let P := label A
  let u (z : Grid M) : Prop := Dyadic.diam z < r
  let v (z : Grid M) : Prop := x+z ∈ p.block M
  have hR : 1 ≤ R := p.invlen_ge
  have hr : 0 < r := by unfold r; have := p.len_pos; positivity
  have he : P.prob (fun x => ¬ u x) ≤ 1/2 := by
    have he : (P.prob (fun x => ¬u x))*r^2 ≤ 100/(1000*R)^2 := by
      apply le_trans _ (S_variance _ (by linarith) h _ hA)
      unfold prob
      rw [← Ex_mul]
      refine Ex_mono _ fun i => ?_
      dsimp only; split_ifs with H
      · rw [zero_mul]; positivity
      · rw [one_mul]
        apply pow_le_pow_left₀ hr.le _
        exact not_lt.mp H
    have ht : 100/(1000*R)^2 ≤ (1/2)*r^2 := by
      unfold R r; rw [rinv]
      have h0 := p.len_pos
      field_simp; nlinarith
    exact le_of_mul_le_mul_right (he.trans ht) (by positivity)
  have hb : P.prob u ≤ P.prob v + (P.prob fun z => v (-z)) := by
    unfold prob; rw [← Ex_add]; refine Ex_mono _ fun i => ?_
    by_cases hi : u i
    · have HH : v i ∨ v (-i) := by
        simpa only [v,sub_eq_add_neg] using close_kept hp hx hi
      rcases HH with HH|HH <;> simp only [hi,HH,ite_true] <;>
        split_ifs <;> norm_num
    · simp only [hi,ite_false]; split_ifs <;> norm_num
  rw [prob_compl] at he
  rw [even_prob A v] at hb
  change _ ≤ P.prob v; linarith

lemma posterior_denominator {p : Node} (hp : p.ok M) {A : Form M}
    (hA : S M (1000*p.invlen) ≤ A) (h : 1000*p.invlen ≤ 2^M)
    (s : Profile M) {r : ℝ} (hr : admissible s p r)
    (hn : ∀ i∈s, 0 ≤ i.1) (hh : (2:ℝ) • mixForm s ≤ A) :
    exp (- (2*r)-F A)/4 ≤ expU (prefixE s p) := by
  obtain ⟨x,hx,h1⟩ := hr
  let Q := label A
  let c := exp (- (2*r)-F A)
  have hc : 0 < c := exp_pos _
  have HE (y : Grid M) : c*(K A y * (if x+y∈p.block M then 1 else 0)) ≤
      prefixE s p (x+y) := by
    unfold prefixE; split_ifs with hiv
    · rw [mul_one,K_eq,tune]
      unfold c; rw [← exp_add]; apply Real.exp_monotone
      have hi := sumE_compare x (x+y) hn
      have h2 := form_mono hh (x-(x+y))
      rw [form_smul, show x-(x+y)=-y by ring,form_even A y] at h2
      rw [show x-(x+y)=-y by ring] at hi
      linarith
    · simp
  have hh' := Ex_mono (uniform _) HE
  simp only [Ex_lmul,← expU_ex,expU_translate,← label_ex] at hh'
  apply le_trans _ hh'
  have hh2 := label_node_inside hp hA h x hx
  let f (y : Grid M) := if x+y∈p.block M then (1:ℝ) else 0
  have Heq : (label A).prob (fun z => x+z∈p.block M)=(label A).Ex f := by

    rw [prob_eq]; simp [f,Ex]
  rw [Heq] at hh2
  change c/4 ≤ c*(label A).Ex f
  nlinarith

end FourierLLogL.Dyadic.Thermal

end OAI
