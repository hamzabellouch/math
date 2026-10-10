import OAI.Analysis.FourierLLogL.Compress.Freeze
import OAI.Analysis.FourierLLogL.Finite.Complex

open Set Function Filter
open scoped BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Real Law
variable {A G Θ I Ω : Type} [Fintype A] [Fintype G] [AddCommGroup G]
    [Fintype Θ] [Fintype I] [DecidableEq I] [Fintype Ω]
set_option linter.unusedSectionVars false

lemma char_neg (χ : AddChar G ℂ) (hn : ∀ x, ‖χ x‖ = 1) (x : G) :
    χ (-x) = conj (χ x) := by
  apply mul_left_cancel₀ (a := χ x) (by intro h; have H := hn x; rw [h,norm_zero] at H; norm_num at H)
  rw [← χ.map_add_eq_mul,Complex.mul_conj,← Complex.sq_norm, hn]
  simp

lemma char_sum (χ : AddChar G ℂ) (f : I → G) :
    χ (∑ i, f i) = ∏ i, χ (f i) := by
  classical
  suffices H : ∀ s : Finset I, χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) from H _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.prod_insert hi,Finset.sum_insert hi,χ.map_add_eq_mul,ih]

lemma heat_prod (tag : A→G) (c : G→ℝ) (Q : Law Θ) (χ : Θ→AddChar G ℂ)
    (hn : ∀ t x, ‖χ t x‖=1)
    (hc : ∀ g, ((exp (-c g) : ℝ):ℂ)=Q.Cx (fun t => χ t g))
    (p : I→Law A) (z : G) :
    (pack p).Ex (fun x => exp (-c (z-tot tag x))) ≤
      Q.Ex (fun t => ∏ i, ‖(p i).Cx (fun a => χ t (tag a))‖) := by
  let f (x : I→A) := exp (-c (z-tot tag x))
  have H (x : I→A) (t : Θ) :
      χ t (z-tot tag x) = χ t z * ∏ i, conj (χ t (tag (x i))) := by
    rw [sub_eq_add_neg,(χ t).map_add_eq_mul,char_neg (χ t) (hn t)]
    unfold tot
    rw [char_sum,map_prod]
  let C (i : I) (t : Θ) := (p i).Cx fun a => χ t (tag a)
  have heq :
      (↑((pack p).Ex f) : ℂ) =
        Q.Cx fun t => χ t z * ∏ i, conj (C i t) := by
    rw [← Cx_ofReal]; unfold f
    simp_rw [hc,H]
    rw [Cx_swap]
    apply congrArg

    funext t
    rw [Cx_lmul,Cx_prod p (fun _ x => conj (χ t (tag x)))]
    simp_rw [Cx_conj]; rfl
  have ht := Cx_norm Q (fun t => χ t z * ∏ i, conj (C i t))
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at ht
  simp_rw [norm_mul,Complex.norm_prod,hn,one_mul,Complex.norm_conj] at ht
  exact le_trans (le_abs_self _) ht

/-- Defect between two letter phases. -/
def defect (tag : A → G) (χ : Θ → AddChar G ℂ) (a b : A) (t : Θ) :=
  1 - (χ t (tag a-tag b)).re

lemma defect_nonneg (tag : A → G) (χ : Θ → AddChar G ℂ) (hn : ∀ t x, ‖χ t x‖=1) (a b t) :
    0 ≤ defect tag χ a b t := by
  unfold defect
  have H := Complex.abs_re_le_norm (χ t (tag a-tag b))
  rw [hn] at H; linarith [(abs_le.mp H).2]

lemma defect_mean (tag : A → G) (χ : Θ → AddChar G ℂ) (hn : ∀ t x, ‖χ t x‖=1)
    (p : Law A) (t) :
    p.Ex (fun a => p.Ex (fun b => defect tag χ a b t)) =
      1- ‖p.Cx (fun a => χ t (tag a))‖^2 := by
  unfold defect
  have h (a b : A) :
      (χ t) (tag a-tag b) = χ t (tag a)*conj (χ t (tag b)) := by
    rw [sub_eq_add_neg,(χ t).map_add_eq_mul,char_neg _ (hn t)]
  simp_rw [h,Ex_sub,Ex_const,sq_norm_Cx]

/-- If the characteristic product has large integral, then it has large volume at the
corresponding defect level. -/
lemma phase_region (Q : Law Θ) (f : I → Θ → ℝ) (hf : ∀ i t, 0 ≤ f i t ∧ f i t ≤ 1)
    {E : ℝ} (he : 1 ≤ E) (h : exp (-(2*E)) ≤ Q.Ex fun t => ∏ i, f i t) :
    let A (x : Θ) := ∑ i, (1-f i x ^ 2)
    exp (-(3*E)) ≤ Q.prob fun x => A x ≤ 8*E := by
  classical
  intro D
  let S (x : Θ) := D x ≤ 8*E
  have h1 (x : ℝ) (hp : 0 ≤ x) : x ≤ exp (-(1-x^2)/2) := by
    have hi := Real.add_one_le_exp (-(1-x^2))
    have hh := Real.exp_pos (-(1-x^2)/2)
    rw [show -(1-x^2)=-(1-x^2)/2+ -(1-x^2)/2 by ring,
      Real.exp_add] at hi
    nlinarith
  have hx (x : Θ) :
      (∏ i, f i x) ≤ (if S x then (1:ℝ) else 0)+ exp (-(4*E)) := by
    split_ifs with H
    · apply le_trans (b:=∏ i : I,(1:ℝ)) (Finset.prod_le_prod₀ (fun i _ => (hf i x).1)
        (fun i _ => (hf i x).2))
      simp [exp_nonneg]
    · apply le_trans (b:=∏ i, exp (-(1-f i x^2)/2)) (Finset.prod_le_prod₀
        (fun i _ => (hf i x).1) (fun i _ => h1 _ (hf _ _).1))
      have heq : ∑ i, (-(1-f i x^2)/2) = -(D x)/2 := by
        unfold D; rw [← Finset.sum_div,Finset.sum_neg_distrib]
      rw [← Real.exp_sum,heq,zero_add]
      apply exp_monotone; unfold S at H; linarith
  have heq : Q.Ex (fun x => if S x then (1:ℝ) else 0) = Q.prob S := by
    unfold prob
    congr 1
  have H := Q.Ex_mono hx
  rw [Ex_add,heq,Ex_const] at H
  have hb : 2 ≤ exp E := le_trans (by linarith) (Real.add_one_le_exp E)
  have H1 := exp_nonneg (-(4*E))
  have H2 := exp_nonneg (-(3*E))
  have H3 : exp (-(2*E)) = exp (-(3*E))*exp E := by rw [← exp_add]; congr 1; ring
  have H4 : exp (-(3*E)) = exp (-(4*E))*exp E := by rw [← exp_add]; congr 1; ring
  change _ ≤ Q.prob S
  nlinarith


lemma log_gap (P : Law A) [Nonempty A]
    (s : Finset A)
    (hp : (1/2:ℝ) ≤ P.prob fun x => x ∈ s) :
    log (Fintype.card A) - log (s.card:ℝ) ≤
      2*(log (Fintype.card A)-P.entropy+log 2) := by
  classical
  let f (x : A) : Bool := decide (x ∈ s)
  let Q := P.send f
  have h1 : P.entropy = Q.entropy +
      Q.Ex fun b => (P.after f b).entropy := by
    have hI : P.H (fun x => (x,f x)) = P.entropy := by
      rw [← H_self]; apply H_partition; simp
    rw [← hI,H_pair_chain,Hcond_after]
    simp_rw [H_self]
    rfl
  have hh : Q true = P.prob (fun x => x ∈ s) := by
    unfold Q; rw [ send_apply]
    congr; simp [f]
  have hPos : 0 < Q true := by rw [hh]; linarith
  have hcard : 0 < (s.card:ℝ) := by
    obtain ⟨x,hx,_⟩ := (send_pos_iff P f true).mp hPos
    have ht : x ∈ s := by simpa only [f,decide_eq_true_eq] using hx
    exact_mod_cast Finset.card_pos.mpr ⟨x,ht⟩
  let L := log (Fintype.card A)
  let T := log (s.card:ℝ)
  have hT : T ≤ L := Real.log_le_log hcard (by exact_mod_cast Finset.card_le_univ _)
  have H : (P.after f true).entropy ≤ T :=
    entropy_le_log_size _ s fun x hx => by
      simpa only [f,decide_eq_true_eq] using ((after_mem hPos).mp hx).1
  have H' : (P.after f false).entropy ≤ L := entropy_le_log_card _
  have Hb : Q.entropy ≤ log 2 := by simpa using entropy_le_log_card Q
  have HI : Q false + Q true = 1 := by simpa [Fintype.sum_bool,add_comm] using Q.total
  rw [h1,Ex,Fintype.sum_bool]
  change L-T ≤ _
  have : L-T ≤ 2*(L-(Q.entropy+
      (Q true*(P.after f true).entropy + Q false*(P.after f false).entropy))+log 2) := by
    have hPos' := Q.nonneg false
    rw [← hh] at hp
    nlinarith [mul_le_mul_of_nonneg_left H hPos.le,
      mul_le_mul_of_nonneg_left H' hPos', show Q false * L+ Q true * L=L by rw [← add_mul,HI,one_mul]]
  exact this


lemma prob_half (P : Law Ω) (f : Ω → ℝ) (hn : ∀ x, 0 ≤ f x) (E : ℝ) (he : 0 < E)
    (hp : P.Ex f ≤ E) :
    (1/2:ℝ) ≤ P.prob fun x => f x ≤ 2*E := by
  classical
  let p (x : Ω) := f x ≤ 2*E
  let F (x : Ω) := if ¬p x then 1 else (0:ℝ)
  have hh : P.Ex F = P.prob (fun x => ¬p x) := by
    apply congrArg (P.Ex)
    funext x; unfold F
    split_ifs <;> simp_all
  rw [prob_compl] at hh
  have hi (x : Ω) : 2*E * F x ≤ f x := by
    unfold F p; split_ifs with H
    · simp [hn x]
    · simp; linarith
  have H := (P.Ex_mono hi).trans hp
  rw [Ex_lmul, hh] at H
  change _ ≤ P.prob p
  nlinarith

def small_defects (tag : A → G) (χ : Θ → AddChar G ℂ) (Q : Law Θ)
    (L : ℝ) (s : Finset A) (a : A) (F : ℝ) : Prop :=
  ∀ p : Law A, (∀ x, 0 < p x → x ∈ s) →
    exp (-F) ≤ Q.Ex fun t => exp ((-L)*p.Ex (fun x => defect tag χ x a t))

lemma alignment (tag : A → G) (c : G → ℝ) (Q : Law Θ) (χ : Θ → AddChar G ℂ)
    (hn : ∀ t x, ‖χ t x‖=1)
    (hc : ∀ g, ((exp (-c g) : ℝ):ℂ)=Q.Cx (fun t => χ t g))
    (p : I → Law A) [Nonempty I] [Nonempty A] (z : G)
    (F D L : ℝ) (he : 1 ≤ F) (hd : 0 < D) (hL : 0 ≤ L)
    (hL' : L ≤ Fintype.card I)
    (hz : exp (-(2*F)) ≤ (pack p).Ex (fun x => exp (-c (z-tot tag x))))
    (hs : ∑ i, (log (Fintype.card A)-entropy (p i)) ≤ 2*(Fintype.card I*D)) :
    ∃ (a : A) (s : Finset A), s.Nonempty ∧
      log (Fintype.card A) - log (s.card:ℝ) ≤ 8*D+2 ∧
      small_defects tag χ Q L s a (35*F) := by
  classical
  let f i (t : Θ) := ‖(p i).Cx (fun a => χ t (tag a))‖
  have hf1 (i : I) (t : Θ) : f i t ≤ 1 := norm_Cx_unit _ _ fun x => (hn _ _).le
  have hf0 (i : I) (t : Θ) : 0 ≤ f i t := norm_nonneg _
  let W (x : Θ) : Prop := ∑ i, (1 - f i x ^ 2) ≤ 8*F
  have hh : exp (-(3*F)) ≤ Q.prob W := phase_region Q f (fun i t => ⟨hf0 _ _,hf1 _ _⟩)
    he (hz.trans (heat_prod _ _ _ _ hn hc p z))
  let P := Q.condP W
  have hW : 0 < Q.prob W := lt_of_lt_of_le (exp_pos _) hh
  let g (i : I) := P.Ex fun t => 1-f i t^2
  let A' (i : I) := log (Fintype.card A)-entropy (p i)
  have hgp (i : I) : 0 ≤ g i := Ex_nonneg P fun t => by
    nlinarith [hf1 i t,hf0 i t]
  let T := (Fintype.card I:ℝ)
  have ht : 0 < T := by unfold T; positivity
  have hg : (uniform I).Ex g ≤ 8*F/T := by
    have hi : ∑ i, g i ≤ 8*F := by
      unfold g
      rw [← Ex_finset_sum]
      refine le_trans (b:=P.Ex fun _ => 8*F) (P.Ex_mono_mem fun x hx => ?_) (P.Ex_const _).le
      exact ((Law.condP_mem hW).mp hx).1
    simp_rw [Ex,uniform_apply,← Finset.mul_sum]
    exact le_trans (mul_le_mul_of_nonneg_left hi (inv_pos.mpr ht).le)
      (by dsimp [T]; rw [← div_eq_inv_mul])
  have ha : (uniform I).Ex A' ≤ 2*D := by
    simp_rw [Ex,uniform_apply,← Finset.mul_sum,← div_eq_inv_mul]
    exact (div_le_iff₀ ht).mpr (by dsimp only [T,A']; linarith)
  obtain ⟨i, _,hi,hi'⟩ := average_two_below (uniform I) g A' (fun i _ => hgp i)
    (fun i _ => sub_nonneg.mpr (entropy_le_log_card _)) (8*F/T) (2*D)
    (by have := lt_of_lt_of_le zero_lt_one he; positivity) (by positivity) hg ha
  let R := p i
  let G (x y : A) := P.Ex (defect tag χ x y)
  have HG : R.Ex (fun y => R.Ex fun x => G x y) ≤ 16*F/T := by
    have Heq : R.Ex (fun y => R.Ex fun x => G x y) = g i := by
      rw [Ex_swap]
      unfold G
      simp_rw [Ex_swap R P]
      unfold g f
      simp_rw [defect_mean _ _ hn]
      rfl
    rw [Heq]
    exact hi.trans (le_of_eq (by ring))
  obtain ⟨a,ha',ha''⟩ := R.exists_le_Ex (fun y => R.Ex fun x => G x y)
  let s := Finset.univ.filter fun x => G x a ≤ 2*(16*F/T)
  have ha0 : R.Ex (fun x => G x a) ≤ 16*F/T := ha''.trans HG
  have hp : (1/2:ℝ) ≤ R.prob fun x => x ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact prob_half _ _ (fun x => Ex_nonneg _ (fun y => defect_nonneg _ _ hn x a y))
      _ (by have := lt_of_lt_of_le zero_lt_one he; positivity) ha0
  obtain ⟨x,hx,_⟩ := (prob_pos_iff R (fun x => x∈s)).mp
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hp)
  refine ⟨a,s,⟨x,hx⟩,(log_gap R s hp).trans ?_,?_⟩
  · change log (Fintype.card A) - entropy R ≤ _ at hi'
    have hi := Real.log_le_sub_one_of_pos (x:=2) (by norm_num)
    linarith
  intro V hv
  let v (t : Θ) := V.Ex fun x => defect tag χ x a t
  have hB : P.Ex v ≤ 32*F/T := by
    unfold v; rw [Ex_swap P V]
    refine le_trans (b:=V.Ex fun _ => 32*F/T) (V.Ex_mono_mem fun x hx => ?_)
      (V.Ex_const _).le
    have H := (Finset.mem_filter.mp (hv x hx)).2
    change G x a ≤ _
    exact H.trans (le_of_eq (by ring))
  have H1 : P.Ex (fun t => exp ((-L)* v t)) ≥ exp (-(32*F)) := by
    have H := Ex_exp P (fun t => (-L)*v t)
    rw [Ex_lmul] at H
    apply le_trans _ H
    apply exp_monotone
    have hbp := (le_div_iff₀ ht).mp hB
    change L ≤ T at hL'
    have hg1 : 0 ≤ P.Ex v :=
      P.Ex_nonneg fun t => V.Ex_nonneg fun x => defect_nonneg tag χ hn x a t
    nlinarith
  calc
    exp (-(35*F)) = exp (-(3*F))*exp (-(32*F)) := by rw [← exp_add]; congr 1; ring
    _ ≤ Q.prob W * P.Ex (fun t => exp ((-L)*v t)) :=
      mul_le_mul hh H1 (exp_nonneg _) hW.le
    _ ≤ _ := by
      dsimp only [P]
      rw [prob_mul_Ex_condP]
      apply Q.Ex_mono; intro t; split_ifs <;> first | exact le_rfl | exact exp_nonneg _

end FourierLLogL.Compress

end OAI
