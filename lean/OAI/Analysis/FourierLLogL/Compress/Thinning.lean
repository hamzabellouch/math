import OAI.Analysis.FourierLLogL.Compress.ThinChoice
/-! # Thinned coupling -/

open Function Set Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A G Ω I : Type} [Fintype A] [Fintype G] [Fintype Ω] [Fintype I] [DecidableEq I]
    [AddCommGroup G] [DecidableEq G]
set_option linter.unusedSectionVars false

def sums (I : Type) [Fintype I] [DecidableEq I] (tag : A → G) : Finset G :=
  Finset.univ.image (tot tag : (I→A) → G)

def lnS (I : Type) [Fintype I] [DecidableEq I] (tag : A → G) :=
  log ((sums I tag).card)

lemma lnS_bound (P : Law Ω) (X : Ω → I → A) (tag : A → G) :
    P.H (fun x => tot tag (X x)) ≤ lnS I tag := by
  classical
  refine entropy_le_log_size _ _ fun x hx => ?_
  obtain ⟨a,rfl,ha⟩ := (send_pos_iff _ _ _).mp hx
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma lnS_nonneg (I : Type) [Fintype I] [DecidableEq I] (tag : A → G) :
    0 ≤ lnS I tag := by
  unfold lnS
  cases (sums I tag).card with
  | zero => simp
  | succ n => exact log_nonneg (by simp)


lemma kl_le_by_height (d : ℝ) (hd : 0 < d) (P Q : Law A) (h : ∀ x, d*P x ≤ Q x) :
    P.kl Q ≤ -log d := by
  rw [kl_ex,show -log d = P.Ex _ from (Ex_const P (-log d)).symm]
  refine Ex_mono_mem P ?_
  intro x hx
  have H := Real.log_le_log (mul_pos hd hx) (h x)
  rw [log_mul hd.ne' hx.ne'] at H
  linarith

lemma fill_cost (tag : A → G) (c : G → ℝ) (hc : c 0=0) (q : Law A)
    (d : ℝ) (hd : 0 < d) (Q : I → Law A) (hq : ∀ i x, d*Q i x ≤ q x) :
    d * bill tag c q (pack Q) (fun x => x) (fun _ => 0) ≤
      Fintype.card I + d * lnS I tag := by
  have hh (i : I) : (Q i).dominated q :=
    fun x hx => lt_of_lt_of_le (mul_pos hd hx) (hq i x)
  have heq : covered (pack Q) (fun x => x) q :=
    fun x hx i => hh i _ ((pack_pos Q x).mp hx i)
  rw [bill_with_entropy heq,send_id,pack_kl hh]
  have Hk : ∑ i, kl (Q i) q ≤ ∑ _i : I, -log d := Finset.sum_le_sum
    (fun i _ => kl_le_by_height d hd (Q i) q (hq i))
  have Hs := lnS_bound (pack Q) (fun x => x) tag
  unfold ans
  simp only [add_zero]
  have Hn := Hcond_nonneg (pack Q) (fun _ => (0:G)) (fun x => x)
  simp_rw [hc,Ex_const]
  have HC := Real.negMulLog_le_one_sub_self hd.le
  unfold negMulLog at HC
  have hsub : d*(-log d) ≤ 1 := by linarith
  calc
    _ ≤ d*((∑ _i : I, -log d)+lnS I tag) := by
      apply mul_le_mul_of_nonneg_left _ hd.le
      linarith
    _ ≤ _ := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have H : (0:ℝ)≤ Fintype.card I := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsub H]

private lemma complete_row (δ : ℝ) (hd : 0 ≤ δ) (P : Law A) (a : A → ℝ)
    (_h0 : ∀ x, 0 ≤ a x) (hp : ∀ x, a x ≤ P x) (ht : ∑ x, a x = 1-δ) :
    ∃ R : Law A, ∀ x, a x + δ*R x = P x := by
  have h : ∑ x, (P x - a x) = δ := by rw [Finset.sum_sub_distrib,P.total,ht]; ring
  obtain hz|hz := eq_or_lt_of_le hd
  · refine ⟨P,fun x => ?_⟩
    have HH := Finset.single_le_sum (s:=Finset.univ) (f:=fun x => P x-a x)
      (fun x _ => sub_nonneg.mpr (hp x)) (Finset.mem_univ x)
    rw [← hz,zero_mul]; linarith [hp x]
  · refine ⟨proportional (fun x => P x-a x) (fun x => sub_nonneg.mpr (hp x)) (by rw [h]; exact hz),fun x => ?_⟩
    rw [proportional_apply,h]; field_simp; ring

theorem thinned_bill (tag : A → G) (c : G → ℝ) (hc : ∀ x, 0 ≤ c x) (hc0 : c 0 = 0)
    (r n : ℕ) (hr : 0 < r) (hn : n=2*r)
    (P : Law Ω) (X : Ω → Letters n A) (U : Ω → G) (q : Law A)
    (hcov : covered P X q) (ε : ℝ) (hε : ∀ i, tv (P.send (fun x => X x i)) q ≤ ε) :
    ∃ Q : Law (WordSample r A G), (∀ i, Q.send (fun a => a.1 i) = q) ∧
      bill tag c q Q Prod.fst Prod.snd ≤ bill tag c q P X U +
        log (Fintype.card (Ticket r n)) + (r + 2*ε*lnS (Fin r) tag) := by
  classical
  obtain ⟨k, hδ, h⟩ := thin_sampler r n hr hn P q X ε hε
  let R := P.withNext k
  let W := Ticket r n
  let Z : Ω × W → W := Prod.snd
  let D := R.send Prod.snd
  let δ := D none
  have hd : 0 ≤ δ := D.nonneg _
  have hds : δ ≤ 2*ε := le_trans (le_of_eq (send_apply R Prod.snd none)) hδ
  let X' (p : Ω × W) := X p.1
  let U' (p : Ω × W) := U p.1
  let QA (e : Fin r ↪ Fin n) : Law (WordSample r A G) :=
    (R.after Z (some e)).send (fun x => (keep X' e x,U' x))
  let m (i : Fin r) (a : A) :=
    ∑ e : Fin r ↪ Fin n, D (some e) * ((QA e).send (fun x => x.1 i)) a
  have hmm (i : Fin r) (f : A → ℝ) :
      ∑ e : Fin r ↪ Fin n, D (some e)* (QA e).Ex (fun x => f (x.1 i)) =
        R.Ex (fun x => gain i (fun j => f (X' x j)) x.2) := by
    let V (j : W) (x : Ω × W) := gain i (fun a => f (X' x a)) j
    have H : D.Ex (fun w => (R.after Z w).Ex (V w)) = _ :=
      R.after_Ex_sum Z V
    refine Eq.trans ?_ H
    change _ = ∑ w, D w * (R.after Z w).Ex (V w)
    rw [Fintype.sum_option]
    unfold V gain
    change _ = D none*((R.after Z none).Ex fun _ => 0)+(∑ e : Fin r ↪ Fin n,D (some e)*((R.after Z (some e)).Ex fun a => f (X' a (e i))))
    rw [Ex_const,mul_zero,zero_add]
    refine Finset.sum_congr rfl fun e _ => ?_
    dsimp only [QA]
    rw [Ex_send]; rfl
  have Hm0 (i a) : 0 ≤ m i a := Finset.sum_nonneg fun e _ =>
    mul_nonneg (D.nonneg _) ((send _ _).nonneg _)
  have Hmp (i a) : m i a ≤ q a := by
    let f (x : A) : ℝ := if x=a then 1 else 0
    have HH := h i f (by intro x; unfold f; split_ifs <;> norm_num)
    change R.Ex (fun x => gain i (fun j => f (X' x j)) x.2) ≤ _ at HH
    rw [← hmm] at HH
    have H1 (P : Law A) : P.Ex f = P a := by unfold f Ex; simp
    have H2 (e : Fin r ↪ Fin n) :
        (QA e).Ex (fun x => f (x.1 i)) = (QA e).send (fun x => x.1 i) a :=
      (Ex_send (QA e) (fun x => x.1 i) f).symm.trans (H1 _)
    simp_rw [H1,H2] at HH; exact HH
  have ht (i) : ∑ a, m i a = 1-δ := by
    unfold m
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,Law.total,mul_one]
    have HH := D.total
    rw [Fintype.sum_option] at HH
    unfold δ; linarith
  choose R' hR using fun i => complete_row δ hd q (m i) (Hm0 i) (Hmp i) (ht i)
  let Ξ : Law (WordSample r A G) := (pack R').send (fun x => (x,0))
  let T (x : Ticket r n) := match x with
    | none => Ξ
    | some e => QA e
  refine ⟨D.through T,fun i => ?_,?_⟩
  · apply Law.ext; intro a
    let f (x : WordSample r A G) := x.1 i
    have heq : (D.through T).send f = D.through (fun w => (T w).send f) := by
      apply ext_of_Ex; intro g; rw [Ex_send]
      simp_rw [Ex_through,Ex_send]
    change (D.through T).send f a = q a
    rw [heq,through_apply,Ex,Fintype.sum_option]
    have h1 : (T none).send f a = R' i a := by
      change (((pack R').send _).send _) _ = _
      unfold f; rw [send_send]
      exact congrArg (fun P : Law A => P a) (marginalPack _ i)
    rw [h1]
    exact (add_comm _ _).trans (hR i a)
  let C (Q : Law (WordSample r A G)) := bill tag c q Q Prod.fst Prod.snd
  let V (w) := bill tag c q (R.after Z w) X' U'
  have HV : D.Ex V ≤ bill tag c q P X U + log (Fintype.card (Ticket r n)) := by
    have heq : bill tag c q R X' U' = bill tag c q P X U :=
      calc
        _ = bill tag c q (R.send Prod.fst) X U := (bill_send tag c q R X U Prod.fst).symm
        _ = _ := by rw [show R.send Prod.fst = P from send_fst_withNext P k]
    refine (bill_condition tag c q R X' U' Z).trans ?_
    rw [heq]
    exact add_le_add_right (H_card _ _) _
  have hr' : covered R X' q := fun x hx i => hcov _ (by
      have H := R.send_pos Prod.fst hx; rwa [show R.send Prod.fst=P from send_fst_withNext P k] at H) i
  have hb (e : Fin r ↪ Fin n) :
      D (some e)*C (QA e) ≤ D (some e)*V (some e) := by
    obtain hh|hh := eq_or_lt_of_le (D.nonneg (some e))
    · rw [← hh,zero_mul,zero_mul]
    · apply mul_le_mul_of_nonneg_left _ hh.le
      unfold C QA
      rw [bill_send]
      exact bill_subfamily tag c q (R.after Z _) X' U' (covered_after hr' Z _ hh) _ e.injective
  have hxy : δ*C Ξ ≤ r + 2*ε*lnS (Fin r) tag + δ*V none := by
    obtain he|he := eq_or_lt_of_le hd
    · rw [← he,zero_mul,zero_mul]
      have := lnS_nonneg (Fin r) tag
      have : 0 ≤ ε := by linarith
      positivity
    unfold C Ξ
    rw [bill_send]
    have hF := fill_cost tag c hc0 q δ he R' (fun i x => by linarith [hR i x,Hm0 i x])
    rw [Fintype.card_fin] at hF
    have hV : 0 ≤ V none := bill_nonneg (covered_after hr' Z _ he) _ _ hc _
    refine hF.trans ?_
    nlinarith [lnS_nonneg (Fin r) tag]
  refine (bill_through_le tag c q D Prod.fst Prod.snd T).trans ?_
  change D.Ex (fun w => C (T w)) ≤ _ + _
  calc
    _ ≤ D.Ex V + (r+2*ε*lnS (Fin r) tag) := by
      unfold Ex
      rw [Fintype.sum_option,Fintype.sum_option]
      dsimp only [T]
      have HH := Finset.sum_le_sum (s:=Finset.univ) (fun e _ => hb e)
      unfold δ at hxy
      linarith
    _ ≤ _ := add_le_add_left HV _

end FourierLLogL.Compress

end OAI
