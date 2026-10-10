import OAI.Analysis.FourierLLogL.Compress.Context

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A G V B Ω I : Type} [Fintype A] [Fintype G] [AddCommGroup G]
    [Fintype V] [Fintype Ω] [Fintype B] [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

lemma average_two_below (P : Law Ω) (f g : Ω → ℝ)
    (h0 : ∀ x, 0 < P x → 0 ≤ f x) (h1 : ∀ x, 0 < P x → 0 ≤ g x)
    (F G : ℝ) (hp : 0 < F) (hq : 0 < G) (hf : P.Ex f ≤ F) (hg : P.Ex g ≤ G) :
    ∃ x, 0 < P x ∧ f x ≤ 2*F ∧ g x ≤ 2*G := by
  obtain ⟨x,hx,hh⟩ := P.exists_le_Ex (fun x => F*g x + G*f x)
  rw [Ex_add,Ex_lmul,Ex_lmul] at hh
  have H : F*g x + G*f x ≤ F*G+G*F := le_trans hh (by gcongr)
  exact ⟨x,hx,by nlinarith [h1 _ hx],by nlinarith [h0 _ hx]⟩

/-- A small noisy cost implies a large heat sum (Gibbs comparison). -/
lemma large_heat (P : Law Ω) (q : Law A) (X : Ω → A) (tag : A → G) (U : Ω → G) (c : G → ℝ)
    (hcov : (P.send X).dominated q) (F : ℝ)
    (hF : P.Ex (fun x => -log (q (X x))) - P.Hcond X (fun x => tag (X x)+U x)+
      P.Ex (fun x => c (U x)) ≤ F) :
    ∃ z : G, exp (-F) ≤ q.Ex fun a => exp (-c (z-tag a)) := by
  let Z (a : Ω) := tag (X a)+U a
  let V := P.send Z
  let p z := P.after Z z
  let g (z : G) :=
    (p z).Ex (fun x => -log (q (X x))) - (p z).H X + (p z).Ex (fun x => c (U x))
  have hh : V.Ex g ≤ F := by
    have H (f : Ω → ℝ) :
        V.Ex (fun z => (p z).Ex f) = P.Ex f := after_Ex_sum P Z (fun _ => f)
    unfold g; rw [Ex_add,Ex_sub,H,H]
    change _ - (P.send Z).Ex (fun z => (P.after Z z).H X)+_≤ _
    rw [← Hcond_after]; exact hF
  obtain ⟨z,hz,hze⟩ := V.exists_le_Ex g
  let f a := q a* exp (-c (z-tag a))
  let D := ∑ a, f a
  have hf (a) : 0 ≤ f a := mul_nonneg (q.nonneg _) (exp_nonneg _)
  have hc (a) (ha : 0 < p z a) : 0 < q (X a) := by
    have HH := (after_mem (P:=P) (W:=Z) hz).mp ha
    exact hcov _ (P.send_pos X HH.2)
  have ht : 0 < D := by
    obtain ⟨x,hx⟩ := q.mem_nonempty
    have h : 0 < f x := mul_pos hx (exp_pos _)
    exact lt_of_lt_of_le h (Finset.single_le_sum (s:=Finset.univ) (fun a _ => hf a) (Finset.mem_univ _))
  let Q := proportional f hf ht
  have he (x) (hx : 0 < p z x) :
      -log (Q (X x)) = -log (q (X x))+c (U x)+log D := by
    have hx' := (after_mem (P:=P) (W:=Z) hz).mp hx
    have h : z-tag (X x)=U x := by rw [← hx'.1]; unfold Z; abel
    change -log (f _/D) = _
    rw [log_div (mul_pos (hc _ hx) (exp_pos _)).ne' ht.ne']
    rw [log_mul (hc _ hx).ne' (exp_pos _).ne',h,log_exp]
    ring
  have hd : ((p z).send X).dominated Q := by
    intro a ha
    obtain ⟨y,rfl,hy⟩ := (send_pos_iff _ _ _).mp ha
    exact div_pos (mul_pos (hc y hy) (exp_pos _)) ht
  have HC : (p z).H X ≤ (p z).Ex (fun x => -log (Q (X x))) := by
    rw [← Ex_send (p z) X (fun x => -log (Q x))]
    exact sub_nonneg.mp (kl_nonneg hd)
  have hlin := ((p z).Ex_congr_mem he)
  rw [hlin,Ex_add,Ex_add,Ex_const] at HC
  have h1 : -F ≤ log D := by
    have hi := hze.trans hh
    dsimp only [g] at hi; linarith
  refine ⟨z,le_trans (Real.exp_le_exp.mpr h1) (Real.exp_log ht).le⟩

/-- Stack selection with one coordinate per actual letter. -/
lemma stack_select (tag : A → G) (c : G → ℝ) (hc : ∀ x, 0 ≤ c x)
    (p : Law (A×V)) (P : Law Ω) (X : Ω → I → A) (W : Ω → I → V) (U : Ω → G)
    (hp : ∀ i : I, P.send (fun x => (X x i,W x i)) = p)
    (F D : ℝ) (hF : 0 < F) (hD : 0 < D)
    [Nonempty I]
    (hs : Fintype.card I * p.Hcond Prod.fst Prod.snd -
      P.Hcond X (fun x => (ans tag X U x, W x)) + P.Ex (fun x => c (U x)) ≤ F)
    (hd : log (Fintype.card A) - p.Hcond Prod.fst Prod.snd ≤ D) :
    ∃ (q : I → Law A) (z : G),
      exp (-(2*F)) ≤ (pack q).Ex (fun x => exp (-c (z-tot tag x))) ∧
      ∑ i, (log (Fintype.card A)- (q i).entropy) ≤ 2*(Fintype.card I*D) := by
  classical
  let R w := P.after W w
  let k v := (p.after Prod.snd v).send Prod.fst
  let q (w : I → V) (i : I) : Law A := k (w i)
  let Z := ans tag X U
  let Y := P.send W
  have hval (a : Ω) (ha : 0 < P a) (i : I) : 0 < q (W a) i (X a i) := by
    have H0 := P.send_pos (fun a => (X a i,W a i)) ha
    rw [hp i] at H0
    exact (p.after Prod.snd (W a i)).send_pos Prod.fst (p.after_self_pos _ H0)
  have hdom (w : I → V) (hw : 0 < Y w) :
      ((R w).send X).dominated (pack (q w)) := by
    intro x hx
    obtain ⟨a,rfl,ha⟩ := (send_pos_iff _ _ _).mp hx
    have H := (after_mem hw).mp ha
    rw [pack_pos,← H.1]
    exact hval a H.2
  let N := Fintype.card I
  let a (w : I → V) :=
    (R w).Ex (fun x => -log (pack (q w) (X x))) -
      (R w).Hcond X Z + (R w).Ex fun x => c (U x)
  let b (w : I → V) := ∑ i, (log (Fintype.card A) - entropy (q w i))
  have ha (w) (hw : 0 < Y w) : 0 ≤ a w := by
    have hh := kl_nonneg (hdom w hw)
    unfold kl crossE at hh
    rw [Ex_send] at hh
    have ht := Hcond_le_H (R w) X Z
    unfold H at ht
    exact add_nonneg (by linarith) (Ex_nonneg (R w) (fun x => hc _))
  have hb (w : I → V) : 0 ≤ b w :=
    Finset.sum_nonneg fun i _ => sub_nonneg.mpr (entropy_le_log_card _)
  have hrow (i : I) (f : (A×V) → ℝ) :
      P.Ex (fun x => f (X x i,W x i)) = p.Ex f := by
    rw [← Ex_send P (fun x => (X x i,W x i)), hp i]
  have hE : Y.Ex a ≤ F := by
    have hX : Y.Ex (fun w => (R w).Ex fun x => -log (pack (q w) (X x))) =
        ∑ i : I, p.Hcond Prod.fst Prod.snd := by
      let f (w : I → V) (x : Ω) := -log (pack (q w) (X x))
      rw [show Y.Ex _ = P.Ex _ from P.after_Ex_sum W f]
      have H1 (x : Ω) (hx : 0 < P x) :
          f (W x) x = ∑ i, -log (q (W x) i (X x i)) := by
        unfold f; rw [pack_apply,log_prod,Finset.sum_neg_distrib]
        exact fun i _ => (hval x hx i).ne'
      rw [P.Ex_congr_mem H1,Ex_finset_sum,Hcond_log]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact hrow i (fun x => -log (k x.2 x.1))
    have HU : Y.Ex (fun w => (R w).Ex (fun x => c (U x))) = _ :=
      P.after_Ex_sum W (fun _ x => c (U x))
    have hz : Y.Ex (fun w => (R w).Hcond X Z) = _ :=
      (Hcond_after_cond P X Z W).symm
    unfold a
    rw [Ex_add,Ex_sub,hX,HU,hz,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact hs
  have hB : Y.Ex b ≤ N * D := by
    have HH : ∀ i : I, Y.Ex (fun w => entropy (q w i)) = p.Hcond Prod.fst Prod.snd := by
      intro i
      dsimp only [Y]; rw [Ex_send]
      rw [Hcond_after,Ex_send]
      exact hrow i (fun x => entropy (k x.2))
    unfold b
    simp_rw [Ex_finset_sum,Ex_sub,HH,Ex_const,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  obtain ⟨w,hw,hw',hw''⟩ :=
    average_two_below Y a b ha (fun x _ => hb x) F (N*D) hF
      (mul_pos (by unfold N; positivity) hD) hE hB
  obtain ⟨z,hz⟩ := large_heat (R w) (pack (q w)) X (tot tag) U c (hdom w hw) (2*F) hw'
  exact ⟨q w,z,hz,hw''⟩

lemma freeze (tag : A → G) (hi : Injective tag) (c : G → ℝ) (hc : ∀ x, 0 ≤ c x)
    (P : Labelled A) (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (F D : ℝ) (hF : 0 < F) (hD : 0 < D) (hs : fundK tag c P m r ≤ F)
    (hd : log (Fintype.card A) - fundG tag P 1 ≤ D) :
    ∃ (q : (Fin r×Fin m) → Law A) (z : G),
      exp (-(2*F)) ≤ (pack q).Ex (fun x => exp (-c (z-tot tag x))) ∧
      ∑ i, (log (Fintype.card A)- (q i).entropy) ≤ 2*((r:ℝ)*m*D) := by
  have : NeZero r := ⟨hr.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩
  let t := lblSum tag P m
  let C := lblCtx P m
  let Q := lblP P m
  obtain ⟨S,hS,he⟩ := (opt_spec r Q t C (fun x => x) c).1
  let Y := WordSample r (Letters m (A×P.obs)) G
  let X (p : Y) (i : Fin r × Fin m) := (p.1 i.1 i.2).1
  let W (p : Y) (i : Fin r × Fin m) := (p.1 i.1 i.2).2
  have Hrow (i : Fin r×Fin m) : S.send (fun p => (X p i,W p i)) = P.law := by
    have h1 : Q.send (fun x => x i.2) = P.law := marginalPack _ _
    rw [← h1,← hS i.1,send_send]; rfl
  have HQ : Q.Hcond (fun x => x) C = m*P.law.Hcond Prod.fst Prod.snd := by
    have HH := Hcond_vec_pack (fun _ : Fin m => P.law) (fun _ a => a)
      (fun _ => Prod.snd)
    have hi : P.law.Hcond (fun x => x) Prod.snd = P.law.Hcond Prod.fst Prod.snd := by
      unfold Hcond; congr 1; apply H_partition; simp
    simp_rw [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at HH
    exact HH
  let u0 : Y → G := Prod.snd
  let s0 (x : Y) := ans t Prod.fst u0 x
  have ht0 (x : Y) : s0 x = ans tag X u0 x := by
    unfold s0 t lblSum ans tot
    simp only [Fintype.sum_prod_type, Function.comp_apply, X]
  let w0 (x : Y) := ctxt C Prod.fst x
  have h1 : S.Hcond Prod.fst (fun x => (s0 x,w0 x)) =
      S.Hcond X (fun x => (ans tag X u0 x,W x)) := by
    unfold Hcond
    have h' (x y : Y) : w0 x = w0 y ↔ W x=W y := by
      simp only [w0,W,C,ctxt,lblCtx,funext_iff,Prod.forall]
    congr 1
    · apply H_partition
      intro x y
      simp only [Prod.mk.injEq,h',ht0]
      have hy : x.1=y.1 ↔ X x=X y ∧ W x=W y := by
        simp only [X,W,funext_iff,Prod.forall]
        constructor
        · intro h; simp [h]
        · grind
      tauto
    · apply H_partition; simp only [Prod.mk.injEq,h',ht0]; tauto
  have hcost : Fintype.card (Fin r×Fin m)*P.law.Hcond Prod.fst Prod.snd -
      S.Hcond X (fun x => (ans tag X u0 x,W x))+ S.Ex (fun a => c (u0 a)) ≤ F := by
    have HH : rent t C (fun x => x) c S Prod.fst Prod.snd ≤ F := he.le.trans hs
    unfold rent at HH
    rw [rent_first hS,HQ] at HH
    change _ - S.Hcond Prod.fst (fun x => (s0 x,w0 x))+S.Ex (fun x => c (u0 x)) ≤ F at HH
    rw [h1] at HH
    simp only [Fintype.card_fin,Fintype.card_prod,Nat.cast_mul,mul_assoc] at *
    exact HH
  have Hsel := stack_select tag c hc P.law S X W u0 Hrow F D hF hD hcost
    (by rwa [fundG_one tag hi] at hd)
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using Hsel
end FourierLLogL.Compress

end OAI
