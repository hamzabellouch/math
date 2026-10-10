import OAI.Analysis.FourierLLogL.Compress.Thinning
import OAI.Analysis.FourierLLogL.Compress.Context
/-! # Initial estimates for contextual costs -/
open Function Filter Set
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A Ω G : Type} [Fintype A] [Fintype Ω] [Fintype G] [AddCommGroup G]
    [DecidableEq G] {n : ℕ}
set_option linter.unusedSectionVars false


lemma initial_pack (p : Law A) (m : ℕ) :
    lblP (initial p) m = (iid p m).send
      (fun x => fun i => (x i,())) := by
  unfold lblP iid initial
  exact (sendPack (fun _ => p) (fun _ (x : A) => (x,()))).symm

lemma G_initial (tag : A → G) (p : Law A) (m : ℕ) :
    fundG tag (initial p) m = (iid p m).H (tot tag) := by
  unfold fundG
  rw [initial_pack]
  exact (Hcond_send (iid p m) (fun x i => (x i,()))
    (lblSum tag (initial p) m) (lblCtx (initial p) m)).trans (Hcond_constant _ _ (fun _ => ()))

lemma K_initial (tag : A → G) (c : G → ℝ) (p : Law A) (m r : ℕ) :
    fundK tag c (initial p) m r = opt r (iid p m) (tot tag)
      (fun _ => fun _ : Fin m => ()) id c := by
  unfold fundK
  rw [initial_pack]
  exact opt_proj (lblSum tag (initial p) m) (lblCtx (initial p) m) id c
    (iid p m) (fun x i => (x i,())) r

lemma I_initial (tag : A → G) (p : Law A) (r : ℕ) :
    fundI tag (initial p) r = opt r p tag (fun _ => ()) (fun _ : Unit => (0:G))
      (fun _ => 0) := by
  unfold fundI initial
  exact opt_proj (fun x : A×Unit => tag x.1) Prod.snd _ _ p (fun x => (x,())) r

lemma trial_initial {E Z : Type} [Fintype E] [Fintype Z] [Nonempty E]
    (tag : A → G) (p : Law A) (e : E → G) (c : E→ℝ) (z : Z)
    (P : Law Ω) (X : Ω → Letters n A) (U : Ω → E)
    (h : hasRows p P X) :
    rent tag (fun _ => z) e c P X U =
      (∑ i, P.Ex (fun a => -log (p (X a i)))) -
        P.Hcond X (ans tag X (fun a => e (U a))) + P.Ex (fun a => c (U a)) := by
  have hz (i : Fin n) :
      P.Hcond (readP X i) ((fun _ => z) ∘ readP X i) =
      P.Ex (fun a => -log (p (X a i))) := by
    have h1 : P.Hcond (readP X i) (fun _ => z) = P.H (readP X i) :=
      Hcond_constant _ _ _
    rw [show (fun (_:A) => z) ∘ readP X i = fun _ => z from rfl,h1,H_log,h i]; rfl
  unfold rent
  simp_rw [hz]
  congr 2
  apply Hcond_right_partition
  simp only [Prod.mk.injEq]; tauto

lemma K_initial_le (tag : A → G) (c : G → ℝ) (p : Law A) (m r : ℕ)
    (P : Law Ω) (X : Ω → Letters r (Letters m A)) (U : Ω → G)
    (h : hasRows (iid p m) P X) :
    fundK tag c (initial p) m r ≤ bill (tot tag) c (iid p m) P X U := by
  rw [K_initial]
  apply le_trans (opt_le_rent _ _ _ _ _ P X U h) (le_of_eq ?_)
  rw [trial_initial _ _ _ _ _ _ X U h]; rfl

lemma exact_zero_g {I : Type} [Fintype I] [DecidableEq I]
    (P : Law Ω) (X : Ω → I → A) (tag : A → G) (q : Law A) (h : covered P X q) :
    bill tag (fun _=>0) q P X (fun _=>0) =
      (P.send X).kl (pack (fun _ => q)) + P.H (fun a => tot tag (X a)) := by
  rw [bill_with_entropy h,Hcond_determined (P:=P) (X:=fun _=>0) (W:=X) (fun _ _ _ => rfl)]
  unfold ans
  simp_rw [add_zero,Ex_const]
  ring

lemma I_initial_le (tag : A → G) (p : Law A) (r : ℕ)
    (P : Law Ω) (X : Ω → Letters r A) (hh : hasRows p P X) :
    fundI tag (initial p) r ≤ (P.send X).kl (iid p r)+P.H (fun a => tot tag (X a)) := by
  rw [I_initial]
  apply le_trans (opt_le_rent _ _ _ _ p P X (fun _ => ()) hh)
  rw [trial_initial _ _ _ _ _ _ X _ hh]
  change bill tag (fun _=>0) p P X (fun _=>0) ≤ _
  exact (exact_zero_g P X tag p (kl_covered P X p hh)).le

/-- Compare the entropy of the exact sum with the entropy of the perturbed sum and the error. -/
lemma sum_entropy {I : Type} [Fintype I] [DecidableEq I]
    (P : Law Ω) (X : Ω → I → A) (U : Ω → G) (tag : A → G)
    (c : G → ℝ) (hc : ∀ x, 0 ≤ c x) (q : Law A) (hcov : covered P X q)
    (Q : Law G) (hQ : ∀ y, 0 < Q y) (L : ℝ) (hL : ∀ y, -log (Q y) = L+c y) :
    let F := bill tag c q P X U
    P.H (fun a => tot tag (X a)) + (P.send X).kl (pack fun _ => q) ≤ 3*F+2*L := by
  intro F
  let S (a) := tot tag (X a)
  let Z := ans tag X U
  have hEnt : P.H U ≤ L + P.Ex (fun a => c (U a)) := by
    have H := entropy_le_cross_aux (P.send U) Q Q.nonneg Q.total.le fun x _ => hQ x
    refine H.trans (le_of_eq ?_)
    unfold crossE
    simp_rw [hL,Ex_send,Ex_add,Ex_const]
  have hBill : P.Ex (fun a => c (U a)) ≤ F :=
    ((le_add_of_nonneg_left (kl_nonneg (covered_pack hcov))).trans
      (kl_le_bill hcov tag c hc _))
  have hH := bill_with_entropy hcov tag c U
  change F = _+(P.H Z-_)+_ at hH
  have HI : P.H S ≤ P.H Z + P.H U := by
    have H1 : P.H S ≤ P.H (fun a => (U a,Z a)) :=
      H_le_of_determined _ fun a b hh => by
        have hi := Prod.mk.inj hh
        change U a=U b ∧ S a+U a=S b+U b at hi
        exact add_right_cancel (b:=U b) (by rw [← hi.2,hi.1])
    have H2 := Hcond_le_H P U Z
    rw [H_pair_chain] at H1; linarith
  have hC := Hcond_le_H P U X
  change P.H S + _ ≤ _
  linarith [P.Ex_nonneg (fun a => hc (U a))]


structure Starting (tag : A → G) (c : G → ℝ) (N m : ℕ) (E ε : ℝ) where
  q : Law A
  P : Law (WordSample N A G)
  sym : exch P
  marg (i : Fin N) : P.send (fun a => a.1 i) = q
  bound : bill tag c q P Prod.fst Prod.snd ≤ E
  within : m ≤ N
  near : tv (P.send (prefixB Prod.fst m within)) (iid q m) ≤ ε

namespace Starting
variable {tag : A → G} {c : G → ℝ} {N m : ℕ} {E ε : ℝ} (s : Starting tag c N m E ε)

lemma cover : covered s.P Prod.fst s.q := kl_covered _ _ _ s.marg

lemma exact_bound (hc : ∀ x, 0 ≤ c x) (Q : Law G) (hQ : ∀ y, 0 < Q y)
    (L : ℝ) (hL : ∀ y, -log (Q y)=L+c y)
    (n : ℕ) (hn : n ≤ N) :
    let X := prefixB (α:=A) (Ω:=WordSample N A G) Prod.fst n hn
    s.P.H (fun a => tot tag (X a)) + (s.P.send X).kl (iid s.q n) ≤ 3*E+2*L := by
  intro X
  have h1 := bill_subfamily tag c s.q s.P Prod.fst Prod.snd s.cover
    (offset 0 n (show 0+n ≤ N by omega)) (offset_injective _ _ _)
  change bill tag c s.q s.P X Prod.snd ≤ _ at h1
  refine (sum_entropy s.P X Prod.snd tag c hc s.q (covered_subfamily s.cover _) Q hQ L hL).trans ?_
  linarith [s.bound]

lemma I_upper (hc : ∀ x, 0 ≤ c x) (Q : Law G) (hQ : ∀ y, 0 < Q y)
    (L : ℝ) (hL : ∀ y,-log (Q y)=L+c y) (n : ℕ) (hn : n ≤ N) :
    fundI tag (initial s.q) n ≤ 3*E+2*L := by
  have h := s.exact_bound hc Q hQ L hL n hn
  let X := prefixB (α:=A) (Ω:=WordSample N A G) Prod.fst n hn
  have heq : hasRows s.q s.P X := fun i => s.marg (offset 0 n _ i)
  refine (I_initial_le tag s.q n s.P X heq).trans ?_
  rw [add_comm]
  exact h

lemma near_small (n : ℕ) (hn : n ≤ m) :
    tv (s.P.send (prefixB Prod.fst n (hn.trans s.within))) (iid s.q n) ≤ ε := by
  let X : Letters m A → Letters n A := fun x i => x (offset 0 n (by omega : 0+n ≤ m) i)
  have h := tv_data_processing (s.P.send (prefixB Prod.fst m s.within)) (iid s.q m) X
  rw [send_send] at h
  have hh : (iid s.q m).send X = iid s.q n :=
    sendPack_embedding _ _ (offset_injective _ _ _)
  rw [hh] at h
  apply le_trans _ s.near
  have he : (fun a : WordSample N A G => X (prefixB Prod.fst m s.within a)) = prefixB Prod.fst n (hn.trans s.within) := by
    funext x ⟨i,hi⟩; simp only [X,prefixB,readBlock,keep,offset,zero_add]
  rwa [he] at h
lemma G_upper (hc : ∀ x, 0 ≤ c x) (Q : Law G) (hQ : ∀ y, 0 < Q y)
    (L : ℝ) (hL : ∀ y,-log (Q y)=L+c y) (n : ℕ) (hn : n ≤ m) :
    fundG tag (initial s.q) n ≤ 3*E+2*L+log 2 + ε*lnS (Fin n) tag := by
  rw [G_initial]
  let X := prefixB (α:=A) (Ω:= WordSample N A G) Prod.fst n (hn.trans s.within)
  let Y := tot tag (ι:=Fin n)
  have H1 : tv ((iid s.q n).send Y) ((s.P.send X).send Y) ≤ ε := by
    rw [tv_comm]
    exact (tv_data_processing _ _ Y).trans (s.near_small n hn)
  have HT := entropy_le_of_tv ((iid s.q n).send Y) ((s.P.send X).send Y)
    (sums (Fin n) tag) fun x hx => by
      obtain ⟨a,rfl,_⟩ := (send_pos_iff _ _ _).mp hx
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  change _ ≤ (s.P.send X).H Y + (_ + _ * lnS (Fin n) tag) at HT
  have hk : dominated (s.P.send X) (iid s.q n) := covered_pack
    (covered_subfamily s.cover _)
  have he := s.exact_bound hc Q hQ L hL n (hn.trans s.within)
  change s.P.H _+kl (s.P.send X) _ ≤ _ at he
  apply HT.trans
  rw [H_send]
  nlinarith [kl_nonneg hk,lnS_nonneg (Fin n) tag]

lemma block_near (n : ℕ) (hn : n ≤ m) (g : Fin n → Fin N) (hg : Injective g) :
    tv (s.P.send (keep Prod.fst g)) (iid s.q n) ≤ ε := by
  let f := offset 0 n (by have := s.within; omega : 0+n ≤ N)
  have Hf : Injective f := offset_injective _ _ _
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair _ _ Hf hg
  have hh :=
    congrArg (fun R : Law (WordSample N A G) => R.send (keep Prod.fst f)) (s.sym e)
  rw [send_send] at hh
  have heq : (fun x : WordSample N A G => keep Prod.fst f (appPerm e x)) =
      keep Prod.fst g := by
    funext x i; dsimp only [keep,appPerm]; rw [he i]
  rw [heq] at hh
  rw [hh]
  exact s.near_small n hn

lemma block_card (n r : ℕ) :
    lnS (Fin r) (tot tag (ι:=Fin n)) = lnS (Fin (r*n)) tag := by
  let e := finProdFinEquiv (m:=r) (n:=n)
  have hh (x : Fin (r*n) → A) :
      tot tag x = tot (tot tag (ι:=Fin n)) (fun i : Fin r => fun j => x (e (i,j))) := by
    unfold tot
    rw [← Fintype.sum_equiv e (fun i => tag (x (e i))) (fun i => tag (x i)) (fun _ => rfl),
      Fintype.sum_prod_type]
  have H : sums (Fin (r*n)) tag = sums (Fin r) (tot tag (ι:=Fin n)) := by
    ext a
    simp only [sums,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨_,(hh x).symm⟩
    · rintro ⟨x,rfl⟩
      refine ⟨(fun i => x (e.symm i).1 (e.symm i).2),?_⟩
      rw [hh]; simp
  simp only [lnS,H]

lemma K_upper (hc : ∀ x, 0 ≤ c x) (hc0 : c 0 = 0)
    (n r : ℕ) (hr : 0 < r) (hn : n ≤ m) (hn' : 2*r*n ≤ N) :
    fundK tag c (initial s.q) n r ≤ E + log (Fintype.card (Ticket r (2*r))) +
      (r + 2*ε*lnS (Fin (r*n)) tag) := by
  let g : Fin (2*r) × Fin n → Fin N := offset 0 ((2*r)*n) (by omega) ∘ finProdFinEquiv
  have hg : Injective g := (offset_injective _ _ _).comp finProdFinEquiv.injective
  let X (x : WordSample N A G) (i : Fin (2*r)) (j : Fin n) := x.1 (g (i,j))
  let q := iid s.q n
  have Hc : covered s.P X q := by
    intro x hx i; exact (pack_pos _ _).mpr (fun j => s.cover x hx (g (i,j)))
  have Hm (i : Fin (2*r)) : tv (s.P.send (fun x => X x i)) q ≤ ε :=
    s.block_near _ hn (fun j => g (i,j)) (fun _ _ h => congrArg Prod.snd (hg h))
  obtain ⟨Q,hQ,hb⟩ := thinned_bill (tot tag (ι:=Fin n)) c hc hc0 r (2*r) hr rfl
    s.P X Prod.snd q Hc ε Hm
  let X' := keep (Prod.fst : WordSample N A G → _) g
  have heq : bill (tot tag (ι:=Fin n)) c q s.P X Prod.snd =
      bill tag c s.q s.P X' Prod.snd := by
    let Y := ans tag X' Prod.snd
    have hy : ans (tot tag (ι:=Fin n)) X Prod.snd = Y := by
      ext x; unfold Y ans tot
      rw [Fintype.sum_prod_type]; rfl
    unfold bill
    rw [hy, Fintype.sum_prod_type]
    have h2 : s.P.Hcond X Y = s.P.Hcond X' Y := by
      unfold Hcond
      congr 1
      refine H_partition _ fun a b => ?_
      simp only [Prod.mk.injEq,funext_iff,Prod.forall,X,X',keep]
    have h1 (i : Fin (2*r)) : s.P.Ex (fun a => -log (q (X a i))) =
        ∑ j, s.P.Ex (fun a => -log (s.q (X' a (i,j)))) := by
      rw [← Ex_finset_sum]
      apply Ex_congr_mem
      intro x hx
      change -log (∏ j : Fin n, s.q (X x i j)) = _
      rw [log_prod,Finset.sum_neg_distrib]
      · rfl
      · exact fun j _ => (s.cover x hx _).ne'
    rw [h2]
    simp_rw [h1]
    rfl
  have hh := bill_subfamily tag c s.q s.P Prod.fst Prod.snd s.cover g hg
  change bill tag c s.q s.P X' Prod.snd ≤ _ at hh
  rw [heq,block_card] at hb
  refine le_trans (K_initial_le tag c s.q n r Q Prod.fst Prod.snd hQ) ?_
  exact le_trans hb (add_le_add_left (add_le_add_left (hh.trans s.bound) _) _)

end Starting
end FourierLLogL.Compress

end OAI
