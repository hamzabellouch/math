import OAI.Analysis.FourierLLogL.Finite.Alternative
import OAI.Analysis.FourierLLogL.Finite.Independent
/-! # Noisy sum entropy cost -/

open Set Function Filter
open scoped BigOperators
noncomputable section

namespace OAI

namespace FourierLLogL.Compress
open Real Law

variable {ι τ κ α Ω Ω' A G : Type}
variable [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ]
variable [Fintype α] [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype G] [AddCommGroup G]

def tot (tag : α → G) (x : ι → α) : G := ∑ i, tag (x i)

def ans (tag : α → G) (X : Ω → ι → α) (U : Ω → G) (a : Ω) := tot tag (X a)+U a

/-- Noisy bill: cross entropy with fixed comparator law per position, entropy of
letter vector conditional on noisy sum, plus error cost. -/
def bill (tag : α → G) (c : G → ℝ) (q : Law α)
    (P : Law Ω) (X : Ω → ι → α) (U : Ω → G) :=
  (∑ i, P.Ex fun a => -log (q (X a i))) - P.Hcond X (ans tag X U) + P.Ex (fun a => c (U a))

lemma bill_send (tag : α → G) (c : G → ℝ) (q : Law α)
    (P : Law Ω) (X : Ω' → ι → α) (U : Ω' → G) (W : Ω → Ω') :
    bill tag c q (P.send W) X U = bill tag c q P (fun x => X (W x)) (fun x => U (W x)) := by
  unfold bill; simp_rw [Hcond_send,Ex_send]; rfl

lemma bill_mixture_le (tag : α → G) (c : G → ℝ) (q : Law α)
    (P Q : Law Ω) (X : Ω → ι → α) (U : Ω → G) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    bill tag c q (mixture P Q t h0 h1) X U ≤
      t*bill tag c q P X U + (1-t)*bill tag c q Q X U := by
  unfold bill
  simp_rw [mixture_Ex,Finset.sum_add_distrib, ← Finset.mul_sum]
  have H := Hcond_mixture_ge P Q t h0 h1 X (ans tag X U)
  linarith

lemma bill_cont (tag : α → G) (c : G → ℝ) (q : Law α)
    (X : Ω → ι → α) (U : Ω → G) :
    Continuous (fun P : Law Ω => bill tag c q P X U) :=
  ((continuous_finsetSum _ fun _ _ => continuous_Ex _).sub (continuous_Hcond _ _)).add
    (continuous_Ex _)

lemma bill_through_le (tag : α → G) (c : G → ℝ) (q : Law α)
    (P : Law Ω) (X : Ω' → ι → α) (U : Ω' → G) (Q : Ω → Law Ω') :
    bill tag c q (P.through Q) X U ≤ P.Ex (fun a => bill tag c q (Q a) X U) := by
  unfold bill
  simp_rw [Ex_add,Ex_sub,Ex_through, ← Ex_finset_sum]
  linarith [Hcond_through P Q X (ans tag X U)]

/-- All letters have support contained in comparison law's. -/
def covered (P : Law Ω) (X : Ω → ι → α) (q : Law α) : Prop :=
  ∀ x, 0 < P x → ∀ i, 0 < q (X x i)

lemma covered_pack {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q) :
    (P.send X).dominated (pack (fun _ => q)) := by
  intro x hx
  obtain ⟨a,rfl,ha⟩ := (send_pos_iff _ _ _).mp hx
  exact (pack_pos _ _).mpr (h a ha)

lemma sum_crosspack {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q) :
    (P.send X).crossE (pack (fun _ => q)) = ∑ i, P.Ex fun a => -log (q (X a i)) := by
  rw [crossE_pack (covered_pack h)]
  simp_rw [crossE,Ex_send]

lemma kl_le_bill {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q)
    (tag : α → G) (c : G → ℝ) (_hc : ∀ x, 0 ≤ c x) (U : Ω → G) :
    (P.send X).kl (pack (fun _ => q)) + P.Ex (fun a => c (U a)) ≤ bill tag c q P X U := by
  unfold bill kl
  rw [sum_crosspack h]
  exact add_le_add_left (sub_le_sub_left (Hcond_le_H P X _) _) _

lemma bill_nonneg {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q)
    (tag : α → G) (c : G → ℝ) (hc : ∀ x, 0 ≤ c x) (U : Ω → G) :
    0 ≤ bill tag c q P X U := le_trans
      (add_nonneg (kl_nonneg (covered_pack h)) (P.Ex_nonneg fun a => hc (U a)))
      (kl_le_bill h tag c hc U)

lemma bill_with_entropy {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q)
    (tag : α → G) (c : G → ℝ) (U : Ω → G) :
    bill tag c q P X U =
      (P.send X).kl (pack (fun _ => q)) + (P.H (ans tag X U) - P.Hcond U X) +
        P.Ex fun a => c (U a) := by
  let Z := ans tag X U
  have h1 : P.H (fun a => (U a,X a)) = P.H (fun a => (X a,Z a)) :=
    P.H_partition fun x y => by
      simp only [Z,ans,Prod.mk.injEq]
      constructor
      · rintro ⟨hu,hx⟩; rw [hu,hx]; exact ⟨rfl,rfl⟩
      · rintro ⟨hx,hz⟩; rw [hx] at hz; exact ⟨add_left_cancel hz,hx⟩
  unfold bill kl
  rw [← sum_crosspack h]
  change _ - P.Hcond X Z + _ = (_ - P.H X) + (P.H Z- P.Hcond U X)+_
  unfold Hcond; rw [h1]; ring

lemma bill_change {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q)
    (tag : α → G) (c : G → ℝ) (U : Ω → G) (p : Law α)
    (hp : ∀ i, P.send (fun x => X x i) = p) :
    bill tag c p P X U ≤ bill tag c q P X U := by
  apply add_le_add_left
  apply sub_le_sub_right
  refine Finset.sum_le_sum fun i _ => ?_
  let x (a : Ω) := X a i
  have h1 : p.dominated q := by
    intro b hb
    have HH : 0 < P.send x b := by rw [hp i]; exact hb
    obtain ⟨a,rfl,ha⟩ := (P.send_pos_iff _ b).mp HH
    exact h a ha i
  suffices hi : (P.send x).crossE p ≤ (P.send x).crossE q by
    simpa only [crossE, Ex_send] using hi
  rw [show x = _ from rfl, hp i]
  exact sub_nonneg.mp (kl_nonneg h1)

lemma bill_condition (tag : α → G) (c : G → ℝ) (q : Law α)
    (P : Law Ω) (X : Ω → ι → α) (U : Ω → G) (W : Ω → A) :
    (P.send W).Ex (fun w => bill tag c q (P.after W w) X U) ≤
      bill tag c q P X U + P.H W := by
  let Z := ans tag X U
  have hE (f : Ω → ℝ) :
      (P.send W).Ex (fun w => (P.after W w).Ex f) = P.Ex f :=
    P.after_Ex_sum W (fun _ => f)
  have hY := Hcond_after_cond P X Z W
  have hP := P.Hcond_nonneg W (fun x => (X x,Z x))
  have hl := Hcond_le_H P W Z
  have heq := P.H_partition (X:=fun x => ((X x), Z x,W x))
    (Y:=fun x => (W x,X x,Z x)) (fun _ _ => by simp; tauto)
  have hp := P.H_pair_rev W Z
  unfold bill
  simp_rw [Ex_add,Ex_sub,Ex_finset_sum,hE]
  change _ - ((P.send W).Ex (fun w => (P.after W w).Hcond X Z)) + _ ≤
    (_-P.Hcond X Z + _)+_
  rw [← hY]
  unfold Hcond at *
  linarith


omit [DecidableEq ι] [DecidableEq τ] [DecidableEq κ] in
lemma sum_split' (e : τ ⊕ κ ≃ ι) {M : Type*} [AddCommMonoid M] (f : ι → M) :
    ∑ i, f i = ∑ i, f (e (.inl i)) + ∑ i, f (e (.inr i)) :=
  calc
    _ = ∑ i, f (e i) :=
      (Fintype.sum_equiv e _ f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_sum_type _

def keep (X : Ω → ι → α) (s : τ → ι) := fun a i => X a (s i)

lemma bill_split (tag : α → G) (c : G → ℝ) (q : Law α)
    (P : Law Ω) (X : Ω → ι → α) (U : Ω → G) (h : covered P X q) (e : τ ⊕ κ ≃ ι) :
    let V := keep X (fun i => e (.inl i))
    let W := keep X (fun i => e (.inr i))
    (P.send W).Ex (fun w => bill tag c q (P.after W w) V U) ≤ bill tag c q P X U := by
  intro V W
  let Y := ans tag V U
  let Z := ans tag X U
  have hs (x : Ω) : Z x = Y x + tot tag (W x) := by
    unfold Z Y ans tot
    rw [sum_split' e (fun i => tag _)]
    dsimp only [V,W,keep]
    abel
  have hh (x y : Ω) : X x = X y ↔ (V x,W x) = (V y,W y) := by
    constructor
    · intro h; unfold V W keep; rw [h]
    · intro H
      funext i
      obtain ⟨t,rfl⟩ := e.surjective i
      rcases t with t|t
      · exact congrFun (congrArg Prod.fst H) t
      · exact congrFun (congrArg Prod.snd H) t
  have hpart :
      P.Hcond X Z = P.Hcond (fun x => (V x,W x)) Z := by
    unfold Hcond
    congr 1
    exact P.H_partition fun x y => by simp [hh x y]
  have hpart' :
      P.Hcond V (fun x => (W x,Z x)) = P.Hcond V (fun x => (Y x,W x)) := by
    apply Hcond_right_partition
    intro a b
    simp only [Prod.mk.injEq, hs]
    constructor
    · rintro ⟨h,he⟩; rw [h] at he; exact ⟨add_right_cancel he,h⟩
    · rintro ⟨h,h'⟩; rw [h,h']; exact ⟨rfl,rfl⟩
  have hCE : P.Hcond W Z ≤ ∑ i, P.Ex (fun x => -log (q (W x i))) := by
    have hcW : covered P W q := fun x hx _ => h x hx _
    apply le_trans (P.Hcond_le_H W Z)
    rw [← sum_crosspack hcW]
    exact sub_nonneg.mp (kl_nonneg (covered_pack hcW))
  have hE (f : Ω → ℝ) :
      (P.send W).Ex (fun w => (P.after W w).Ex f) = P.Ex f :=
    P.after_Ex_sum W (fun _ => f)
  unfold bill
  simp_rw [Ex_add,Ex_sub,Ex_finset_sum,hE, ← Hcond_after_cond]
  change _ - P.Hcond V _ + _ ≤ (_ - P.Hcond X Z) + _
  rw [sum_split' e (fun i : ι => P.Ex (fun x => -log (q (X x i)))),
    hpart,Hcond_chain,hpart']
  change _ - P.Hcond V (fun x => (Y x,W x)) + _ ≤
    ((∑ i, P.Ex fun x => -log (q (V x i))) + (∑ i, P.Ex fun x => -log (q (W x i))) - _) + _
  linarith

lemma bill_subfamily (tag : α → G) (c : G → ℝ) (q : Law α)
    (P : Law Ω) (X : Ω → ι → α) (U : Ω → G) (h : covered P X q)
    (g : τ → ι) (hg : Injective g) :
    bill tag c q P (keep X g) U ≤ bill tag c q P X U := by
  classical
  let e := (Equiv.sumCongr (Equiv.ofInjective g hg)
      (Equiv.refl {x // ¬ (fun y => y ∈ range g) x})).trans (Equiv.sumCompl (fun y => y ∈ range g))
  let V := keep X (fun i => e (.inl i))
  let W := keep X (fun i => e (.inr i))
  have H :
      bill tag c q P V U ≤ bill tag c q P X U := by
    refine le_trans ?_ (bill_split tag c q P X U h e)
    have hh := bill_through_le tag c q (P.send W) V U (P.after W)
    rw [through_after] at hh
    exact hh
  have heq : V = keep X g := rfl
  rwa [heq] at H

omit [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] in
lemma covered_subfamily {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q)
    (g : τ → ι) : covered P (keep X g) q := fun x hx _ => h x hx _

omit [Fintype ι] [DecidableEq ι] in
lemma covered_after {P : Law Ω} {X : Ω → ι → α} {q : Law α} (h : covered P X q)
    (W : Ω → A) (w : A) (hw : 0 < P.send W w) : covered (P.after W w) X q :=
  fun x hx i => h x ((after_mem hw).mp hx).2 i

end FourierLLogL.Compress

end OAI
