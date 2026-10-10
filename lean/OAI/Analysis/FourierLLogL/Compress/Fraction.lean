import OAI.Analysis.FourierLLogL.Compress.Observe
/-! # Partial refinements -/

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {V W Y Ω G A : Type} [Fintype A] [Fintype V] [Fintype W] [Fintype G]
    [Fintype Y] [Fintype Ω] [AddCommGroup G]

lemma mix_send (P Q : Law Ω) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (X : Ω → A) :
    (mixture P Q t h0 h1).send X = mixture (P.send X) (Q.send X) t h0 h1 := by
  apply ext_of_Ex; intro f
  simp_rw [mixture_Ex,Ex_send,mixture_Ex]

lemma marked_cond (P Q : Law Ω) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (X : Ω → A) (W : Ω → V) (f : V → Bool)
    (hP : ∀ x, 0 < P x → f (W x) = true)
    (hQ : ∀ x, 0 < Q x → f (W x) = false) :
    (mixture P Q t h0 h1).Hcond X W =
      t*P.Hcond X W+(1-t)*Q.Hcond X W := by
  rw [mixture_eq_through]
  let B := coinP t h0 h1
  let K (b : Bool) := if b then P else Q
  let R := withNext B K
  change (through B K).Hcond X W = _
  have hy (z : Bool × Ω) (hz : 0 < R z) : f (W z.2) = z.1 := by
    obtain ⟨b,x⟩ := z
    change 0 < B b * K b x at hz
    have hx : 0 < K b x := pos_of_mul_pos_right hz (B.nonneg b)
    cases b
    · exact hQ x hx
    · exact hP x hx
  let X' (z : Bool×Ω) := X z.2
  let W' (z : Bool×Ω) := W z.2
  rw [← send_snd_withNext B K,Hcond_send]
  have HH : R.Hcond X' W' = R.Hcond X' (fun z => (z.1, W' z)) := by
    calc
      _ = R.Hcond X' (fun z => (f (W' z),W' z)) :=
        Hcond_right_partition _ _ (fun _ _ => by simp; grind)
      _ = _ := Hcond_congr (X:=X') (fun _ _ => rfl)
        (W:=fun z => (f (W' z),W' z)) fun z hz => by rw [show _=z.1 from hy z hz]
  have H :=
    Hcond_withNext B K (fun _ => X) (fun _ => W)
  change R.Hcond X' W' = _
  rw [HH,show R.Hcond X' _ = _ from H,coinP_Ex]
  rfl

def retag (f : V → W) (x : A×V) : A×W := (x.1,f x.2)

omit [Fintype A] [Fintype V] [Fintype W] in
lemma retag_inj (f : V → W) (hf : Injective f) :
    Injective (retag (A:=A) f) := by
  rintro ⟨x,a⟩ ⟨y,b⟩ h
  simpa only [retag,Prod.mk.injEq,hf.eq_iff] using h

abbrev blend (P Q : Labelled A) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Labelled A :=
  { obs := P.obs ⊕ Q.obs
    law := mixture (P.law.send (retag Sum.inl)) (Q.law.send (retag Sum.inr)) t h0 h1 }

lemma blend_refines (P Q R : Labelled A) (hp : refines P R) (hq : refines Q R)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : refines (blend P Q t h0 h1) R := by
  obtain ⟨u,hu⟩ := hp; obtain ⟨v,hv⟩ := hq
  refine ⟨Sum.elim u v,?_⟩
  dsimp only [blend]
  rw [mix_send,send_send,send_send]
  apply Law.ext; intro a
  rw [mixture_apply]
  dsimp only [retag,Sum.elim_inl,Sum.elim_inr]
  rw [hu,hv]; ring

lemma retag_Hcond (P : Law (A×V)) (f : V→W) (h : Injective f) :
    (P.send (retag f)).Hcond (fun x => x) Prod.snd = P.Hcond (fun x => x) Prod.snd := by
  rw [full_pair,full_pair,Hcond_send]
  apply Hcond_right_partition
  exact fun _ _ => h.eq_iff

lemma blend_H (P Q : Labelled A) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (blend P Q t h0 h1).law.Hcond (fun a => a) Prod.snd =
      t*P.law.Hcond (fun a => a) Prod.snd+(1-t)*Q.law.Hcond (fun a => a) Prod.snd := by
  dsimp only [blend]
  let K := Sum.elim (fun _ : P.obs => true) (fun _ : Q.obs => false)
  rw [marked_cond _ _ t h0 h1 _ _ K, retag_Hcond _ (Sum.inl : P.obs → P.obs ⊕ Q.obs)
    Sum.inl_injective,retag_Hcond _ (Sum.inr : Q.obs → P.obs ⊕ Q.obs) Sum.inr_injective]
  all_goals
    intro x hx
    obtain ⟨y,rfl,_⟩ := (send_pos_iff _ _ _).mp hx
    rfl


def upRows (n : ℕ) (f : V→W) (x : WordSample n (A×V) Unit) :
    WordSample n (A×W) Unit := (ctxt (retag f) Prod.fst x, x.2)

def packedH (n : ℕ) (tag : A→G) (W : Type) [Fintype W] (x : WordSample n (A×W) Unit) :=
  (ans (tag ∘ Prod.fst) Prod.fst (fun _ => 0) x,ctxt Prod.snd Prod.fst x)

lemma retag_trial (n : ℕ) (tag : A → G) (P : Law (WordSample n (A×V) Unit))
    (f : V → W) (h : Injective f) :
    (P.send (upRows n f)).Hcond Prod.fst (packedH n tag W) =
      P.Hcond Prod.fst (packedH n tag V) := by
  rw [Hcond_send]
  have hc (x y : WordSample n (A×V) Unit) :
      packedH n tag W (upRows n f x) = packedH n tag W (upRows n f y) ↔
      packedH n tag V x = packedH n tag V y := by
    simp only [packedH,upRows,ctxt,ans,tot,comp_apply,retag, Prod.mk.injEq,funext_iff,h.eq_iff]
  unfold Hcond
  congr 1
  · refine H_partition _ fun x y => ?_
    have heq : (upRows n f x).1=(upRows n f y).1 ↔ x.1=y.1 := by
      simp only [funext_iff,upRows,ctxt,(retag_inj f h).eq_iff]
    rw [show (Prod.fst x) = x.1 from rfl]
    constructor
    · intro hh
      replace hh := Prod.mk.inj hh
      exact Prod.ext (heq.mp hh.1) ((hc x y).mp hh.2)
    · intro hh
      replace hh := Prod.mk.inj hh
      exact Prod.ext (heq.mpr hh.1) ((hc x y).mpr hh.2)
  · exact H_partition _ hc

lemma retag_trial_rows (n : ℕ) (p : Law (A × V)) (P : Law (WordSample n (A × V) Unit))
    (h : hasRows p P Prod.fst) (f : V → W) :
    hasRows (p.send (retag f)) (P.send (upRows n f)) Prod.fst := by
  intro i; rw [← h i,send_send,send_send]; rfl

lemma exact_rent (n : ℕ) (S : Labelled A) (tag : A → G)
    (P : Law (WordSample n (A×S.obs) Unit)) (h : hasRows S.law P Prod.fst) :
    rent (tag ∘ Prod.fst) Prod.snd (fun _ : Unit => (0:G)) (fun _ => 0) P Prod.fst Prod.snd =
      (n:ℝ) * S.law.Hcond (fun a => a) Prod.snd - P.Hcond Prod.fst (packedH n tag _) := by
  rw [rent,rent_first h, Fintype.card_fin]
  rw [Ex_const,add_zero]; rfl

lemma blend_I (tag : A → G) (P Q : Labelled A) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (n : ℕ) : fundI tag (blend P Q t h0 h1) n ≤ t*fundI tag P n+(1-t)*fundI tag Q n := by
  let u0 (_ : Unit) := (0:G)
  let c0 (_ : Unit) := (0:ℝ)
  obtain ⟨R,hR,eR⟩ := (opt_spec n P.law (tag ∘ Prod.fst) Prod.snd u0 c0).1
  obtain ⟨S,hS,eS⟩ := (opt_spec n Q.law (tag ∘ Prod.fst) Prod.snd u0 c0).1
  let B := blend P Q t h0 h1
  let p := (Sum.inl : P.obs → P.obs ⊕ Q.obs)
  let q := (Sum.inr : Q.obs → P.obs ⊕ Q.obs)
  let T := mixture (R.send (upRows n p)) (S.send (upRows n q)) t h0 h1
  have hT : hasRows (blend P Q t h0 h1).law T Prod.fst := by
    intro i
    unfold T
    rw [mix_send, retag_trial_rows n _ R hR p i, retag_trial_rows n _ S hS q i]
  apply le_trans (opt_le_rent (tag ∘ Prod.fst) Prod.snd u0 c0 _ T _ Prod.snd hT)
  change _ ≤ t*opt n P.law _ _ u0 c0+(1-t)*opt n Q.law _ _ u0 c0
  rw [← eR,← eS]
  dsimp only [u0,c0]
  rw [exact_rent n (blend P Q t h0 h1) tag T hT, exact_rent n P tag R hR,exact_rent n Q tag S hS]
  have hp := Hcond_mixture_ge (R.send (upRows n p)) (S.send (upRows n q)) t h0 h1
    Prod.fst (packedH n tag _)
  rw [retag_trial n tag R p Sum.inl_injective, retag_trial n tag S q Sum.inr_injective] at hp
  rw [blend_H]
  unfold T
  linarith

lemma blend_G1 (tag : A→G) (hi : Injective tag) (P Q : Labelled A)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    fundG tag (blend P Q t h0 h1) 1 = t*fundG tag P 1+(1-t)*fundG tag Q 1 := by
  rw [I_single tag hi, I_single tag hi, I_single tag hi]; exact blend_H P Q t h0 h1

end FourierLLogL.Compress

end OAI
