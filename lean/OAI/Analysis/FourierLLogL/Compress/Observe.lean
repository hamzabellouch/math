import OAI.Analysis.FourierLLogL.Compress.Context
/-! # The block observation -/

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A V G E Ω Ω' : Type} [Fintype A] [Fintype G] [AddCommGroup G]
    [Fintype Ω] [Fintype Ω']
set_option linter.unusedSectionVars false


def sumLaw (tag : A → G) (P : Labelled A) (m : ℕ) :=
  (lblP P m).send (fun a => (lblSum tag P m a,lblCtx P m a))

lemma full_pair (p : Law (Ω×Ω')) :
    p.Hcond (fun x => x) Prod.snd = p.Hcond Prod.fst Prod.snd := by
  unfold Hcond
  congr 1
  exact H_partition _ (by simp)

lemma G_as_sum (tag : A → G) (P : Labelled A) (m) :
    fundG tag P m = (sumLaw tag P m).Hcond (fun x => x) Prod.snd := by
  rw [full_pair]
  unfold sumLaw fundG; rw [Hcond_send]

lemma I_single (tag : A → G) (hi : Injective tag) (P : Labelled A) :
    fundG tag P 1 = P.law.Hcond (fun x => x) Prod.snd :=
  (fundG_one _ hi P).trans (full_pair P.law).symm

lemma K_as_sum (tag : A → G) (c : G → ℝ) (P : Labelled A) (m n) :
    fundK tag c P m n = opt n (sumLaw tag P m) Prod.fst Prod.snd (fun x => x) c :=
  (opt_proj Prod.fst Prod.snd (fun x => x) c (lblP P m) (fun a => (lblSum tag P m a,lblCtx P m a)) n).symm

def sumPlus (tag : A → G) (P : Labelled A) (m : ℕ)
    (x : (A × P.obs) × (G × Letters m P.obs)) : G × Letters (m+1) P.obs :=
  (tag x.1.1+x.2.1, appendOne (x.1.2,x.2.2))

def rowPlus (tag : A → G) (P : Labelled A) (m : ℕ)
    (x : (A × P.obs) × (G × Letters m P.obs)) := (x.1.1,sumPlus tag P m x)

lemma sumLaw_succ (tag : A → G) (P : Labelled A) (m) :
    sumLaw tag P (m+1) = (P.law.tensorP (sumLaw tag P m)).send (sumPlus tag P m) := by
  unfold sumLaw
  rw [show lblP P (m+1) = _ from iid_succ P.law m,send_send]
  have hQ := send_tensorP P.law (lblP P m) (fun x => x)
    (fun a => (lblSum tag P m a,lblCtx P m a))
  rw [send_id] at hQ
  rw [← hQ,send_send]
  simp_rw [lbl_succ_sum,lbl_succ_ctx]
  rfl

abbrev observe (tag : A → G) (P : Labelled A) (m : ℕ) : Labelled A :=
  { obs := G × Letters (m+1) P.obs
    law := (P.law.tensorP (sumLaw tag P m)).send (rowPlus tag P m) }

lemma observe_refines (tag : A → G) (P : Labelled A) (m : ℕ) :
    refines (observe tag P m) P := by
  refine ⟨fun x => x.2 0,?_⟩
  dsimp only [observe]
  rw [send_send]
  have he : (fun x : (A × P.obs) × (G × Letters m P.obs) =>
      ((rowPlus tag P m x).1,(rowPlus tag P m x).2.2 0)) = Prod.fst := by
    funext x; rfl
  rw [he, send_fst_tensorP]

lemma rowPlus_inj (tag : A → G) (P : Labelled A) (m : ℕ) :
    Injective (rowPlus tag P m) := by
  rintro ⟨⟨a,b⟩,⟨s,w⟩⟩ ⟨⟨a',b'⟩,⟨s',w'⟩⟩ he
  simp only [rowPlus,sumPlus,Prod.mk.injEq,appendOne,cons_part] at *
  grind

lemma observe_row_ent (tag : A → G) (P : Labelled A) (m : ℕ) :
    (sumLaw tag P (m+1)).Hcond (fun x => x) Prod.snd +
      (observe tag P m).law.Hcond (fun x => x) Prod.snd =
      P.law.Hcond (fun x => x) Prod.snd + (sumLaw tag P m).Hcond (fun x => x) Prod.snd := by
  rw [sumLaw_succ]
  dsimp only [observe]
  let R := P.law
  let Q := sumLaw tag P m
  let Z := R.tensorP Q
  let Y := sumPlus tag P m
  let X := rowPlus tag P m
  have hf {α β : Type} [Fintype α] [Fintype β] (P : Law (α × β)) :
      P.Hcond (fun x => x) Prod.snd = P.entropy - P.H Prod.snd := by
    have h := Hcond_function P (fun x => x) Prod.snd
    rw [H_self] at h; exact h
  simp_rw [hf]
  have hx : Z.H X = Z.entropy :=
    (H_partition Z (X:=X) (Y:=fun x => x) (fun a b => (rowPlus_inj tag P m).eq_iff)).trans (H_self Z)
  have hz : (Z.send Y).H Prod.snd = P.law.H Prod.snd + Q.H Prod.snd := by
    rw [H_send]; refine Eq.trans ?_ (H_tensorP R Q Prod.snd Prod.snd)
    apply H_partition
    intro x y
    simp only [Y,sumPlus,appendOne,cons_part,Prod.mk.injEq]
  change ((Z.send Y).entropy - (Z.send Y).H Prod.snd)+((Z.send X).entropy - (Z.send X).H Prod.snd) = _
  rw [hz,H_send]
  change (Z.H Y- (R.H Prod.snd+Q.H Prod.snd))+(Z.H X-Z.H Y) = _
  rw [hx,show Z.entropy = _ from entropy_tensorP R Q]
  change _ = (R.entropy-_) + (Q.entropy-_)
  ring

lemma observe_cost (tag : A → G) (hi : Injective tag) (P : Labelled A) (m : ℕ) :
    fundG tag P 1 - fundG tag (observe tag P m) 1 =
      fundG tag P (m+1) - fundG tag P m := by
  rw [I_single tag hi,I_single tag hi,G_as_sum tag P (m+1),G_as_sum tag P m]
  linarith [observe_row_ent tag P m]


private lemma observe_cond (tag : A → G) (P : Labelled A) (m r : ℕ)
    (R : Law Ω) (S : Law Ω') (X : Ω → Letters r (A×P.obs))
    (Y : Ω' → Letters r (G × Letters m P.obs)) (g : Ω' → G) :
    let V := R.tensorP S
    let tag' := tag ∘ Prod.fst (β := P.obs)
    let Y' (x : Ω × Ω') (i : Fin r) := sumPlus tag P m (X x.1 i, Y x.2 i)
    let X' (x : Ω × Ω') (i : Fin r) := rowPlus tag P m (X x.1 i, Y x.2 i)
    R.Hcond X (fun x => (ans tag' X (fun _ => 0) x, ctxt Prod.snd X x)) +
      S.Hcond Y (fun x => (ans Prod.fst Y g x, ctxt Prod.snd Y x)) ≤
      V.Hcond Y' (fun x => (ans Prod.fst Y' (fun x => g x.2) x, ctxt Prod.snd Y' x)) +
      V.Hcond X' (fun x => (ans (tag ∘ Prod.fst) X' (fun _ => 0) x, ctxt Prod.snd X' x)) := by
  intro V tag' Y' X'
  let B (x) := (ans tag' X (fun _ => 0) x, ctxt Prod.snd X x)
  let C (x) := (ans Prod.fst Y g x, ctxt Prod.snd Y x)
  let B' (x) := (ans Prod.fst Y' (fun x => g x.2) x, ctxt Prod.snd Y' x)
  let C' (x) := (ans (tag ∘ Prod.fst) X' (fun _ => 0) x, ctxt Prod.snd X' x)
  let W (x : Ω × Ω') := (B x.1,C x.2)
  have hb1 (x : Ω × Ω') : (B' x).1 = (B x.1).1 + (C x.2).1 := by
    unfold B' B C Y'
    unfold ans tot tag' sumPlus
    simp only [Finset.sum_add_distrib,comp_apply,add_zero,add_assoc]
  have hc1 (x : Ω × Ω') : (C' x).1 = (B x.1).1 := rfl
  have H1 : V.Hcond Y' W ≤ V.Hcond Y' B' := by
    apply Hcond_antitone
    intro x y hh
    have h1 : B x.1 = B y.1 := congrArg (fun v => v.1) hh
    have h2 : C x.2 = C y.2 := congrArg Prod.snd hh
    apply Prod.ext
    · rw [hb1,hb1,h1,h2]
    · funext i
      have h3 := congrFun (congrArg Prod.snd h1) i
      have h4 := congrFun (congrArg Prod.snd h2) i
      change appendOne (_,_) = appendOne (_,_)
      exact congrArg appendOne (Prod.ext h3 h4)
  have H2 : V.Hcond X' (fun x => (Y' x,W x)) ≤ V.Hcond X' C' := by
    refine Hcond_antitone _ _ fun x y hh => ?_
    have h1 : W x=W y := congrArg Prod.snd hh
    have h2 : Y' x=Y' y := congrArg Prod.fst hh
    apply Prod.ext
    · rw [hc1,hc1,show B x.1 = B y.1 from congrArg Prod.fst h1]
    · exact h2
  have Hi : V.Hcond (fun x => (X x.1,Y x.2)) W = V.Hcond (fun x => (X' x,Y' x)) W := by
    unfold Hcond
    congr 1
    apply H_partition
    intro a b
    have HH : (X a.1,Y a.2)=(X b.1,Y b.2) ↔ (X' a,Y' a)=(X' b,Y' b) := by
      simp only [X',Y',funext_iff,Prod.mk.injEq,(rowPlus_inj tag P m).eq_iff,forall_and]
      constructor
      · intro ⟨hh,h⟩; simp [hh,h]
      · tauto
    simp only [Prod.mk.injEq,HH]
  rw [Hcond_chain V X' Y' W] at Hi
  have h := Hcond_tensor R S X Y B C
  change V.Hcond (fun x => (X x.1,Y x.2)) W = _ at h
  change R.Hcond X B+S.Hcond Y C ≤ V.Hcond Y' B'+V.Hcond X' C'
  linarith

lemma observe_save (tag : A → G) (c : G → ℝ) (P : Labelled A) (m r : ℕ) :
    fundK tag c P (m+1) r + fundI tag (observe tag P m) r ≤
      fundI tag P r + fundK tag c P m r := by
  classical
  rw [K_as_sum,K_as_sum]
  let tag' : A × P.obs → G := tag ∘ Prod.fst
  let u0 (_ : Unit) := (0:G)
  let c0 (_ : Unit) := (0:ℝ)
  obtain ⟨R,hR,eR⟩ := (opt_spec r P.law tag' Prod.snd u0 c0).1
  let Q := sumLaw tag P m
  obtain ⟨S,hS,eS⟩ := (opt_spec r Q Prod.fst Prod.snd (fun x => x) c).1
  let D := WordSample r (A × P.obs) Unit
  let E := WordSample r (G × Letters m P.obs) G
  let V := R.tensorP S
  let Y (x : D×E) (i : Fin r) := sumPlus tag P m (x.1.1 i, x.2.1 i)
  let X (x : D×E) (i : Fin r) := rowPlus tag P m (x.1.1 i, x.2.1 i)
  let Ue (x : D×E) := x.2.2
  have Hlaw (i : Fin r) :
      V.send (fun x : D×E => (x.1.1 i,x.2.1 i)) = P.law.tensorP Q := by
    rw [show (fun x : D×E => (x.1.1 i,x.2.1 i)) = _ from rfl]
    have HH := send_tensorP R S (readP Prod.fst i) (readP Prod.fst i)
    rw [hR i,hS i] at HH
    exact HH
  have hY : hasRows (sumLaw tag P (m+1)) V Y := by
    intro i
    rw [sumLaw_succ,show P.law.tensorP (sumLaw tag P m) = _ from (Hlaw i).symm,
      send_send]; rfl
  have hX : hasRows (observe tag P m).law V X := by
    intro i; dsimp only [observe]
    rw [show P.law.tensorP (sumLaw tag P m) = _ from (Hlaw i).symm,send_send]; rfl
  let tag'' : (A × (observe tag P m).obs) → G := tag ∘ Prod.fst
  refine (add_le_add (opt_le_rent _ _ _ c _ V Y Ue hY)
    (opt_le_rent tag'' Prod.snd u0 c0 _ V X (fun _ => ()) hX)).trans ?_
  change _ ≤ opt _ _ tag' _ u0 c0 + opt _ Q _ _ _ _
  rw [← eR,← eS]
  dsimp only []
  unfold rent
  rw [rent_first hX,rent_first hY,rent_first hS,rent_first hR]
  have H := observe_cond tag P m r R S Prod.fst Prod.fst Prod.snd
  have H0 := observe_row_ent tag P m

  have heq : V.Ex (fun a => c (Ue a)) = S.Ex (fun a => c a.2) := by
    dsimp only [V,Ue]
    rw [Ex_tensorP]; exact Ex_const R (S.Ex (fun a => c a.2))
  dsimp only [u0,c0,X,Y,Ue,tag'',tag',V,Q,id_eq,comp_apply] at *
  simp only [Ex_const]
  have hmul := congrArg (fun t : ℝ => (Fintype.card (Fin r):ℝ)*t) H0
  linarith

end FourierLLogL.Compress

end OAI
