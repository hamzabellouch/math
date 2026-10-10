import OAI.Analysis.FourierLLogL.Compress.Rent
/-! # Data processing for contextual cost -/

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A B V W G E Ω Ω' : Type} [Fintype A] [Fintype B]
    [Fintype V] [Fintype W] [Fintype G] [Fintype E] [Nonempty E]
    [Fintype Ω] [Fintype Ω'] [AddCommGroup G] {n : ℕ}
set_option linter.unusedSectionVars false

lemma Hcond_congr {P : Law Ω} {X Y : Ω → A} {W W' : Ω → B}
    (h : ∀ a, 0 < P a → X a = Y a) (h' : ∀ a, 0 < P a → W a = W' a) :
    P.Hcond X W = P.Hcond Y W' := by
  unfold Hcond
  rw [H_congr_mem P h']
  congr 1
  refine H_congr_mem P fun a ha => ?_
  rw [h a ha,h' a ha]

lemma rent_proj_eq (tag : B → G) (w : B → V) (u : E → G) (c : E → ℝ)
    (P : Law Ω) (X : Ω → Letters n A) (U : Ω → E) (σ : A → B) :
    let Y := ctxt σ X
    rent (tag ∘ σ) (w ∘ σ) u c P X U =
      rent tag w u c P Y U +
      ((∑ i, P.Hcond (readP X i) (readP Y i)) -
        P.Hcond X (fun x => (Y x, ans tag Y (fun a => u (U a)) x))) := by
  intro Y
  let Z := ans tag Y (fun a => u (U a))
  have h1 (i : Fin n) :
      P.Hcond (readP X i) ((w ∘ σ) ∘ readP X i) =
      P.Hcond (readP X i) (readP Y i) + P.Hcond (readP Y i) (w ∘ readP Y i) := by
    let R := (w ∘ readP Y i)
    have he := Hcond_reduce P (readP X i) R σ
    change P.Hcond _ R = _ + P.Hcond (readP Y i) R
    rw [he]; congr 1
    apply Hcond_right_partition
    simp only [R,Y,ctxt,readP,comp_apply,Prod.mk.injEq]
    grind
  have h2 :
      P.Hcond X (fun x => (Z x,ctxt w Y x)) =
        P.Hcond X (fun x => (Y x,Z x)) +
        P.Hcond Y (fun x => (Z x,ctxt w Y x)) := by
    nth_rw 1 [Hcond_reduce P X _ (fun v i => σ (v i))]
    congr 1
    apply Hcond_right_partition
    intro a b
    simp only [Prod.mk.injEq,Y,ctxt,funext_iff]
    grind
  unfold rent
  change _ - P.Hcond X (fun x => (Z x,ctxt w Y x))+_ = _
  rw [h2]
  simp_rw [h1,Finset.sum_add_distrib]
  dsimp only [Z]
  ring

lemma rent_projection (tag : B → G) (w : B → V) (u : E → G) (c : E → ℝ)
    (P : Law Ω) (X : Ω → Letters n A) (U : Ω → E) (σ : A → B) :
    rent tag w u c P (ctxt σ X) U ≤ rent (tag ∘ σ) (w ∘ σ) u c P X U := by
  rw [rent_proj_eq]
  refine le_add_of_nonneg_right (sub_nonneg.mpr ?_)
  let Y := ctxt σ X
  let Z (x : Ω) := (Y x,ans tag Y (fun x => u (U x)) x)
  refine (Hcond_vec_le P X Z).trans (Finset.sum_le_sum fun i _ => ?_)
  apply Hcond_antitone
  intro a b h
  exact congrFun (congrArg Prod.fst h) i

lemma rent_congr_mem (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ)
    (P : Law Ω) {X Y : Ω → Letters n A} (U : Ω → E)
    (h : ∀ x, 0 < P x → X x=Y x) :
    rent tag w u c P X U = rent tag w u c P Y U := by
  unfold rent
  suffices H : ∑ i, P.Hcond (readP X i) (w ∘ readP X i) =
      ∑ i, P.Hcond (readP Y i) (w ∘ readP Y i) by
    have hh (x : Ω) (hx : 0 < P x) :
        (ans tag X (fun x => u (U x)) x, ctxt w X x) =
          (ans tag Y (fun x => u (U x)) x, ctxt w Y x) := by
      unfold ans ctxt; rw [h x hx]
    rw [H]
    have ht := Hcond_congr h (W:=fun x => (ans tag X (fun x => u (U x)) x, ctxt w X x))
      (W':=fun x => (ans tag Y (fun x => u (U x)) x, ctxt w Y x)) hh
    rw [ht]
  refine Finset.sum_congr rfl fun i _ => ?_
  apply Hcond_congr
  · exact fun x hx => congrFun (h x hx) _
  · exact fun x hx => congrArg w (congrFun (h x hx) _)

lemma opt_proj (tag : B → G) (w : B → V) (u : E → G) (c : E → ℝ)
    (p : Law A) (σ : A → B) (n : ℕ) :
    opt n (p.send σ) tag w u c = opt n p (tag ∘ σ) (w ∘ σ) u c := by
  classical
  apply le_antisymm
  · obtain ⟨P,hP,he⟩ := (opt_spec n p (tag ∘ σ) (w ∘ σ) u c).1
    rw [← he]
    let X : WordSample n A E → Letters n A := Prod.fst
    exact (opt_le_rent tag w u c (p.send σ) P (ctxt σ X) Prod.snd fun i => by
      rw [← hP i,send_send]; rfl).trans (rent_projection tag w u c P _ _ _)
  obtain ⟨P,hP,he⟩ := (opt_spec n (p.send σ) tag w u c).1
  let X : WordSample n B E → Letters n B := Prod.fst
  let Q x := pack (fun i : Fin n => p.after σ (X x i))
  let R := P.withNext Q
  let Y : WordSample n B E × (Letters n A) → Letters n A := Prod.snd
  let B0 (z : WordSample n B E × Letters n A) := X z.1
  let error (z : WordSample n B E × Letters n A) := z.1.2
  have hr : hasRows p R Y := by
    intro i
    apply ext_of_Ex; intro f
    rw [Ex_send]
    change R.Ex (fun z => f (z.2 i)) = p.Ex f
    unfold R
    rw [Ex_withNext]
    simp_rw [Q, Ex_pack_proj _ i f]
    change P.Ex (fun x => (p.after σ (readP X i x)).Ex f) = _
    rw [← Ex_send P (readP X i) (fun b => (p.after σ b).Ex f),show P.send (readP X i) = _ from hP i]
    exact p.after_Ex_sum σ (fun _ => f)
  have heq (x : WordSample n B E × Letters n A) (hx : 0 < R x) : ctxt σ Y x = B0 x := by
    rcases x with ⟨a,b⟩
    change 0 < P a * Q a b at hx
    have hpos : 0 < P a ∧ 0 < Q a b :=
      (mul_pos_iff.mp hx).resolve_right (by intro hh; linarith [hh.1,P.nonneg a])
    funext i
    have hi := (pack_pos (fun i => p.after σ (X a i)) b).mp hpos.2 i
    have hmarg := P.send_pos (readP X i) hpos.1
    rw [show P.send (readP X i) = _ from hP i] at hmarg
    exact ((after_mem hmarg).mp hi).1
  have hsrc : rent tag w u c R B0 error = opt n (p.send σ) tag w u c := by
    have h1 := send_fst_withNext P Q
    have hi := rent_send tag w u c R X Prod.snd Prod.fst
    change rent tag w u c (R.send Prod.fst) X Prod.snd = _ at hi
    rw [h1] at hi
    exact hi.symm.trans he
  refine (opt_le_rent (tag ∘ σ) (w ∘ σ) u c p R Y error hr).trans ?_
  rw [rent_proj_eq]
  let B1 := ctxt σ Y
  let Z (b : WordSample n B E × Letters n A) :=
    (B1 b, ans tag B1 (fun x => u (error x)) b)
  let Z0 (b : WordSample n B E × Letters n A) :=
    (B0 b, ans tag B0 (fun x => u (error x)) b)
  change rent tag w u c R B1 error + (_ - R.Hcond Y Z) ≤ _
  rw [rent_congr_mem tag w u c R error heq,hsrc]
  suffices H : ∑ i, R.Hcond (readP Y i) (readP B1 i) ≤ R.Hcond Y Z by linarith
  have hZ : R.Hcond Y Z = R.Hcond Y Z0 :=
    Hcond_congr (fun _ _ => rfl) fun x hx => by unfold Z Z0 ans; rw [show B1 x = B0 x from heq x hx]
  rw [hZ]
  apply le_trans (b:=R.Hcond Y Prod.fst)
  · have H1 : R.Hcond Y Prod.fst = P.Ex (fun x => (Q x).entropy) := by
      have H := Hcond_withNext' P Q (fun _ y => y)
      simpa only [H_self] using H
    have H2 (i : Fin n) : R.Hcond (readP Y i) (readP B1 i) = p.Hcond (fun a => a) σ := by
      rw [← hr i]
      rw [Hcond_send]; rfl
    have H3 (i : Fin n) :
        P.Ex (fun x => (p.after σ (X x i)).entropy) = p.Hcond (fun a => a) σ := by
      rw [Hcond_after]
      simp_rw [H_self]
      have hi := hP i
      rw [← hi,Ex_send]; rfl
    rw [H1]; simp_rw [Q,entropy_pack,H2,Ex_finset_sum,H3]; exact le_rfl
  · apply Hcond_antitone
    rintro ⟨a,b⟩ ⟨a',b'⟩ h
    cases (show a=a' from h)
    rfl

lemma opt_refined (tag : B → G) (w : B → V) (w' : A → W) (u : E → G) (c : E → ℝ)
    (p : Law A) (σ : A → B) (n : ℕ) (g : W → V) (h : w ∘ σ = g ∘ w') :
    opt n p (tag ∘ σ) w' u c ≤ opt n (p.send σ) tag w u c := by
  rw [opt_proj tag w]
  obtain ⟨P,hP,he⟩ := (opt_spec n p (tag ∘ σ) (w ∘ σ) u c).1
  exact (opt_le_rent _ _ _ _ p P _ _ hP).trans
    ((rent_antitone _ w' (w ∘ σ) u c g h P Prod.fst Prod.snd).trans he.le)

end FourierLLogL.Compress

end OAI
