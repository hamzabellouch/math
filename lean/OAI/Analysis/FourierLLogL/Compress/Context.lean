import OAI.Analysis.FourierLLogL.Compress.Projection
import OAI.Analysis.FourierLLogL.Compress.Select

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A V W G E α β Ω Ω' : Type} [Fintype A] [Fintype G] [AddCommGroup G]
    [Fintype α] [Fintype β] [Fintype Ω] [Fintype Ω'] [Fintype V] [Fintype W]
    [Fintype E] [Nonempty E] {n : ℕ}
set_option linter.unusedSectionVars false

/-- Numerical Context State. -/
structure Labelled (A : Type) [Fintype A] where
  obs : Type
  [fObs : Fintype obs]
  law : Law (A × obs)

attribute [instance] Labelled.fObs

def initial (p : Law A) : Labelled A := {obs := Unit, law:=p.send (fun x => (x,()))}

def refines (P Q : Labelled A) : Prop :=
  ∃ u : P.obs → Q.obs, P.law.send (fun a => (a.1,u a.2)) = Q.law

lemma refines_refl (p : Labelled A) : refines p p := by
  refine ⟨id,?_⟩; exact send_id p.law

lemma refines_trans {p q r : Labelled A} :
    refines p q → refines q r → refines p r := by
  rintro ⟨u,hu⟩ ⟨v,hv⟩
  rw [← hu,send_send] at hv
  exact ⟨v ∘ u,hv⟩

def lblSum (tag : A → G) (W : Labelled A) (m : ℕ) (x : Letters m (A × W.obs)) : G :=
  tot (tag ∘ Prod.fst) x
def lblCtx (W : Labelled A) (m : ℕ) (x : Letters m (A × W.obs)) : Letters m W.obs :=
  fun i => (x i).2

/-- m-letter block of joint letter-and-context pairs, iid. -/
def lblP (W : Labelled A) (m : ℕ) := iid W.law m

/-- Conditional entropy of total sum. -/
def fundG (tag : A → G) (p : Labelled A) (m : ℕ) :=
  (lblP p m).Hcond (lblSum tag p m) (lblCtx p m)

/-- Conditional exact cost. -/
def fundI (tag : A → G) (P : Labelled A) (r : ℕ) :=
  opt r P.law (tag ∘ Prod.fst) Prod.snd (fun _ : Unit => (0:G)) (fun _ => 0)

/-- Conditional m-block noisy cost. -/
def fundK (tag : A → G) (c : G → ℝ) (P : Labelled A) (m r : ℕ) :=
  opt r (lblP P m) (lblSum tag P m) (lblCtx P m) id c

lemma I_anti (tag : A → G) {P Q : Labelled A} (h : refines P Q) (r : ℕ) :
    fundI tag P r ≤ fundI tag Q r := by
  obtain ⟨u,hu⟩ := h
  unfold fundI
  rw [← hu]
  let f (x : A×P.obs) := (x.1,u x.2)
  exact opt_refined (tag ∘ Prod.fst) Prod.snd Prod.snd (fun _ : Unit => 0) (fun _ => 0) P.law f r u rfl

lemma K_anti (tag : A → G) (c : G → ℝ) {P Q : Labelled A}
    (h : refines P Q) (m r : ℕ) : fundK tag c P m r ≤ fundK tag c Q m r := by
  obtain ⟨u,hu⟩ := h
  let X (x : A × P.obs) := (x.1,u x.2)
  let f (x : Letters m _) i := X (x i)
  have H : lblP Q m = (lblP P m).send f := by
    unfold lblP iid; rw [show Q.law = _ from hu.symm]
    exact (sendPack (fun _ : Fin m => P.law) (fun _ => X)).symm
  unfold fundK
  rw [H]
  exact opt_refined (lblSum tag Q m) (lblCtx Q m) (lblCtx P m) id c (lblP P m) f r (fun x i => u (x i)) rfl

lemma G_anti (tag : A → G) {P Q : Labelled A} (h : refines P Q)
    (m : ℕ) : fundG tag P m ≤ fundG tag Q m := by
  obtain ⟨u,hu⟩ := h
  let X (x : A × P.obs) := (x.1,u x.2)
  let f (x : Letters m _) i := X (x i)
  have H : lblP Q m = (lblP P m).send f := by
    unfold lblP iid; rw [show Q.law = _ from hu.symm]
    exact (sendPack (fun _ : Fin m => P.law) (fun _ => X)).symm
  unfold fundG
  rw [H,Hcond_send]
  apply Hcond_antitone
  intro a b hh
  funext i
  exact congrArg u (congrFun hh i)

lemma fundG_one (tag : A → G) (hi : Injective tag) (P : Labelled A) :
    fundG tag P 1 = P.law.Hcond Prod.fst Prod.snd := by
  let Q := lblP P 1
  have h : Q.send (fun x => x 0) = P.law := marginalPack _ _
  rw [← h,Hcond_send]
  unfold fundG Hcond
  congr 1
  · refine H_partition _ fun a b => ?_
    unfold lblSum lblCtx tot
    simp only [Fin.sum_univ_one,comp_apply,Prod.mk.injEq,hi.eq_iff,funext_iff]
    simp [Fin.forall_fin_one]
  · refine H_partition _ fun a b => ?_
    simp [funext_iff,lblCtx, Fin.forall_fin_one]

def appendOne {m : ℕ} (p : A × Letters m A) : Letters (m+1) A := Fin.cons p.1 p.2

lemma iid_succ (P : Law A) (m : ℕ) :
    iid P (m+1) = (P.tensorP (iid P m)).send appendOne := by
  apply ext_by_products
  intro f
  dsimp only [iid]
  rw [Ex_send,Ex_tensorP]
  rw [pack_Ex_prod _ f]
  simp_rw [Fin.prod_univ_succ]
  unfold appendOne
  simp only [Fin.cons_zero,Fin.cons_succ]
  simp_rw [Ex_lmul,pack_Ex_prod _ (fun i : Fin m => f i.succ),Ex_mul]

lemma cons_part {m : ℕ} {a b : A} {x y : Letters m A} :
    (Fin.cons a x : Letters (m+1) A) = Fin.cons b y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0,by funext i; simpa using congrFun h i.succ⟩
  · rintro ⟨rfl,rfl⟩; rfl


lemma Hcond_tensor (P : Law Ω) (Q : Law Ω') (X : Ω → α) (Z : Ω' → β)
    (Y : Ω → V) (T : Ω' → W) :
    (P.tensorP Q).Hcond (fun x => (X x.1,Z x.2)) (fun x => (Y x.1,T x.2)) =
      P.Hcond X Y + Q.Hcond Z T := by
  unfold Hcond
  rw [H_partition (X:=fun (x:Ω×Ω') => ((X x.1,Z x.2),(Y x.1,T x.2)))
    (Y:=fun x => ((X x.1,Y x.1),(Z x.2,T x.2))) _ (fun _ _ => by simp; tauto)]
  rw [H_tensorP P Q (fun x => (X x,Y x)) (fun x => (Z x,T x)),H_tensorP]; ring

lemma Hcond_tensor_right (P : Law Ω) (Q : Law Ω') (Z : Ω' → β)
    (Y : Ω → V) (T : Ω' → W) :
    (P.tensorP Q).Hcond (fun x => Z x.2) (fun x => (Y x.1,T x.2)) = Q.Hcond Z T := by
  let X (_x : Ω) := ()
  rw [show Q.Hcond Z T = P.Hcond X Y + Q.Hcond Z T by
        rw [Hcond_determined (P:=P) (X:=X) (W:=Y) (fun _ _ _ => rfl)]; ring,
    ← Hcond_tensor]
  unfold Hcond
  congr 1
  apply H_partition
  simp only [Prod.mk.injEq, X]; tauto

lemma lbl_succ_sum (tag : A → G) (P : Labelled A) (m : ℕ)
    (x : (A×P.obs) × Letters m (A × P.obs)) :
    lblSum tag P (m+1) (appendOne x) = tag x.1.1 + lblSum tag P m x.2 := by
  unfold lblSum tot; rw [Fin.sum_univ_succ]; rfl

lemma lbl_succ_ctx (P : Labelled A) (m : ℕ)
    (x : (A×P.obs) × Letters m (A × P.obs)) :
    lblCtx P (m+1) (appendOne x) = appendOne (x.1.2,lblCtx P m x.2) := by
  funext i
  cases i using Fin.cases <;> simp [lblCtx,appendOne]

lemma fundG_succ (tag : A → G) (P : Labelled A) (m : ℕ) :
    let Q := P.law.tensorP (lblP P m)
    let X (x : (A×P.obs) × Letters m (A×P.obs)) := tag x.1.1 + lblSum tag P m x.2
    let Z (x : (A×P.obs) × Letters m (A×P.obs)) := (x.1.2,lblCtx P m x.2)
    fundG tag P (m+1) = Q.Hcond X Z := by
  intro Q X Z
  unfold fundG
  rw [show lblP P (m+1)=Q.send appendOne from iid_succ P.law m,Hcond_send]
  simp_rw [lbl_succ_sum,lbl_succ_ctx]
  refine Hcond_right_partition _ X (fun x y => ?_)
  unfold appendOne Z
  simp only [cons_part,Prod.mk.injEq]

lemma fundG_mono (tag : A → G) (P : Labelled A) : Monotone (fundG tag P) := by
  refine monotone_nat_of_le_succ fun i => ?_
  rw [fundG_succ]
  let Q := lblP P i
  let R := P.law.tensorP Q
  let W (x : (A×P.obs) × Letters i (A×P.obs)) := (x.1, lblCtx P i x.2)
  let X (x : (A×P.obs) × Letters i (A×P.obs)) := tag x.1.1 + lblSum tag P i x.2
  have hr : R.Hcond X W = R.Hcond (fun x => lblSum tag P i x.2) W := by
    unfold Hcond
    congr 1
    apply H_partition
    intro x y
    simp only [W,X,Prod.mk.injEq]
    constructor
    · rintro ⟨h,h1,h2⟩; rw [h1] at h; exact ⟨add_left_cancel h,h1,h2⟩
    · rintro ⟨h,h1,h2⟩; exact ⟨by rw [h,h1],h1,h2⟩
  have he : R.Hcond (fun x => lblSum tag P i x.2) W = fundG tag P i :=
    Hcond_tensor_right P.law Q (lblSum tag P i) (fun x => x) (lblCtx P i)
  change fundG tag P i ≤ R.Hcond X _
  rw [← hr.trans he]
  apply Hcond_antitone
  intro x y h
  have H1 := congrArg Prod.fst h
  have H2 := congrArg Prod.snd h
  exact Prod.ext (show x.1.2=y.1.2 from congrArg Prod.snd H1) (show lblCtx P i x.2=lblCtx P i y.2 from H2)

lemma opt_succ (p : Law A) (tag : A → G) (w : A → V)
    (u : E → G) (c : E → ℝ) (n : ℕ) :
    opt n p tag w u c ≤ opt (n+1) p tag w u c := by
  obtain ⟨P,hP,he⟩ := (opt_spec (n+1) p tag w u c).1
  let X : WordSample (n+1) A E → Letters (n+1) A := Prod.fst
  let U : WordSample (n+1) A E → E := Prod.snd
  let Y (x : _) (i : Fin n) := X x i.succ
  let A' := readP X 0
  let W (x) := ans tag X (fun x => u (U x)) x
  let Z (x) := ans tag Y (fun x => u (U x)) x
  let WX (x : WordSample (n+1) A E) := (W x,ctxt w X x)
  let WY (x : WordSample (n+1) A E) := (Z x,ctxt w Y x)
  have hr : rent tag w u c P Y U ≤ rent tag w u c P X U := by
    have h :
        P.Hcond X WX = P.Hcond Y (fun x => (A' x,WX x))+P.Hcond A' WX := by
      rw [← Hcond_chain]
      unfold Hcond
      congr 1
      refine H_partition _ fun x y => ?_
      have hX : X x = X y ↔ Y x = Y y ∧ A' x = A' y := by
        constructor
        · intro h; dsimp only [Y,A',readP]; rw [h]; exact ⟨rfl,rfl⟩
        · rintro ⟨h1,h2⟩; funext i
          cases i using Fin.cases with
          | zero => exact h2
          | succ j => exact congrFun h1 j
      simp only [Prod.mk.injEq,hX]
    have hc : P.Hcond Y (fun x => (A' x,WX x)) ≤ P.Hcond Y WY := by
      refine Hcond_antitone _ _ fun x y hh => ?_
      change (Z x,ctxt w Y x) = _
      have heW (x) : W x = tag (A' x)+Z x := by
        unfold W Z ans tot
        rw [Fin.sum_univ_succ,add_assoc]
        rfl
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      have h3 : W x=W y := congrArg (fun a : G×_ => a.1) h2
      have h4 : ctxt w X x=ctxt w X y := congrArg (fun a : G×_ => a.2) h2
      rw [heW,heW, show A' x = A' y from h1] at h3
      exact Prod.ext (add_left_cancel h3) (funext fun i => congrFun h4 i.succ)
    have hd : P.Hcond A' WX ≤ P.Hcond A' (w ∘ A') := by
      refine Hcond_antitone P _ (fun x y hh => ?_)
      have he : ctxt w X x = ctxt w X y := congrArg (fun a : G×_ => a.2) hh
      exact congrFun he 0
    unfold rent
    refine add_le_add_left ?_ _
    change _ - P.Hcond Y WY ≤ _ - P.Hcond X WX
    rw [Fin.sum_univ_succ,h]
    have hEq (i : Fin n) : readP X i.succ = readP Y i := rfl
    simp_rw [hEq]
    change _ ≤ P.Hcond A' (w ∘ A')+_ - _
    linarith
  exact (opt_le_rent tag w u c p P Y U fun i => hP i.succ).trans (hr.trans he.le)

lemma fundI_mono (tag : A → G) (P : Labelled A) : Monotone (fundI tag P) :=
  monotone_nat_of_le_succ (fun n => opt_succ P.law (tag ∘ Prod.fst) Prod.snd
    (fun _ : Unit => 0) (fun _ => 0) n)

end FourierLLogL.Compress

end OAI
