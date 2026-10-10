import OAI.Analysis.FourierLLogL.Finite.Comparison

/-! # Entropy cost of changes of signal -/
open Function Set Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Law
open Real
variable {α β γ η : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype η]
open scoped Classical

/-- expected entropy remaining conditional on a signal channel -/
def privateH (P : Law α) (k : α → Law β) :=
    (P.withNext k).Hcond Prod.fst Prod.snd

lemma privateH_le (P : Law α) (k : α → Law β) : P.privateH k ≤ P.entropy := by
  have H := (P.withNext k).Hcond_le_H Prod.fst Prod.snd
  exact (show _ ≤ _ from H).trans (le_of_eq (by
    unfold Law.H; rw [send_fst_withNext]))

lemma signal_cost (P : Law α) (k : α → Law β) :
    (P.withNext k).Hcond Prod.snd Prod.fst = P.Ex fun x => (k x).entropy := by
  unfold Hcond; rw [H_pair_rev]; simp_rw [Prod.mk.eta,H_self,entropy_withNext,H,send_fst_withNext]; ring

lemma privateH_const (P : Law α) (Q : Law β) :
    P.privateH (fun _ => Q) = P.entropy := by
  unfold privateH Hcond
  simp only [Prod.mk.eta,H_self]
  rw [entropy_withNext,Ex_const]
  unfold H
  rw [show P.withNext (fun _ => Q) = P.tensorP Q from rfl,send_snd_tensorP]; ring

lemma Hcond_compare (P : Law α) (Y : α → β) (X : α → γ) (q : γ → Law β)
    (hq : ∀ i, 0 < P i → 0 < q (X i) (Y i)) :
    P.Hcond Y X ≤ P.Ex fun i => -log (q (X i) (Y i)) := by
  rw [Hcond_after]
  rw [← after_Ex_sum P X (fun x i => -log (q x (Y i)))]
  refine Ex_mono_mem _ fun x hx => ?_
  rw [← Ex_send (P.after X x) Y (fun i => -log (q x i))]
  apply entropy_le_cross_aux _ (q x) (q x).nonneg (q x).total.le
  intro i hi
  obtain ⟨i,rfl,hii⟩ := (send_pos_iff _ _ _).mp hi
  obtain ⟨rfl,H⟩ := (after_mem hx).mp hii
  exact hq i H

lemma Hcond_pair_comm (P : Law α) (X : α → β) (Y : α → γ) (Z : α → η) :
    P.Hcond (fun x => (X x,Y x)) Z = P.Hcond (fun x => (Y x,X x)) Z := by
  unfold Hcond; congr 1; apply P.H_partition; simp [and_comm]

def triple (P : Law α) (k : α → Law β) (v : α × β → Law γ) :=
    (P.withNext k).withNext v

/-- Increment cost when jointly revealing two signals; the second may depend on x and first. -/
theorem refine_signal (P : Law α) (k : α → Law β) (v : α × β → Law γ)
    (q : β → Law γ) (hq : ∀ x i, 0 < q x i) :
    let R := triple P k v
    P.privateH k - R.Hcond (fun i => i.1.1) (fun i => (i.2,i.1.2)) ≤
      (P.withNext k).Ex (fun x => (v x).kl (q x.2)) := by
  intro R
  let X := fun i : (α × β) × γ => i.1.1
  let B := fun i : (α × β) × γ => i.1.2
  let C : (α × β) × γ → γ := Prod.snd
  have he : P.privateH k = R.Hcond X B := by
    have HH := R.Hcond_send Prod.fst Prod.fst Prod.snd
    rw [show R.send Prod.fst=P.withNext k from send_fst_withNext _ _] at HH
    exact HH
  have hi := Hcond_compare R C B q (fun x _ => hq _ _)
  have hx : (P.withNext k).Ex (fun x => (v x).crossE (q x.2)) = R.Ex (fun i => -log (q (B i) (C i))) := by
    unfold crossE R triple; rw [Ex_withNext _ v]
  have hv1 : R.Hcond C (fun x => (X x,B x)) = R.Hcond Prod.snd Prod.fst := by
    refine Hcond_right_partition _ _ ?_
    intro a b; unfold X B; simp
  have hv2 : R.Hcond C (fun x => (X x,B x)) = (P.withNext k).Ex fun x => (v x).entropy :=
    hv1.trans (signal_cost _ _)
  change P.privateH k - R.Hcond X (fun x => (C x,B x)) ≤ _
  simp_rw [he,kl,Ex_sub,hx,← hv2]
  have h1 := Hcond_chain R X C B
  have h2 := Hcond_chain R C X B
  rw [Hcond_pair_comm] at h2
  linarith


/-- When retaining the new signal only, the cost increment is smaller. -/
theorem replace_signal (P : Law α) (k : α → Law β) (v : α → Law γ)
    (q : β → Law γ) (hq : ∀ x i, 0 < q x i) :
    P.privateH k - P.privateH v ≤
      (P.withNext k).Ex (fun x => (v x.1).kl (q x.2)) := by
  have H := refine_signal P k (fun x => v x.1) q hq
  let R := triple P k (fun x => v x.1)
  have hi : R.send (fun x => (x.1.1,x.2))=P.withNext v := by
    apply ext_of_Ex; intro f
    unfold R triple; rw [Ex_send]; simp only [Ex_withNext]; simp only [Ex_const]
  have HH : P.privateH v=R.Hcond (fun x => x.1.1) (fun x => x.2) := by
    unfold privateH
    rw [← hi,Hcond_send]
  have hu : R.Hcond (fun x => x.1.1) (fun x => (x.2,x.1.2)) ≤ P.privateH v := by
    rw [HH]
    apply Hcond_antitone
    intro a b h; exact (Prod.mk.inj h).1
  calc
    _ ≤ P.privateH k - R.Hcond (fun x => x.1.1) (fun x => (x.2,x.1.2)) :=
      sub_le_sub_left hu _
    _ ≤ _ := H

/-- Restriction on a deterministic bit or observation w/o revealing labels -/
lemma after_channel (P : Law α) (f : α → β) (k : α → Law γ)
    {b : β} (h : 0 < P.send f b) :
    (P.withNext k).after (fun x => f x.1) b = (P.after f b).withNext k := by
  have H : (P.withNext k).send (fun x => f x.1) = P.send f := by
    exact Eq.symm (by
      conv_lhs => rw [← send_fst_withNext P k]
      rw [send_send])
  apply Law.ext; rintro ⟨x,i⟩
  apply mul_left_cancel₀ h.ne'
  nth_rw 1 [← H]
  rw [send_mul_after,withNext_apply,withNext_apply,← mul_assoc,send_mul_after]
  simp only [ite_mul,zero_mul]

lemma det_channel (P : Law α) (f : α → β) (k : α → Law γ) :
    let R := P.withNext k
    let W : α × γ → β := fun i => f i.1
    (P.send f).Ex (fun i => (P.after f i).privateH k) + R.Hcond W Prod.snd =
      P.privateH k := by
  intro R W
  have HH : (P.withNext k).send (fun x => f x.1) = P.send f := by
    exact Eq.symm (by conv_lhs => rw [← send_fst_withNext P k,send_send])
  have he : (P.send f).Ex (fun i => (P.after f i).privateH k) =
      R.Hcond Prod.fst (fun i => (W i,i.2)) := by
    rw [Hcond_right_partition (Z:=fun i => (i.2,W i)) R Prod.fst (by simp [and_comm]),Hcond_after_cond]
    rw [show R.send W=_ from HH]
    apply Ex_congr_mem
    intro i hi
    change _ = ((P.withNext k).after _ _).Hcond _ _
    rw [after_channel P f k hi]
    rfl
  rw [he,← Hcond_chain]
  unfold privateH Hcond
  congr 1
  apply H_partition
  simp [W]

end FourierLLogL.Law

end OAI
