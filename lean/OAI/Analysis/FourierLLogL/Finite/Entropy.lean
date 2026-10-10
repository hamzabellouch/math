import OAI.Analysis.FourierLLogL.Finite.Law
/-! # Finite conditional entropy -/
open Function Set Filter
open scoped BigOperators
noncomputable section

namespace OAI

namespace FourierLLogL.Law
universe u v w w'
variable {α : Type u} {β : Type v} {γ : Type w} {η : Type w'}
  [Fintype α] [Fintype β] [Fintype γ] [Fintype η]

open Real

/-- cross entropy (only meaningful for comparison positive on support). -/
def crossE (P : Law α) (q : α → ℝ) : ℝ := P.Ex fun x => -log (q x)

def entropy (P : Law α) : ℝ := crossE P P

lemma entropy_formula (P : Law α) : P.entropy = ∑ x, negMulLog (P x) := by
  simp only [entropy,crossE,Ex,negMulLog,mul_neg,neg_mul]

lemma entropy_nonneg (P : Law α) : 0 ≤ P.entropy := by
  rw [entropy_formula]
  exact Finset.sum_nonneg fun x _ => negMulLog_nonneg (P.nonneg _) (P.le_one _)

/-- Positivity on support condition. -/
def dominated (P Q : Law α) : Prop := ∀ x, 0 < P x → 0 < Q x

lemma dominated_refl (P : Law α) : P.dominated P := fun _ h => h

lemma dominated_send {P Q : Law α} (h : P.dominated Q) (X : α → β) :
    (P.send X).dominated (Q.send X) := by
  intro x hx
  obtain ⟨y,rfl,hy⟩ := (send_pos_iff P X x).mp hx
  exact Q.send_pos X (h y hy)

def kl (P Q : Law α) : ℝ := P.crossE Q - P.entropy

lemma entropy_le_cross_aux (P : Law α) (q : α → ℝ)
    (h0 : ∀ x, 0 ≤ q x) (ht : ∑ x, q x ≤ 1) (h : ∀ x, 0 < P x → 0 < q x) :
    P.entropy ≤ P.crossE q := by
  have H (x : α) :
      P x * (-log (P x)) - P x * (-log (q x)) ≤ q x - P x := by
    obtain heq|hp := eq_or_lt_of_le (P.nonneg x)
    · simpa [← heq] using h0 x
    have he := Real.log_le_sub_one_of_pos (div_pos (h x hp) hp)
    rw [log_div (h x hp).ne' hp.ne'] at he
    have HH := mul_le_mul_of_nonneg_right he hp.le
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hp.ne'] at HH
    linarith
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => H x)
  simp_rw [Finset.sum_sub_distrib, P.total] at HH
  unfold entropy crossE Ex; linarith

lemma kl_nonneg {P Q : Law α} (h : P.dominated Q) : 0 ≤ P.kl Q :=
  sub_nonneg.mpr (entropy_le_cross_aux P Q Q.nonneg Q.total.le h)

lemma entropy_uniform [Nonempty α] :
    (uniform α).entropy = log (Fintype.card α : ℝ) := by
  unfold entropy crossE
  simp_rw [uniform_apply, log_inv, neg_neg, Ex_const]

lemma entropy_le_log_card (P : Law α) :
    P.entropy ≤ log (Fintype.card α : ℝ) := by
  obtain ⟨x,_⟩ := P.mem_nonempty
  have : Nonempty α := ⟨x⟩
  have h : P.dominated (uniform α) := by intro x _; rw [uniform_apply]; positivity
  have hi := kl_nonneg h
  unfold kl crossE at hi
  simp_rw [uniform_apply, log_inv, neg_neg, Ex_const] at hi
  exact sub_nonneg.mp hi

lemma entropy_point (x : α) : (point x).entropy = 0 := by
  classical
  simp only [entropy, crossE, Ex_point, point_apply, ite_true, log_one, neg_zero]

/-- Shannon entropy of an observable on the finite law P. -/
def H (P : Law α) (X : α → β) : ℝ := (P.send X).entropy

/-- Conditional entropy H(X|W). -/
def Hcond (P : Law α) (X : α → β) (W : α → γ) : ℝ :=
  P.H (fun x => (X x, W x)) - P.H W

lemma H_self (P : Law α) : P.H (fun x => x) = P.entropy := by rw [H,send_id]

lemma H_nonneg (P : Law α) (X : α → β) : 0 ≤ P.H X := entropy_nonneg _

lemma H_card (P : Law α) (X : α → β) : P.H X ≤ log (Fintype.card β : ℝ) :=
  entropy_le_log_card _

lemma H_log (P : Law α) (X : α → β) :
    P.H X = P.Ex (fun x => -log (P.send X (X x))) := by rw [H,entropy,crossE,Ex_send]

lemma H_congr_mem (P : Law α) {X Y : α → β} (h : ∀ x, 0 < P x → X x = Y x) :
    P.H X = P.H Y := congrArg entropy (P.send_congr_mem h)

lemma H_send (P : Law α) (X : α → β) (Y : β → γ) :
    (P.send X).H Y = P.H (fun x => Y (X x)) := by rw [H, H, send_send]

/-- If two observables induce the same partition, their entropies coincide. -/
lemma H_partition (P : Law α) {X : α → β} {Y : α → γ}
    (h : ∀ x y, X x = X y ↔ Y x = Y y) : P.H X = P.H Y := by
  have hh (x : α) : P.send X (X x) = P.send Y (Y x) := by
    rw [send_apply, send_apply]
    congr 1
    ext y; exact h _ _
  simp_rw [H_log, hh]

lemma H_pair_rev (P : Law α) (X : α → β) (W : α → γ) :
    P.H (fun a => (X a, W a)) = P.H (fun a => (W a, X a)) :=
  P.H_partition (fun x y => by simp [and_comm])

lemma H_constant (P : Law α) (b : β) : P.H (fun _ => b) = 0 := by
  have h : P.send (fun _ => b) = point b := by
    apply ext_of_Ex; intro f
    rw [Ex_send, Ex_point, Ex_const]
  rw [H,h,entropy_point]

lemma Hcond_constant (P : Law α) (X : α → β) (b : γ) :
    P.Hcond X (fun _ => b) = P.H X := by
  rw [Hcond,H_constant,sub_zero]
  exact P.H_partition (fun x y => by simp)

lemma Hcond_send (P : Law α) (X : α → β) (Y : β → γ) (W : β → η) :
    (P.send X).Hcond Y W = P.Hcond (fun x => Y (X x)) (fun x => W (X x)) := by
  unfold Hcond; rw [H_send, H_send]

lemma H_pair_chain (P : Law α) (X : α → β) (W : α → γ) :
    P.H (fun x => (X x,W x)) = P.H W + P.Hcond X W := by unfold Hcond; ring

lemma Hcond_log (P : Law α) (X : α → β) (W : α → γ) :
    P.Hcond X W = P.Ex (fun x => -log ((P.after W (W x)).send X (X x))) := by
  unfold Hcond
  simp_rw [H_log, ← Ex_sub]
  apply Ex_congr_mem
  intro x hx
  have h1 := send_pos P W hx
  have h2 := send_pos _ X (P.after_self_pos W hx)
  rw [joint_after, log_mul h1.ne' h2.ne']
  ring

lemma Hcond_after (P : Law α) (X : α → β) (W : α → γ) :
    P.Hcond X W = (P.send W).Ex fun w => (P.after W w).H X := by
  rw [Hcond_log]
  simp_rw [H_log]
  exact (P.after_Ex_sum W (fun w x => -log ((P.after W w).send X (X x)))).symm

lemma Hcond_nonneg (P : Law α) (X : α → β) (W : α → γ) :
    0 ≤ P.Hcond X W := by
  rw [Hcond_after]
  exact Ex_nonneg _ fun w => H_nonneg _ _

lemma Hcond_determined (P : Law α) {X : α → β} {W : α → γ}
    (h : ∀ x y, W x = W y → X x = X y) : P.Hcond X W = 0 :=
  sub_eq_zero.mpr (P.H_partition fun x y => by simp; exact fun hh => h x y hh)

lemma H_le_of_determined (P : Law α) {X : α → β} {W : α → γ}
    (h : ∀ x y, W x = W y → X x = X y) : P.H X ≤ P.H W := by
  have h1 := P.Hcond_nonneg W X
  have h2 := P.Hcond_determined h
  rw [Hcond,P.H_pair_rev] at h1; rw [Hcond] at h2; linarith

lemma Hcond_le_H (P : Law α) (X : α → β) (W : α → γ) :
    P.Hcond X W ≤ P.H X := by
  have H1 : P.H X = (P.send W).Ex fun w => ((P.after W w).send X).crossE (P.send X) := by
    rw [H_log]
    simp_rw [crossE,Ex_send]
    have hh := (P.after_Ex_sum W (fun _ x => -log ((P.send X) (X x)))).symm
    rwa [Ex_send] at hh

  rw [H1,Hcond_after]
  refine Ex_mono_mem _ ?_
  intro w hw
  apply entropy_le_cross_aux
  · exact (send P X).nonneg
  · exact (send P X).total.le
  intro x hx
  obtain ⟨a,rfl,ha⟩ := (send_pos_iff _ _ _).mp hx
  exact send_pos _ _ ((after_mem hw).mp ha).2

lemma H_associate (P : Law α) (X : α → β) (Y : α → γ) (Z : α → η) :
    P.H (fun x => ((X x,Y x),Z x)) = P.H (fun x => (X x,(Y x,Z x))) :=
  P.H_partition (fun x y => by simp [and_assoc])

lemma Hcond_chain (P : Law α) (X : α → β) (Y : α → γ) (Z : α → η) :
    P.Hcond (fun x => (X x,Y x)) Z =
      P.Hcond X (fun x => (Y x,Z x)) + P.Hcond Y Z := by
  unfold Hcond
  rw [H_associate]; ring

lemma Hcond_after_cond (P : Law α) (X : α → β) (Y : α → γ) (Z : α → η) :
    P.Hcond X (fun x => (Y x,Z x)) = (P.send Z).Ex fun z => (P.after Z z).Hcond X Y := by
  have h := P.Hcond_chain X Y Z
  have h2 :
      (P.send Z).Ex (fun z => (P.after Z z).Hcond X Y) =
        P.Hcond (fun x => (X x,Y x)) Z - P.Hcond Y Z := by
    rw [Hcond_after, Hcond_after, ← Ex_sub]
    rfl
  linarith

/-- Conditioning reduces entropy. -/
lemma Hcond_refine (P : Law α) (X : α → β) (Y : α → γ) (Z : α → η) :
    P.Hcond X (fun x => (Y x,Z x)) ≤ P.Hcond X Z := by
  rw [Hcond_after_cond, Hcond_after]
  exact Ex_mono _ fun _ => Hcond_le_H _ _ _

lemma Hcond_right_partition (P : Law α) (X : α → β) {Y : α → γ} {Z : α → η}
    (h : ∀ a b, Y a = Y b ↔ Z a = Z b) : P.Hcond X Y = P.Hcond X Z := by
  unfold Hcond
  rw [H_partition _ h]
  congr 1
  apply P.H_partition
  intro a b; simp [h]

lemma Hcond_antitone (P : Law α) (X : α → β) {Y : α → γ} {Z : α → η}
    (h : ∀ a b, Y a = Y b → Z a = Z b) : P.Hcond X Y ≤ P.Hcond X Z := by
  rw [Hcond_right_partition (Z:=fun x => (Y x,Z x)) P X (fun a b => by simp; exact h a b)]
  exact Hcond_refine P X _ _

lemma Hcond_subadd (P : Law α) (X : α → β) (Y : α → γ) (Z : α → η) :
    P.Hcond (fun x => (X x,Y x)) Z ≤ P.Hcond X Z + P.Hcond Y Z := by
  rw [Hcond_chain]
  gcongr
  exact Hcond_refine P _ _ _


lemma entropy_withNext (P : Law α) (k : α → Law β) :
    (P.withNext k).entropy = P.entropy + P.Ex (fun x => (k x).entropy) := by
  simp only [entropy_formula, Ex, Fintype.sum_prod_type, withNext_apply]
  simp_rw [negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Law.total, one_mul]

lemma entropy_tensorP (P : Law α) (Q : Law β) :
    (P.tensorP Q).entropy = P.entropy + Q.entropy := by
  rw [tensorP, entropy_withNext, Ex_const]

lemma H_tensorP (P : Law α) (Q : Law β) (X : α → γ) (Y : β → η) :
    (P.tensorP Q).H (fun x => (X x.1,Y x.2)) = P.H X + Q.H Y := by
  unfold H; rw [send_tensorP, entropy_tensorP]

end FourierLLogL.Law

end OAI
