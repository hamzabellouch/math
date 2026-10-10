import OAI.Probability.SATVariance.BystanderStops

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def insertKernel.{u_1} {α : Type u_1} (c : α) (f : List α → ℝ) (l : List α) : ℝ :=
  favg (fun i : Fin (l.length+1) => f (l.insertIdx i c))

def insertAvg.{u_1} {α : Type u_1} : List α → List α → (List α → ℝ) → ℝ
  | [], l, f => f l
  | c::b, l, f => insertAvg b l (insertKernel c f)

inductive Inserts.{u_1} {α : Type u_1} : List α → List α → List α → Prop
  | nil (l : List α) : Inserts [] l l
  | cons (c : α) {b l r : List α} (h : Inserts b l r) (i : ℕ) (hi : i ≤ r.length) :
      Inserts (c::b) l (r.insertIdx i c)

lemma inserts_length.{u_1} {α : Type u_1} {b l r : List α} (h : Inserts b l r) :
    r.length = b.length+l.length := by
  induction h with
  | nil => simp
  | cons c h i hi ih => rw [List.length_insertIdx_of_le_length hi, ih, List.length_cons]; omega

lemma inserts_perm.{u_1} {α : Type u_1} {b l r : List α} (h : Inserts b l r) : r.Perm (b++l) := by
  induction h with
  | nil => simp
  | cons c h i hi ih => exact (List.perm_insertIdx c _ hi).trans (ih.cons c)

lemma insertAvg_congr.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r = g r) : insertAvg b l f = insertAvg b l g := by
  induction b generalizing f g with
  | nil => exact h l (Inserts.nil l)
  | cons c b ih =>
    apply ih
    intro r hr
    unfold insertKernel
    congr 1
    funext i
    exact h _ (Inserts.cons c hr i (by omega))

lemma insertAvg_mono.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r ≤ g r) : insertAvg b l f ≤ insertAvg b l g := by
  induction b generalizing f g with
  | nil => exact h l (Inserts.nil l)
  | cons c b ih =>
    apply ih
    intro r hr
    exact favg_mono (fun i => h _ (Inserts.cons c hr i (by omega)))

lemma insertAvg_const.{u_1} {α : Type u_1} (b l : List α) (a : ℝ) :
    insertAvg b l (fun _ => a) = a := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun _ : Fin (r.length+1) => a)) = a
    simp only [favg_const,ih]

lemma insertAvg_nonneg.{u_1} {α : Type u_1} (b l : List α) {f : List α → ℝ}
    (h : ∀ r, Inserts b l r → 0 ≤ f r) : 0 ≤ insertAvg b l f := by
  rw [← insertAvg_const b l 0]
  exact insertAvg_mono b l h

lemma insertAvg_add.{u_1} {α : Type u_1} (b l : List α) (f g : List α → ℝ) :
    insertAvg b l (fun r => f r+g r) = insertAvg b l f+insertAvg b l g := by
  induction b generalizing f g with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun i : Fin (r.length+1) =>
      f (r.insertIdx i c)+g (r.insertIdx i c))) = _
    simp only [favg_add]
    exact ih _ _

lemma insertAvg_sub.{u_1} {α : Type u_1} (b l : List α) (f g : List α → ℝ) :
    insertAvg b l (fun r => f r-g r) = insertAvg b l f-insertAvg b l g := by
  induction b generalizing f g with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun i : Fin (r.length+1) =>
      f (r.insertIdx i c)-g (r.insertIdx i c))) = _
    simp only [favg_sub]
    exact ih _ _

lemma insertAvg_mul.{u_1} {α : Type u_1} (b l : List α) (a : ℝ) (f : List α → ℝ) :
    insertAvg b l (fun r => a*f r) = a*insertAvg b l f := by
  induction b generalizing f with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun i : Fin (r.length+1) => a*f (r.insertIdx i c))) = _
    simp only [favg_mul]
    exact ih _

lemma insertAvg_sq_le.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) :
    (insertAvg b l f)^2 ≤ insertAvg b l (fun r => (f r)^2) := by
  induction b generalizing f with
  | nil => exact le_refl _
  | cons c b ih =>
    apply (ih (insertKernel c f)).trans
    apply insertAvg_mono
    intro r _
    exact favg_sq_le _

lemma shuffleAvg_cons_kernel.{u_1} {α : Type u_1} (l : List α) (c : α) (f : List α → ℝ) :
    shuffleAvg (c::l) f = shuffleAvg l (insertKernel c f) := by
  rw [shuffleAvg_cons]
  apply shuffleAvg_congr
  intro r hr
  unfold insertKernel
  exact favg_equiv (finCongr (congrArg (fun x => x+1) hr.length_eq).symm)
    (fun i : Fin (r.length+1) => f (r.insertIdx i c))

lemma shuffleAvg_append.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) :
    shuffleAvg (b++l) f = shuffleAvg l (fun r => insertAvg b r f) := by
  induction b generalizing f with
  | nil => rfl
  | cons c b ih =>
    rw [List.cons_append, shuffleAvg_cons_kernel, ih]
    rfl

def insertVar.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) : ℝ :=
  insertAvg b l (fun r => (f r)^2) - (insertAvg b l f)^2

lemma insertVar_nonneg.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) : 0 ≤ insertVar b l f :=
  sub_nonneg.mpr (insertAvg_sq_le b l f)

lemma insertVar_congr.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r = g r) : insertVar b l f = insertVar b l g := by
  unfold insertVar
  rw [insertAvg_congr b l h,insertAvg_congr b l (fun r hr => congrArg (fun x : ℝ => x^2) (h r hr))]

lemma insertVar_mul.{u_1} {α : Type u_1} (b l : List α) (a : ℝ) (f : List α → ℝ) :
    insertVar b l (fun r => a*f r) = a^2*insertVar b l f := by
  have he : (fun r => (a*f r)^2) = (fun r => a^2*(f r)^2) := by funext r; ring
  simp only [insertVar,he,insertAvg_mul]
  ring

lemma insertVar_cons.{u_1} {α : Type u_1} (b l : List α) (c : α) (f : List α → ℝ) :
    insertVar (c::b) l f = insertVar b l (insertKernel c f) +
      insertAvg b l (fun r => fvariance (fun i : Fin (r.length+1) => f (r.insertIdx i c))) := by
  change insertAvg b l (insertKernel c (fun r => (f r)^2)) -
    (insertAvg b l (insertKernel c f))^2 =
    (insertAvg b l (fun r => (insertKernel c f r)^2) -
      (insertAvg b l (insertKernel c f))^2) +
    insertAvg b l (fun r => insertKernel c (fun r => (f r)^2) r -
      (insertKernel c f r)^2)
  rw [insertAvg_sub]
  ring

def Private {n k : ℕ} (c : Clause n k) (l : List (Clause n k)) : Prop :=
  ∃ v : c.1.1, ∀ d ∈ l, v.val ∉ d.1.1

def Bystanders {n k : ℕ} : List (Clause n k) → List (Clause n k) → Prop
  | [], _ => True
  | c::b, l => Private c (b++l) ∧ Bystanders b l

lemma private_perm {n k : ℕ} {c : Clause n k} {l r : List (Clause n k)}
    (h : l.Perm r) (hc : Private c l) : Private c r := by
  obtain ⟨v,hv⟩ := hc
  exact ⟨v,fun d hd => hv d (h.mem_iff.mpr hd)⟩

lemma private_harmless {n k : ℕ} {c : Clause n k} {l : List (Clause n k)}
    (hc : Private c l) : Harmless c l := by
  obtain ⟨v,hv⟩ := hc
  exact harmless_private c l v hv

lemma inserts_stop_bounds {n k : ℕ} {b l r : List (Clause n k)} (hb : Bystanders b l)
    (h : Inserts b l r) : listStop l ≤ listStop r ∧ listStop r ≤ listStop l+b.length := by
  induction h with
  | nil => simp
  | @cons c b l r h i hi ih =>
    have hh : Harmless c r := private_harmless (private_perm (inserts_perm h).symm hb.1)
    rw [listStop_insert c r hh i hi]
    have ht := ih hb.2
    simp only [List.length_cons]
    split_ifs <;> omega

lemma favg_fin_lt {L t : ℕ} (ht : t ≤ L) :
    favg (fun i : Fin L => if i.val < t then (1:ℝ) else 0) = (t:ℝ)/L := by
  unfold favg
  simp only [Fintype.card_fin]
  congr 1
  have he : {i : Fin L // i.val < t} ≃ Fin t :=
    { toFun := fun i => ⟨i.1.val,i.2⟩
      invFun := fun i => ⟨⟨i.val,i.isLt.trans_le ht⟩,i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Fintype.card_subtype] using congrArg (fun x : ℕ => (x:ℝ)) (Fintype.card_congr he)

lemma insertion_moments {L t : ℕ} (hL : 0 < L) (ht : t ≤ L) :
    favg (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      (1+1/(L:ℝ))*t ∧
    fvariance (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      (t:ℝ)*((L:ℝ)-t)/(L:ℝ)^2 := by
  let : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  let f : Fin L → ℝ := fun i => if i.val < t then 1 else 0
  have hf : favg f = (t:ℝ)/L := favg_fin_lt ht
  have hf2 : (fun i => f i ^ 2) = f := by funext i; simp only [f]; split_ifs <;> norm_num
  have he : (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      fun i => (t:ℝ)+f i := by funext i; simp only [Nat.cast_add,f]; split_ifs <;> norm_num
  have he2 : (fun i => ((t:ℝ)+f i)^2) = fun i => (t:ℝ)^2+(2*t)*f i+f i^2 := by
    funext i; ring
  rw [he]
  constructor
  · rw [favg_add,favg_const,hf]; ring
  · simp only [fvariance, he2, favg_add, favg_const, favg_mul, hf2, hf]
    field_simp
    ring

lemma insertKernel_stop {n k : ℕ} (c : Clause n k) (r : List (Clause n k))
    (hc : Harmless c r) :
    insertKernel c (fun s => (listStop s:ℝ)) r =
      (1+1/((r.length:ℝ)+1))*(listStop r:ℝ) := by
  unfold insertKernel
  have he (i : Fin (r.length+1)) := listStop_insert c r hc i (by omega)
  simp only [he]
  exact_mod_cast (insertion_moments (Nat.succ_pos _) (listStop_le r)).1

lemma insertion_variance_stop {n k : ℕ} (c : Clause n k) (r : List (Clause n k))
    (hc : Harmless c r) :
    fvariance (fun i : Fin (r.length+1) => (listStop (r.insertIdx i c):ℝ)) =
      (listStop r:ℝ)*((r.length:ℝ)+1-listStop r)/((r.length:ℝ)+1)^2 := by
  have he (i : Fin (r.length+1)) := listStop_insert c r hc i (by omega)
  simp only [he]
  exact_mod_cast (insertion_moments (Nat.succ_pos _) (listStop_le r)).2

lemma insertVar_stop_lower {n k : ℕ} {b l : List (Clause n k)} (hb : Bystanders b l)
    {A C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hAt : A ≤ (listStop l:ℝ)) (hCt : C ≤ (l.length:ℝ)+1-listStop l)
    (hlen : (b.length:ℝ)+l.length+1 ≤ D) :
    (b.length:ℝ)*(A*C/D^2) ≤ insertVar b l (fun r => (listStop r:ℝ)) := by
  induction b with
  | nil => simp [insertVar,insertAvg]
  | cons c b ih =>
    have hlen' : (b.length:ℝ)+l.length+1 ≤ D := by
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hlen
      linarith
    have hi := ih hb.2 hlen'
    rw [insertVar_cons]
    let a : ℝ := 1+1/((b.length:ℝ)+l.length+1)
    have ha : 1 ≤ a := by
      dsimp [a]
      have : (0:ℝ) ≤ 1/((b.length:ℝ)+l.length+1) := by positivity
      linarith
    have he : insertVar b l (insertKernel c (fun r => (listStop r:ℝ))) =
        a^2*insertVar b l (fun r => (listStop r:ℝ)) := by
      rw [←insertVar_mul]
      apply insertVar_congr
      intro r hr
      rw [insertKernel_stop c r (private_harmless (private_perm (inserts_perm hr).symm hb.1))]
      have hrlen := inserts_length hr
      simp only [hrlen,Nat.cast_add]
      rfl
    rw [he]
    have hstep : A*C/D^2 ≤ insertAvg b l (fun r =>
        fvariance (fun i : Fin (r.length+1) => (listStop (r.insertIdx i c):ℝ))) := by
      rw [←insertAvg_const b l (A*C/D^2)]
      apply insertAvg_mono
      intro r hr
      rw [insertion_variance_stop c r
        (private_harmless (private_perm (inserts_perm hr).symm hb.1))]
      have ht := inserts_stop_bounds hb.2 hr
      have hrlen := inserts_length hr
      have hr0 : 0 < (r.length:ℝ)+1 := by positivity
      have ht0 : 0 ≤ (listStop r:ℝ) := by positivity
      have hs : 0 ≤ (r.length:ℝ)+1-listStop r := by
        have := listStop_le r
        exact sub_nonneg.mpr (by exact_mod_cast this)
      have hAr : A ≤ (listStop r:ℝ) := hAt.trans (by exact_mod_cast ht.1)
      have hCr : C ≤ (r.length:ℝ)+1-listStop r := by
        have ht' : (listStop r:ℝ) ≤ listStop l+b.length := by exact_mod_cast ht.2
        have hrl : (r.length:ℝ) = b.length+l.length := by exact_mod_cast hrlen
        linarith
      have hrD : (r.length:ℝ)+1 ≤ D := by
        rw [hrlen,Nat.cast_add]
        exact hlen'
      calc
        _ ≤ (listStop r:ℝ)*((r.length:ℝ)+1-listStop r)/D^2 :=
          div_le_div_of_nonneg_right (mul_le_mul hAr hCr hC ht0) (sq_nonneg D)
        _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg ht0 hs)
          (sq_pos_of_pos hr0) (by nlinarith)
    have hv := insertVar_nonneg b l (fun r => (listStop r:ℝ))
    have ha2 : 1 ≤ a^2 := by nlinarith
    have hv' := mul_le_mul_of_nonneg_right ha2 hv
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

end RandomKSAT

end

end OAI
