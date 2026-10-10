import OAI.Combinatorics.PlanarL1.Probability

namespace OAI

section

namespace PlanarL1

/-- Finite adaptive execution trees. Every node makes an actual uniform finite
choice; its continuation, including the number of later choices, may depend on
that choice. This is the finite probability law used by the manuscript. -/
inductive Execution (α : Type*) where
  | pure : α → Execution α
  | choose (n : ℕ) : (Fin (n+1) → Execution α) → Execution α

namespace Execution
attribute [local instance] Classical.propDecidable
variable {α β : Type*}

noncomputable def mean : Execution α → (α → ℝ) → ℝ
  | .pure x, f => f x
  | .choose n E, f => (∑ i, mean (E i) f)/(n+1)

noncomputable def prob (E : Execution α) (P : α → Prop) : ℝ := by
  classical
  exact E.mean (fun x => if P x then 1 else 0)

def bind : Execution α → (α → Execution β) → Execution β
  | .pure x, f => f x
  | .choose n E, f => .choose n (fun i => bind (E i) f)

lemma mean_const (E : Execution α) (c : ℝ) : E.mean (fun _ => c) = c := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp [mean,ih]; field_simp

lemma mean_add (E : Execution α) (f g : α → ℝ) :
    E.mean (fun x => f x+g x)=E.mean f+E.mean g := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp only [mean,ih,Finset.sum_add_distrib,add_div]

lemma mean_smul (E : Execution α) (c : ℝ) (f : α → ℝ) :
    E.mean (fun x => c*f x)=c*E.mean f := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp only [mean,ih,← Finset.mul_sum]; ring

lemma mean_mono (E : Execution α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    E.mean f ≤ E.mean g := by
  induction E with
  | pure x => exact h x
  | choose n E ih => exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => ih i)) (by positivity)

lemma mean_nonneg (E : Execution α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ E.mean f := by
  simpa only [mean_const] using E.mean_mono h

lemma mean_bind (E : Execution α) (F : α → Execution β) (f : β → ℝ) :
    (E.bind F).mean f = E.mean (fun x => (F x).mean f) := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp only [bind,mean,ih]

lemma prob_bind (E : Execution α) (F : α → Execution β) (P : β → Prop) :
    (E.bind F).prob P=E.mean (fun x => (F x).prob P) := E.mean_bind F _

lemma prob_nonneg (E : Execution α) (P : α → Prop) : 0 ≤ E.prob P := by
  classical
  exact E.mean_nonneg (by intro x; split_ifs <;> norm_num)

lemma prob_le_one (E : Execution α) (P : α → Prop) : E.prob P ≤ 1 := by
  classical
  simpa only [prob,mean_const] using E.mean_mono (f := fun x => if P x then 1 else 0)
    (g := fun _ => (1:ℝ)) (by intro x; split_ifs <;> norm_num)

lemma prob_compl (E : Execution α) (P : α → Prop) : E.prob (fun x => ¬P x)=1-E.prob P := by
  classical
  have h : E.prob P+E.prob (fun x => ¬P x)=1 := by
    unfold prob
    rw [← mean_add]
    calc
      _=E.mean (fun _ => 1) := by
        congr 1
        funext x
        by_cases hx : P x <;> simp [hx]
      _=1 := E.mean_const 1
  linarith

lemma prob_mono (E : Execution α) {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    E.prob P ≤ E.prob Q := by
  classical
  apply E.mean_mono
  intro x
  by_cases hp : P x
  · simp [hp,h x hp]
  · simp only [hp, ite_false]; split_ifs <;> norm_num

lemma mean_lower_of_event (E : Execution α) {P : α → Prop} {f : α → ℝ} {c : ℝ}
    (hf : ∀ x, 0 ≤ f x) (h : ∀ x, P x → c ≤ f x) : c*E.prob P ≤ E.mean f := by
  classical
  rw [prob,← mean_smul]
  apply E.mean_mono
  intro x
  by_cases hx : P x <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero]
  · exact h x hx
  · exact hf x

/-- Conditional failure bounds compose even when later grids and cell choices
are chosen using the entire previous history. -/
lemma conditional_loss (E : Execution α) (F : α → Execution β)
    (P : α → Prop) (Q : β → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, P x → (F x).prob (fun y => ¬Q y) ≤ ε) :
    (E.bind F).prob (fun y => ¬Q y) ≤ E.prob (fun x => ¬P x)+ε := by
  classical
  rw [prob_bind]
  calc
    _ ≤ E.mean (fun x => (if ¬P x then 1 else 0)+ε) := by
      apply E.mean_mono
      intro x
      by_cases hx : P x
      · simpa only [hx,not_true_eq_false,ite_false,zero_add] using h x hx
      · simpa only [hx,not_false_eq_true,ite_true] using (F x).prob_le_one (fun y => ¬Q y) |>.trans (le_add_of_nonneg_right hε)
    _ = _ := by
      rw [mean_add,mean_const]
      unfold prob
      congr 2
      funext x
      by_cases hx : P x <;> simp [hx]

lemma conditional_success (E : Execution α) (F : α → Execution β)
    (P : α → Prop) (Q : β → Prop) {p : ℝ}
    (h : ∀ x, P x → p ≤ (F x).prob Q) :
    p*E.prob P ≤ (E.bind F).prob Q := by
  rw [prob_bind]
  exact E.mean_lower_of_event (fun x => (F x).prob_nonneg Q) h

/-- Evolution retains the complete state, which can itself contain the past. -/
def evolve (step : ℕ → α → Execution α) (start : Execution α) : ℕ → Execution α
  | 0 => start
  | k+1 => (evolve step start k).bind (step k)

lemma evolve_loss (step : ℕ → α → Execution α) (start : Execution α)
    (P : ℕ → α → Prop) (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (h : ∀ k x, P k x → (step k x).prob (fun y => ¬P (k+1) y) ≤ ε k) (N : ℕ) :
    (evolve step start N).prob (fun x => ¬P N x) ≤
      start.prob (fun x => ¬P 0 x)+∑ k ∈ Finset.range N, ε k := by
  induction N with
  | zero => simp only [evolve,Finset.range_zero,Finset.sum_empty,add_zero,le_refl]
  | succ N ih =>
    have hh := conditional_loss (evolve step start N) (step N) (P N) (P (N+1)) (hε N) (h N)
    simp only [evolve] at *
    rw [Finset.sum_range_succ]
    linarith

/-- The source's `1/2 · p · br/2` calculation, including adaptive first loss. -/
theorem surviving_success (E : Execution α) (F : α → Execution β)
    (P : α → Prop) (Q : β → Prop) {p c d : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hloss : E.prob (fun x => ¬P x) ≤ 1/2)
    (hs : ∀ x, P x → p ≤ (F x).prob Q)
    (value : β → ℝ) (hv : ∀ y, 0 ≤ value y)
    (hq : ∀ y, Q y → c ≤ value y) (hd : d ≤ c*p/2) :
    d ≤ (E.bind F).mean value := by
  have hgood : 1/2 ≤ E.prob P := by rw [E.prob_compl P] at hloss; linarith
  have hsuc := E.conditional_success F P Q hs
  have hmean := (E.bind F).mean_lower_of_event hv hq
  have hprod := mul_le_mul_of_nonneg_left hgood hp
  have hprod' := mul_le_mul_of_nonneg_left (hprod.trans hsuc) hc
  nlinarith

end Execution
end PlanarL1

namespace PlanarL1.Execution
variable {α β ι : Type*}

noncomputable def uniform [Fintype α] [Nonempty α] : Execution α := by
  classical
  let e : Fin (Fintype.card α-1+1) ≃ α :=
    (finCongr (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance))).trans
      (Fintype.equivFin α).symm
  exact .choose (Fintype.card α-1) (fun i => .pure (e i))

lemma mean_uniform [Fintype α] [Nonempty α] (f : α → ℝ) :
    (uniform (α := α)).mean f=(∑ x, f x)/Fintype.card α := by
  classical
  unfold uniform
  simp only [mean]
  have he : (∑ i : Fin (Fintype.card α-1+1), f (((finCongr
    (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance))).trans
      (Fintype.equivFin α).symm) i))=∑ x, f x := Equiv.sum_comp _ _
  rw [he]
  have h : 0 < Fintype.card α := Fintype.card_pos
  have hc : (↑(Fintype.card α-1):ℝ)+1=Fintype.card α := by
    exact_mod_cast Nat.sub_add_cancel h
  rw [hc]

lemma prob_uniform [Fintype α] [Nonempty α] (P : α → Prop) :
    (uniform (α := α)).prob P=FiniteRandom.prob P := by
  classical
  rw [prob,mean_uniform]
  unfold FiniteRandom.prob
  congr 1
  simp only [Finset.sum_boole,FiniteRandom.event]

lemma mean_sum (E : Execution α) [Fintype ι] (f : ι → α → ℝ) :
    E.mean (fun x => ∑ i, f i x)=∑ i, E.mean (f i) := by
  classical
  induction E with
  | pure x => rfl
  | choose n F ih =>
    simp only [mean,ih]
    rw [Finset.sum_comm,Finset.sum_div]

end PlanarL1.Execution


end

end OAI
