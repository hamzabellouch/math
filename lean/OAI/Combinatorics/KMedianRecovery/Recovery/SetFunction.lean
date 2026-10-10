import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthPolynomial

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

variable {E : Type*} [Fintype E] [DecidableEq E]

abbrev SetFunction (E : Type*) := Finset E → ℝ

noncomputable def marginal (g : SetFunction E) (e : E) (S : Finset E) : ℝ :=
  g (insert e S) - g S

noncomputable def operator (w : E → ℝ) (g : SetFunction E) (S : Finset E) : ℝ :=
  (1 - ∑ e, w e) * g S + ∑ e, w e * g (insert e S)

def IsWeight (w : E → ℝ) : Prop := (∀ e, 0 ≤ w e) ∧ ∑ e, w e ≤ 1

abbrev Batch (E : Type*) := List ((E → ℝ) × E)

noncomputable def evaluate : Batch E → SetFunction E → SetFunction E
  | [], g => g
  | (w, _) :: tail, g => evaluate tail (operator w g)

noncomputable def direction : Batch E → SetFunction E → SetFunction E
  | [], _ => fun _ => 0
  | (w, e) :: tail, g => fun S => evaluate tail (marginal g e) S + direction tail (operator w g) S

noncomputable def addMass (w : E → ℝ) (e : E) (d : ℝ) : E → ℝ :=
  fun f => w f + if f = e then d else 0

noncomputable def update (d : ℝ) (b : Batch E) : Batch E :=
  b.map (fun p => (addMass p.1 p.2 d, p.2))

def HasRoom (d : ℝ) (b : Batch E) : Prop :=
  ∀ p ∈ b, IsWeight p.1 ∧ ∑ e, p.1 e + d ≤ 1

def BoundedMarginals (g : SetFunction E) (M : ℝ) : Prop :=
  ∀ e S, 0 ≤ marginal g e S ∧ marginal g e S ≤ M

lemma operator_const (w : E → ℝ) (c : ℝ) (S : Finset E) :
    operator w (fun _ => c) S = c := by
  simp only [operator, ← Finset.sum_mul]
  ring

lemma operator_add (w : E → ℝ) (g h : SetFunction E) (S : Finset E) :
    operator w (fun U => g U + h U) S = operator w g S + operator w h S := by
  simp only [operator, mul_add, Finset.sum_add_distrib]
  ring

lemma operator_smul (w : E → ℝ) (c : ℝ) (g : SetFunction E) (S : Finset E) :
    operator w (fun U => c * g U) S = c * operator w g S := by
  have hs : (∑ e, w e * (c * g (insert e S))) = c * ∑ e, w e * g (insert e S) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold operator
  rw [hs]
  ring

lemma operator_sub (w : E → ℝ) (g h : SetFunction E) (S : Finset E) :
    operator w (fun U => g U - h U) S = operator w g S - operator w h S := by
  simp only [operator, mul_sub, Finset.sum_sub_distrib]
  ring

lemma operator_mono (w : E → ℝ) (hw : IsWeight w) (g h : SetFunction E)
    (hgh : ∀ S, g S ≤ h S) (S : Finset E) : operator w g S ≤ operator w h S := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hgh S) (sub_nonneg.mpr hw.2)
  · exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hgh _) (hw.1 e)

lemma operator_bounds (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E) (a b : ℝ)
    (hg : ∀ S, a ≤ g S ∧ g S ≤ b) (S : Finset E) :
    a ≤ operator w g S ∧ operator w g S ≤ b := by
  constructor
  · simpa only [operator_const] using operator_mono w hw (fun _ => a) g (fun U => (hg U).1) S
  · simpa only [operator_const] using operator_mono w hw g (fun _ => b) (fun U => (hg U).2) S

lemma marginal_operator (w : E → ℝ) (g : SetFunction E) (e : E) (S : Finset E) :
    marginal (operator w g) e S = operator w (marginal g e) S := by
  have hs : (∑ f, w f * g (insert f (insert e S))) =
      ∑ f, w f * g (insert e (insert f S)) := by
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.insert_comm e f]
  unfold marginal operator
  rw [hs]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

lemma operator_marginals (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E) (M : ℝ)
    (hg : BoundedMarginals g M) : BoundedMarginals (operator w g) M := by
  intro e S
  rw [marginal_operator]
  exact operator_bounds w hw (marginal g e) 0 M (hg e) S

lemma sum_addMass (w : E → ℝ) (e : E) (d : ℝ) :
    ∑ f, addMass w e d f = (∑ f, w f) + d := by
  simp [addMass, Finset.sum_add_distrib]

lemma addMass_weight (w : E → ℝ) (e : E) {d : ℝ} (hd : 0 ≤ d)
    (hw : IsWeight w) (hr : (∑ f, w f) + d ≤ 1) : IsWeight (addMass w e d) := by
  refine ⟨?_, ?_⟩
  · intro f
    unfold addMass
    split_ifs <;> linarith [hw.1 f]
  · rwa [sum_addMass]

lemma operator_addMass (w : E → ℝ) (e : E) (d : ℝ) (g : SetFunction E) (S : Finset E) :
    operator (addMass w e d) g S = operator w g S + d * marginal g e S := by
  unfold operator
  rw [sum_addMass]
  have hsum : (∑ f, addMass w e d f * g (insert f S)) =
      (∑ f, w f * g (insert f S)) + d * g (insert e S) := by
    simp only [addMass, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp
  rw [hsum]
  unfold marginal
  ring

lemma evaluate_add (b : Batch E) (g h : SetFunction E) (S : Finset E) :
    evaluate b (fun U => g U + h U) S = evaluate b g S + evaluate b h S := by
  induction b generalizing g h with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    simp only [evaluate]
    conv_lhs => arg 2; ext U; rw [operator_add]
    exact ih _ _

lemma evaluate_smul (b : Batch E) (c : ℝ) (g : SetFunction E) (S : Finset E) :
    evaluate b (fun U => c * g U) S = c * evaluate b g S := by
  induction b generalizing g with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    simp only [evaluate]
    conv_lhs => arg 2; ext U; rw [operator_smul]
    exact ih _

lemma evaluate_const (b : Batch E) (c : ℝ) (S : Finset E) :
    evaluate b (fun _ => c) S = c := by
  induction b with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    simp only [evaluate]
    conv_lhs => arg 2; ext U; rw [operator_const]
    exact ih

lemma evaluate_mono (b : Batch E) (hb : ∀ p ∈ b, IsWeight p.1)
    (g h : SetFunction E) (hgh : ∀ S, g S ≤ h S) (S : Finset E) :
    evaluate b g S ≤ evaluate b h S := by
  induction b generalizing g h with
  | nil => exact hgh S
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    exact ih (fun p hp => hb p (List.mem_cons_of_mem _ hp)) _ _
      (operator_mono w (hb _ (List.mem_cons_self)) g h hgh)

lemma evaluate_bounds (b : Batch E) (hb : ∀ p ∈ b, IsWeight p.1)
    (g : SetFunction E) (a z : ℝ) (hg : ∀ S, a ≤ g S ∧ g S ≤ z) (S : Finset E) :
    a ≤ evaluate b g S ∧ evaluate b g S ≤ z := by
  constructor
  · simpa only [evaluate_const] using evaluate_mono b hb (fun _ => a) g (fun U => (hg U).1) S
  · simpa only [evaluate_const] using evaluate_mono b hb g (fun _ => z) (fun U => (hg U).2) S

lemma evaluate_addMass_head (tail : Batch E) (w : E → ℝ) (e : E) (d : ℝ)
    (g : SetFunction E) (S : Finset E) :
    evaluate ((addMass w e d, e) :: tail) g S =
      evaluate tail (operator w g) S + d * evaluate tail (marginal g e) S := by
  simp only [evaluate]
  conv_lhs => arg 2; ext U; rw [operator_addMass]
  rw [evaluate_add, evaluate_smul]

lemma update_weights {d : ℝ} (b : Batch E) (hd : 0 ≤ d) (hr : HasRoom d b) :
    ∀ p ∈ update d b, IsWeight p.1 := by
  intro p hp
  obtain ⟨⟨w,e⟩, hmem, rfl⟩ := List.mem_map.mp hp
  exact addMass_weight w e hd (hr _ hmem).1 (hr _ hmem).2

lemma evaluate_update_lower (b : Batch E) (g : SetFunction E) {M d : ℝ}
    (_hM : 0 ≤ M) (hd : 0 ≤ d) (hr : HasRoom d b)
    (hg : ∀ S, 0 ≤ g S ∧ g S ≤ M) (S : Finset E) :
    evaluate b g S - (b.length : ℝ) * d * M ≤ evaluate (update d b) g S := by
  induction b generalizing g with
  | nil => simp [evaluate, update]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hw := (hr _ List.mem_cons_self).1
    have htail : HasRoom d tail := fun p hp => hr p (List.mem_cons_of_mem _ hp)
    have ihg := ih (operator w g) htail (operator_bounds w hw g 0 M hg)
    have hm : ∀ U, -M ≤ marginal g e U := fun U => by
      unfold marginal
      linarith [(hg (insert e U)).1, (hg U).2]
    have hm' : -M ≤ evaluate (update d tail) (marginal g e) S := by
      simpa only [evaluate_const] using evaluate_mono (update d tail)
        (update_weights tail hd htail) (fun _ => -M) (marginal g e) hm S
    have heq : update d ((w,e)::tail) = (addMass w e d,e)::update d tail := rfl
    rw [heq, evaluate_addMass_head]
    simp only [evaluate, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hmul := mul_le_mul_of_nonneg_left hm' hd
    nlinarith

theorem categorical_update_bound (b : Batch E) (g : SetFunction E) {M d : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hr : HasRoom d b)
    (hg : BoundedMarginals g M) (S : Finset E) :
    evaluate b g S + d * direction b g S - (b.length : ℝ)^2 * d^2 * M ≤
      evaluate (update d b) g S := by
  induction b generalizing g with
  | nil => simp [evaluate, direction, update]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hw := (hr _ List.mem_cons_self).1
    have htail : HasRoom d tail := fun p hp => hr p (List.mem_cons_of_mem _ hp)
    have ihg := ih (operator w g) htail (operator_marginals w hw g M hg)
    have hder := evaluate_update_lower tail (marginal g e) hM hd htail (hg e) S
    have hder' := mul_le_mul_of_nonneg_left hder hd
    have heq : update d ((w,e)::tail) = (addMass w e d,e)::update d tail := rfl
    rw [heq, evaluate_addMass_head]
    simp only [evaluate, direction, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hlen : (0 : ℝ) ≤ tail.length := Nat.cast_nonneg _
    have herr : 0 ≤ ((tail.length : ℝ) + 1) * d^2 * M := by positivity
    nlinarith

def Diminishing (g : SetFunction E) : Prop :=
  ∀ U V, U ⊆ V → ∀ e, marginal g e V ≤ marginal g e U

omit [Fintype E] in
lemma boundedMarginals_of_submodular (g : SetFunction E) (hmono : Monotone g)
    (hsub : Diminishing g) (hg0 : g ∅ = 0) {M : ℝ}
    (hM : ∀ e, g {e} ≤ M) : BoundedMarginals g M := by
  intro e S
  constructor
  · exact sub_nonneg.mpr (hmono (Finset.subset_insert _ _))
  · have hh := hsub ∅ S (Finset.empty_subset _) e
    simp only [marginal, Finset.insert_empty, hg0, sub_zero] at hh
    exact hh.trans (hM e)

noncomputable def allMarginals : Batch E → SetFunction E → SetFunction E
  | [], _ => fun _ => 0
  | (_, e) :: tail, g => fun S => marginal g e S + allMarginals tail g S

def choices : Batch E → Finset E
  | [] => ∅
  | (_, e) :: tail => insert e (choices tail)

omit [Fintype E] in
lemma submodular_telescope (b : Batch E) (g : SetFunction E) (hg : Diminishing g)
    (S : Finset E) : g (S ∪ choices b) - g S ≤ allMarginals b g S := by
  induction b with
  | nil => simp [choices, allMarginals]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hm := hg S (S ∪ choices tail) Finset.subset_union_left e
    simp only [choices, allMarginals, Finset.union_insert]
    unfold marginal at hm ⊢
    linarith

omit [Fintype E] in
lemma comparison_gap (b : Batch E) (g : SetFunction E) (hmono : Monotone g)
    (hsub : Diminishing g) (S : Finset E) :
    g (choices b) - g S ≤ allMarginals b g S := by
  have ht := submodular_telescope b g hsub S
  have hm := hmono (Finset.subset_union_right : choices b ⊆ S ∪ choices b)
  linarith

lemma operator_diminishing (w : E → ℝ) (hw : IsWeight w)
    (g : SetFunction E) (hg : Diminishing g) : Diminishing (operator w g) := by
  intro U V hUV e
  rw [marginal_operator, marginal_operator]
  unfold operator
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hg U V hUV e) (sub_nonneg.mpr hw.2)
  · apply Finset.sum_le_sum
    intro f _
    exact mul_le_mul_of_nonneg_left (hg (insert f U) (insert f V)
      (Finset.insert_subset_insert f hUV) e) (hw.1 f)

lemma operator_le_self (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E)
    (S : Finset E) (hg : ∀ e, g (insert e S) ≤ g S) : operator w g S ≤ g S := by
  calc
    operator w g S ≤ operator w (fun _ => g S) S := by
      unfold operator
      apply add_le_add le_rfl
      exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hg e) (hw.1 e)
    _ = g S := operator_const _ _ _

lemma operator_marginal_le (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E)
    (hg : Diminishing g) (e : E) (S : Finset E) :
    operator w (marginal g e) S ≤ marginal g e S := by
  apply operator_le_self w hw (marginal g e) S
  intro f
  exact hg S (insert f S) (Finset.subset_insert _ _) e

lemma operator_allMarginals (w : E → ℝ) (b : Batch E) (g : SetFunction E) (S : Finset E) :
    operator w (allMarginals b g) S = allMarginals b (operator w g) S := by
  induction b with
  | nil => exact operator_const _ _ _
  | cons p tail ih =>
    rcases p with ⟨v,e⟩
    simp only [allMarginals, operator_add, ← marginal_operator, ih]

lemma direction_dominates (b : Batch E) (g : SetFunction E)
    (hb : ∀ p ∈ b, IsWeight p.1) (hg : Diminishing g) (S : Finset E) :
    evaluate b (allMarginals b g) S ≤ direction b g S := by
  induction b generalizing g with
  | nil => simp [evaluate, direction, allMarginals]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hw := hb _ List.mem_cons_self
    have htail : ∀ p ∈ tail, IsWeight p.1 := fun p hp => hb p (List.mem_cons_of_mem _ hp)
    have ht := ih (operator w g) htail (operator_diminishing w hw g hg)
    have hm := evaluate_mono tail htail (operator w (marginal g e)) (marginal g e)
      (operator_marginal_le w hw g hg e) S
    simp only [evaluate, direction, allMarginals]
    have heq : operator w (fun U => marginal g e U + allMarginals tail g U) =
        fun U => operator w (marginal g e) U + allMarginals tail (operator w g) U := by
      funext U
      rw [operator_add, operator_allMarginals]
    rw [heq, evaluate_add]
    exact add_le_add hm ht

lemma evaluate_sub (b : Batch E) (g h : SetFunction E) (S : Finset E) :
    evaluate b (fun U => g U - h U) S = evaluate b g S - evaluate b h S := by
  have hh : (fun U => g U - h U) = (fun U => g U + (-1) * h U) := by
    funext U
    ring
  rw [hh, evaluate_add, evaluate_smul]
  ring

theorem categorical_comparison_direction (b : Batch E) (g : SetFunction E)
    (hb : ∀ p ∈ b, IsWeight p.1) (hmono : Monotone g) (hsub : Diminishing g)
    (S : Finset E) : g (choices b) - evaluate b g S ≤ direction b g S := by
  have h := evaluate_mono b hb (fun U => g (choices b) - g U) (allMarginals b g)
    (comparison_gap b g hmono hsub) S
  rw [evaluate_sub, evaluate_const] at h
  exact h.trans (direction_dominates b g hb hsub S)

def SameWeights (b c : Batch E) : Prop := List.Forall₂ (fun p q => p.1 = q.1) b c

lemma evaluate_eq_of_sameWeights (b c : Batch E) (h : SameWeights b c)
    (g : SetFunction E) (S : Finset E) : evaluate b g S = evaluate c g S := by
  induction h generalizing g with
  | nil => rfl
  | @cons p q b c hp hbc ih =>
    rcases p with ⟨w,e⟩
    rcases q with ⟨v,f⟩
    dsimp at hp
    subst v
    exact ih _

noncomputable def ChoiceErrors (err : ℝ) : Batch E → Batch E → SetFunction E → Finset E → Prop
  | [], [], _, _ => True
  | (w,e) :: b, (v,f) :: c, g, S => w = v ∧
      evaluate b (marginal g f) S ≤ evaluate b (marginal g e) S + err ∧
      ChoiceErrors err b c (operator w g) S
  | _, _, _, _ => False

lemma choiceErrors_weights {err : ℝ} (b c : Batch E) (g : SetFunction E) (S : Finset E)
    (h : ChoiceErrors err b c g S) : SameWeights b c := by
  induction b generalizing c g with
  | nil => cases c with
    | nil => exact List.Forall₂.nil
    | cons p c => exact h.elim
  | cons p b ih =>
    cases c with
    | nil => exact h.elim
    | cons q c =>
      rcases p with ⟨w,e⟩
      rcases q with ⟨v,f⟩
      exact List.Forall₂.cons h.1 (ih c _ h.2.2)

end Categorical
end MetricKMedianRecovery

end OAI
