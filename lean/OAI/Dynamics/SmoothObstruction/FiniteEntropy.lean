import Mathlib

namespace OAI

section

open Finset

namespace SmoothObstruction

/-- Shannon entropy in bits; the value at mass zero is zero. -/
noncomputable def entropyTerm (p : ℝ) : ℝ := -(p * Real.log p) / Real.log 2

namespace FiniteEntropy

variable {α β γ : Type*}

noncomputable def natEntropy [Fintype α] (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)
noncomputable def bits [Fintype α] (p : α → ℝ) : ℝ := ∑ a, entropyTerm (p a)

lemma bits_eq [Fintype α] (p : α → ℝ) : bits p = natEntropy p / Real.log 2 := by
  unfold bits natEntropy entropyTerm
  rw [sum_div]
  simp only [Real.negMulLog_def, neg_mul]

/-- The pointwise log-sum bound, including the zero convention. -/
lemma negMulLog_le_cross {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ -p * Real.log q + q - p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · subst p
    simp only [Real.negMulLog_zero, neg_zero, zero_mul, zero_add, sub_zero]
    exact hq.le
  · have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hp.le
    simp only [mul_sub, mul_one, mul_div_cancel₀ _ hp.ne'] at h'
    simp only [Real.negMulLog_def]
    nlinarith

/-- Entropy of a nonnegative vector of total mass `θ` on a finite set. -/
lemma sum_negMulLog_le_mass (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤
      Real.negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log s.card := by
  classical
  let θ := ∑ i ∈ s, p i
  have hθ : 0 ≤ θ := sum_nonneg hp
  by_cases hzero : θ = 0
  · have hz (i : α) (hi : i ∈ s) : p i = 0 :=
      (sum_eq_zero_iff_of_nonneg hp).mp hzero i hi
    simp [show ∑ i ∈ s, p i = 0 from hzero, sum_congr rfl (fun i hi => congrArg Real.negMulLog (hz i hi))]
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hs : s.Nonempty := by
      by_contra h
      have hempty := not_nonempty_iff_eq_empty.mp h
      simp [θ, hempty] at hzero
    have hc : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
    have hq : 0 < θ / s.card := div_pos hθpos hc
    calc
      _ ≤ ∑ i ∈ s, (-p i * Real.log (θ / s.card) + θ / s.card - p i) :=
        sum_le_sum (fun i hi => negMulLog_le_cross (hp i hi) hq)
      _ = -θ * Real.log (θ / s.card) := by
        simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
        rw [← sum_mul, sum_neg_distrib]
        change -θ * Real.log (θ / s.card) + s.card * (θ / s.card) - θ = _
        rw [mul_div_cancel₀ _ hc.ne']
        ring
      _ = _ := by
        rw [Real.log_div hθpos.ne' hc.ne']
        simp only [Real.negMulLog_def]
        change -θ * (Real.log θ - Real.log s.card) = -θ * Real.log θ + θ * Real.log s.card
        ring

lemma entropy_nonneg [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) : 0 ≤ natEntropy p := by
  apply sum_nonneg
  intro a _
  apply Real.negMulLog_nonneg (hp a)
  calc
    p a ≤ ∑ a, p a := single_le_sum (fun a _ => hp a) (mem_univ a)
    _ = 1 := hpsum

lemma entropy_le_log_card [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) : natEntropy p ≤ Real.log (Fintype.card α) := by
  simpa [natEntropy, hpsum] using sum_negMulLog_le_mass univ p (fun a _ => hp a)

/-- Concavity of finite entropy, without any independence assumptions. -/
lemma entropy_mixture [Fintype α] [Fintype β] (w : α → ℝ) (p : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) (hp : ∀ a b, 0 ≤ p a b) :
    ∑ a, w a * natEntropy (p a) ≤ natEntropy (fun b => ∑ a, w a * p a b) := by
  simp only [natEntropy, mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
    (t := univ) (w := w) (p := fun a => p a b) (fun a _ => hw a) hsum
    (fun a _ => hp a b)

/-- Exact entropy chain rule for a finite mixture with the component label retained. -/
lemma entropy_joint [Fintype α] [Fintype β] (w : α → ℝ) (p : α → β → ℝ)
    (hsum : ∀ a, ∑ b, p a b = 1) :
    natEntropy (fun ab : α × β => w ab.1 * p ab.1 ab.2) =
      natEntropy w + ∑ a, w a * natEntropy (p a) := by
  simp only [natEntropy, Fintype.sum_prod_type, Real.negMulLog_mul, sum_add_distrib]
  simp_rw [← sum_mul, hsum, one_mul, ← mul_sum]

lemma negMulLog_le_log_two {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Real.negMulLog x ≤ Real.log 2 := by
  have h := entropy_le_log_card (p := fun b : Bool => if b then x else 1 - x)
    (by intro b; cases b <;> simp <;> linarith) (by simp)
  simp only [natEntropy, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    Fintype.card_bool, Nat.cast_ofNat] at h
  have hn := Real.negMulLog_nonneg (sub_nonneg.mpr hx') (by linarith : 1 - x ≤ 1)
  linarith

/-- The high-atom mass of a finite law at threshold exp(-a log L). -/
noncomputable def heavyMass [Fintype α] (a : ℝ) (p : α → ℝ) : ℝ :=
  ∑ i, if Real.exp (-a * Real.log (Fintype.card α)) < p i then p i else 0

lemma heavyMass_nonneg [Fintype α] (a : ℝ) {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) :
    0 ≤ heavyMass a p := by
  apply sum_nonneg
  intro i _
  split_ifs
  · exact hp i
  · exact le_rfl

lemma heavyMass_le_one [Fintype α] (a : ℝ) {p : α → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : heavyMass a p ≤ 1 := by
  calc
    _ ≤ ∑ i, p i := sum_le_sum (by intro i _; split_ifs <;> simp_all)
    _ = 1 := hsum

/-- The source heavy--light entropy estimate, with its literal one-bit cost. -/
theorem entropy_le_heavy [Fintype α] [Nonempty α] {p : α → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (a : ℝ) :
    natEntropy p ≤ Real.log 2 +
      (1 - (1 - a) * heavyMass a p) * Real.log (Fintype.card α) := by
  classical
  let H : Finset α := univ.filter (fun i => Real.exp (-a * Real.log (Fintype.card α)) < p i)
  let L : Finset α := univ \ H
  let θ := heavyMass a p
  have hθ : θ = ∑ i ∈ H, p i := by simp [θ, heavyMass, H, sum_filter]
  have hθ₀ : 0 ≤ θ := heavyMass_nonneg a hp
  have hθ₁ : θ ≤ 1 := heavyMass_le_one a hp hsum
  have hLH : Disjoint L H := sdiff_disjoint
  have hLU : L ∪ H = univ := sdiff_union_of_subset (subset_univ H)
  have hsumL : ∑ i ∈ L, p i = 1 - θ := by
    have h := sum_union hLH (f := p)
    rw [hLU, hsum, ← hθ] at h
    linarith
  have hheavy : ∑ i ∈ H, Real.negMulLog (p i) ≤
      a * θ * Real.log (Fintype.card α) := by
    calc
      _ ≤ ∑ i ∈ H, a * p i * Real.log (Fintype.card α) := by
        apply sum_le_sum
        intro i hi
        have hi' := (mem_filter.mp hi).2
        have hip : 0 < p i := (Real.exp_pos _).trans hi'
        have hlog : -a * Real.log (Fintype.card α) ≤ Real.log (p i) := by
          rw [← Real.log_exp (-a * Real.log (Fintype.card α))]
          exact Real.log_le_log (Real.exp_pos _) hi'.le
        have hh := mul_le_mul_of_nonneg_left hlog (hp i)
        rw [Real.negMulLog_def]
        nlinarith
      _ = _ := by rw [← sum_mul, ← mul_sum, ← hθ]
  have hlight : ∑ i ∈ L, Real.negMulLog (p i) ≤
      Real.log 2 + (1 - θ) * Real.log (Fintype.card α) := by
    have hbase := sum_negMulLog_le_mass L p (fun i _ => hp i)
    rw [hsumL] at hbase
    have hc : Real.log L.card ≤ Real.log (Fintype.card α) := by
      by_cases he : L = ∅
      · simp only [he, card_empty, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›)
      · apply Real.log_le_log (Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr he)))
        exact_mod_cast card_le_card (subset_univ L)
    calc
      _ ≤ _ := hbase
      _ ≤ _ := add_le_add (negMulLog_le_log_two (by linarith) (by linarith))
        (mul_le_mul_of_nonneg_left hc (by linarith))
  have hsplit := sum_union hLH (f := fun i => Real.negMulLog (p i))
  rw [hLU] at hsplit
  have hfinal := add_le_add hlight hheavy
  rw [← hsplit] at hfinal
  dsimp [natEntropy]
  dsimp [θ] at hfinal
  nlinarith

end FiniteEntropy
end SmoothObstruction

namespace SmoothObstruction.FiniteEntropy

open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def leftMass (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a,b)
noncomputable def rightMass (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a,b)

omit [Fintype α] in
lemma leftMass_nonneg {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) :
    0 ≤ leftMass p a := sum_nonneg (fun _ _ => hp _)
omit [Fintype β] in
lemma rightMass_nonneg {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (b : β) :
    0 ≤ rightMass p b := sum_nonneg (fun _ _ => hp _)
omit [Fintype α] in
lemma le_leftMass {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) (b : β) :
    p (a,b) ≤ leftMass p a := single_le_sum (fun _ _ => hp _) (mem_univ b)
omit [Fintype β] in
lemma le_rightMass {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) (b : β) :
    p (a,b) ≤ rightMass p b := single_le_sum (fun a _ => hp (a,b)) (mem_univ a)
lemma sum_leftMass (p : α × β → ℝ) : ∑ a, leftMass p a = ∑ x, p x := by
  simp only [leftMass, Fintype.sum_prod_type]
lemma sum_rightMass (p : α × β → ℝ) : ∑ b, rightMass p b = ∑ x, p x := by
  simp only [rightMass, Fintype.sum_prod_type]
  exact sum_comm

/-- Finite joint entropy subadditivity, including zero marginal masses.
This is the unconditional entropy input for block-rate existence. -/
theorem entropy_subadd {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    natEntropy p ≤ natEntropy (leftMass p) + natEntropy (rightMass p) := by
  have hpoint (a : α) (b : β) : Real.negMulLog (p (a,b)) ≤
      -p (a,b) * Real.log (leftMass p a) - p (a,b) * Real.log (rightMass p b) +
        leftMass p a * rightMass p b - p (a,b) := by
    rcases eq_or_lt_of_le (hp (a,b)) with he | he
    · rw [← he]
      simp only [Real.negMulLog_zero, neg_zero, zero_mul, sub_zero, zero_add]
      exact mul_nonneg (leftMass_nonneg hp a) (rightMass_nonneg hp b)
    · have ha := he.trans_le (le_leftMass hp a b)
      have hb := he.trans_le (le_rightMass hp a b)
      have h := negMulLog_le_cross (hp (a,b)) (mul_pos ha hb)
      rw [Real.log_mul ha.ne' hb.ne'] at h
      nlinarith
  have hA : (∑ a, ∑ b, -p (a,b) * Real.log (leftMass p a)) = natEntropy (leftMass p) := by
    simp only [← sum_mul, sum_neg_distrib, leftMass, natEntropy, Real.negMulLog_def]
  have hB : (∑ a, ∑ b, -p (a,b) * Real.log (rightMass p b)) = natEntropy (rightMass p) := by
    rw [sum_comm]
    simp only [← sum_mul, sum_neg_distrib, rightMass, natEntropy, Real.negMulLog_def]
  have hAB : (∑ a, ∑ b, leftMass p a * rightMass p b) = 1 := by
    simp only [← mul_sum, sum_rightMass, sum_leftMass, hs, mul_one]
  calc
    _ ≤ ∑ a, ∑ b, (-p (a,b) * Real.log (leftMass p a) -
        p (a,b) * Real.log (rightMass p b) + leftMass p a * rightMass p b - p (a,b)) := by
      simp only [natEntropy, Fintype.sum_prod_type]
      exact sum_le_sum (fun a _ => sum_le_sum (fun b _ => hpoint a b))
    _ = _ := by
      simp only [sub_eq_add_neg, neg_mul, sum_add_distrib, sum_neg_distrib] at hA hB ⊢
      have hpSum : (∑ a, ∑ b, p (a,b)) = 1 := by simpa only [Fintype.sum_prod_type] using hs
      rw [hA, hB, hAB, hpSum]
      ring

/-- Pushing a finite entropy vector through a deterministic map cannot
increase entropy. There is no measurability or independence assumption. -/
noncomputable def pushMass (p : α → ℝ) (f : α → β) (b : β) : ℝ := by
  classical
  exact ∑ a, if f a = b then p a else 0

omit [Fintype β] in
lemma pushMass_nonneg {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (f : α → β) (b : β) :
    0 ≤ pushMass p f b := by
  classical
  unfold pushMass
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

lemma sum_pushMass (p : α → ℝ) (f : α → β) : ∑ b, pushMass p f b = ∑ a, p a := by
  classical
  simp only [pushMass]
  rw [sum_comm]
  simp

lemma entropy_push_le {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (f : α → β) :
    natEntropy (pushMass p f) ≤ natEntropy p := by
  classical
  have hupper (a : α) : p a ≤ pushMass p f (f a) := by
    have h := single_le_sum (s := univ) (a := a)
      (f := fun x => if f x = f a then p x else 0)
      (by intro x _; split_ifs; exact hp x; exact le_rfl) (mem_univ a)
    simpa [pushMass] using h
  have hpoint (a : α) : -p a * Real.log (pushMass p f (f a)) ≤ Real.negMulLog (p a) := by
    rcases eq_or_lt_of_le (hp a) with ha | ha
    · rw [← ha]; simp
    · have hm := Real.log_le_log ha (hupper a)
      simpa only [Real.negMulLog_def] using mul_le_mul_of_nonpos_left hm (by linarith : -p a ≤ 0)
  have heq : natEntropy (pushMass p f) = ∑ a, -p a * Real.log (pushMass p f (f a)) := by
    unfold natEntropy
    simp only [Real.negMulLog_def]
    calc
      _ = ∑ b, ∑ a, -(if f a = b then p a else 0) * Real.log (pushMass p f b) := by
        apply sum_congr rfl
        intro b _
        rw [← sum_mul, sum_neg_distrib]
        rfl
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        simp [ite_mul]
  rw [heq]
  exact sum_le_sum (fun a _ => hpoint a)

end SmoothObstruction.FiniteEntropy

namespace SmoothObstruction.FiniteEntropy
open Finset
variable {α : Type*} [Fintype α]

/-- Entropy of a symbol emitted only on an event of total mass δ. The marker
cost is exactly one natural-log bit; zeros are included. -/
lemma entropy_option {p : Option α → ℝ} (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    natEntropy p ≤ Real.log 2 + (∑ a, p (some a)) * Real.log (Fintype.card α) := by
  let δ := ∑ a, p (some a)
  have hδ : 0 ≤ δ := sum_nonneg (fun a _ => hp (some a))
  have htotal : p none + δ = 1 := by simpa only [Fintype.sum_option] using hs
  have hbin := entropy_le_log_card (p := fun b : Bool => if b then δ else p none)
    (by intro b; cases b; exact hp none; exact hδ)
    (by simpa [add_comm] using htotal)
  simp only [natEntropy, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    Fintype.card_bool, Nat.cast_ofNat] at hbin
  have htail := sum_negMulLog_le_mass (univ : Finset α) (fun a => p (some a))
    (fun a _ => hp (some a))
  simp only [card_univ] at htail
  change _ ≤ Real.negMulLog δ + δ * _ at htail
  unfold natEntropy
  rw [Fintype.sum_option]
  nlinarith

end SmoothObstruction.FiniteEntropy

end

section

namespace SmoothObstruction.FiniteEntropy
open Finset
variable {α : Type*} [Fintype α]

lemma entropy_lower_mass {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) :
    Real.negMulLog (∑ a, p a) ≤ natEntropy p := by
  have hh := entropy_push_le hp (fun _ : α => ())
  simpa [natEntropy,pushMass] using hh

lemma entropy_add_le {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) :
    natEntropy (fun a => p a+q a) ≤ natEntropy p+natEntropy q := by
  let joint : Bool × α → ℝ := fun ba => if ba.1 then q ba.2 else p ba.2
  have h := entropy_push_le (p:=joint) (by intro ba; dsimp [joint]; split <;> [exact hq _; exact hp _]) Prod.snd
  have hpush : pushMass joint Prod.snd = fun a => p a+q a := by
    classical
    funext a
    simp [pushMass,joint,Fintype.sum_prod_type,add_comm]
  rw [hpush] at h
  simpa [joint,natEntropy,Fintype.sum_prod_type,Fintype.sum_bool,add_comm] using h

/-- Removing part of a probability law can increase unnormalized entropy
only by the entropy term of the retained mass. -/
lemma entropy_common_le {p m : α → ℝ} (_hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a=1)
    (hm : ∀ a, 0 ≤ m a) (hmle : ∀ a, m a ≤ p a) :
    natEntropy m ≤ natEntropy p + Real.negMulLog (∑ a,m a) := by
  let r := fun a => p a-m a
  have hr : ∀ a, 0 ≤ r a := fun a => sub_nonneg.mpr (hmle a)
  let joint : Bool × α → ℝ := fun ba => if ba.1 then r ba.2 else m ba.2
  have hj : ∀ ba, 0≤joint ba := by intro ba; dsimp [joint]; split <;> [exact hr _; exact hm _]
  have hjs : ∑ ba, joint ba=1 := by
    simp only [joint,Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    simp only [r,sum_sub_distrib,hs]
    ring
  have hh := entropy_subadd hj hjs
  have hrm : rightMass joint = p := by
    funext a
    simp [rightMass,joint,r]
  have hleft : natEntropy (leftMass joint) =
      Real.negMulLog (∑ a,m a)+Real.negMulLog (∑ a,r a) := by
    simp [natEntropy,leftMass,joint,add_comm]
  have hjh : natEntropy joint=natEntropy m+natEntropy r := by
    simp [natEntropy,joint,Fintype.sum_prod_type,add_comm]
  rw [hrm,hleft,hjh] at hh
  have hlo := entropy_lower_mass hr
  linarith

/-- Shannon's continuity estimate from a literal total-variation distance.
No coupling or chain-rule inequality is assumed. Natural logs here; division
by log 2 gives precisely the manuscript's one-bit cost. -/
theorem entropy_tv {p q : α → ℝ} (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hps : ∑ a,p a=1) (hqs : ∑ a,q a=1) :
    natEntropy q ≤ natEntropy p+Real.log 2+
      ((1/2:ℝ)*∑ a,|p a-q a|)*Real.log (Fintype.card α) := by
  let m := fun a => min (p a) (q a)
  let r := fun a => q a-m a
  have hm : ∀ a,0 ≤ m a := fun a => le_min (hp a) (hq a)
  have hr : ∀ a,0 ≤ r a := fun a => sub_nonneg.mpr (min_le_right _ _)
  have hc := entropy_common_le hp hps hm (fun a => min_le_left _ _)
  have ha := entropy_add_le hm hr
  have hmr : (fun a => m a+r a)=q := by funext a; dsimp [r]; ring
  rw [hmr] at ha
  have hb := sum_negMulLog_le_mass univ r (fun a _ => hr a)
  simp only [card_univ] at hb
  change natEntropy r ≤ Real.negMulLog (∑ a,r a)+(∑ a,r a)*Real.log (Fintype.card α) at hb
  have ht : (∑ a,m a)+(∑ a,r a)=1 := by
    rw [←sum_add_distrib]
    simpa only [hmr] using hqs
  have hbin := entropy_le_log_card (p:=fun b : Bool => if b then ∑ a,m a else ∑ a,r a)
    (by intro b; cases b; exact sum_nonneg (fun a _=>hr a); exact sum_nonneg (fun a _=>hm a))
    (by simpa only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte] using ht)
  simp only [natEntropy,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,Fintype.card_bool,Nat.cast_ofNat] at hbin
  have hδ : (∑ a,r a)=((1/2:ℝ)*∑ a,|p a-q a|) := by
    have hpoint (a : α) : |p a-q a| = p a+q a-2*m a := by
      dsimp [m]
      rcases le_total (p a) (q a) with h|h
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    simp_rw [hpoint]
    simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,hps,hqs]
    simp only [r,sum_sub_distrib,hqs]
    ring
  rw [hδ] at hb
  rw [hδ] at hbin
  linarith
end SmoothObstruction.FiniteEntropy

end

end OAI
