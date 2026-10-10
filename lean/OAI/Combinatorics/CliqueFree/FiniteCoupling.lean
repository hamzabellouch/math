import OAI.Combinatorics.CliqueFree.Model

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq J := Classical.decEq J
local instance : DecidableEq E := Classical.decEq E

abbrev Law (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1
noncomputable def dist (p q : I → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

def push (p : I → ℝ) (f : I → J) (y : J) : ℝ := ∑ i, if f i = y then p i else 0

def mix (p : I → ℝ) (q : I → J → ℝ) (y : J) : ℝ := ∑ i, p i * q i y

lemma sum_push (p : I → ℝ) (f : I → J) (g : J → ℝ) :
    ∑ y, push p f y * g y = ∑ i, p i * g (f i) := by
  simp only [push, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul]

lemma law_push {p : I → ℝ} (hp : Law p) (f : I → J) : Law (push p f) := by
  refine ⟨fun y ↦ sum_nonneg fun i _ ↦ by split_ifs <;> simp_all, ?_⟩
  have h := sum_push p f (fun _ ↦ 1)
  simpa [hp.2] using h

lemma sum_mix (p : I → ℝ) (q : I → J → ℝ) (g : J → ℝ) :
    ∑ y, mix p q y * g y = ∑ i, p i * ∑ y, q i y * g y := by
  simp only [mix, sum_mul, mul_sum, mul_assoc]
  exact sum_comm

lemma law_mix {p : I → ℝ} {q : I → J → ℝ} (hp : Law p) (hq : ∀ i, Law (q i)) :
    Law (mix p q) := by
  refine ⟨fun y ↦ sum_nonneg fun i _ ↦ mul_nonneg (hp.1 i) ((hq i).1 y), ?_⟩
  have h := sum_mix p q (fun _ ↦ 1)
  simpa only [mul_one, (hq _).2, hp.2] using h

lemma law_dirac (j : J) : Law (fun y ↦ if y = j then (1 : ℝ) else 0) := by
  constructor
  · intro y; dsimp; split_ifs <;> norm_num
  · simp

lemma prob_event_le_one {p : I → ℝ} (hp : Law p) (b : I → Prop) [DecidablePred b] :
    (∑ i, if b i then p i else 0) ≤ 1 := by
  rw [← hp.2]
  apply sum_le_sum
  intro i _
  split_ifs <;> simp_all

lemma expected_indicator_push {p : I → ℝ} (f : I → J) (b : J → Prop) [DecidablePred b] :
    (∑ y, if b y then push p f y else 0) = ∑ i, if b (f i) then p i else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using sum_push p f (fun y ↦ if b y then 1 else 0)

lemma expected_indicator_mix (p : I → ℝ) (q : I → J → ℝ) (b : J → Prop) [DecidablePred b] :
    (∑ y, if b y then mix p q y else 0) =
      ∑ i, p i * ∑ y, if b y then q i y else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using sum_mix p q (fun y ↦ if b y then 1 else 0)

open MeasureTheory in
lemma exists_threshold_law (a : I → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    ∃ q : Finset I → ℝ, Law q ∧
      (∀ i, (∑ A, if i ∈ A then q A else 0) = a i) ∧
      (∀ i j, (∑ A, if i ∈ A ∧ j ∈ A then q A else 0) = min (a i) (a j)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 1)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, Real.volume_Icc]
  let f : ℝ → Finset I := fun t ↦ univ.filter (fun i ↦ t ≤ a i)
  have hf : ∀ A, MeasurableSet (f ⁻¹' {A}) := by
    intro A
    have heq : f ⁻¹' {A} = ⋂ i, {t : ℝ | (t ≤ a i ↔ i ∈ A)} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.ext_iff,
        f, mem_filter, mem_univ, true_and, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ A
    · simpa only [hi, iff_true, Set.Iic] using (measurableSet_Iic : MeasurableSet (Set.Iic (a i)))
    · simpa only [hi, iff_false, not_le, Set.Ioi] using (measurableSet_Ioi : MeasurableSet (Set.Ioi (a i)))
  let q : Finset I → ℝ := fun A ↦ μ.real (f ⁻¹' {A})
  have hevent (b : Finset I → Prop) [DecidablePred b] :
      (∑ A, if b A then q A else 0) = μ.real {t | b (f t)} := by
    rw [← sum_filter]
    have h := sum_measureReal_preimage_singleton (μ := μ) (univ.filter b) (fun A _ ↦ hf A)
    convert h using 1; simp
  have hmass (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
      μ.real {t | t ≤ c} = c := by
    change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic c) = c
    rw [measureReal_restrict_apply measurableSet_Iic]
    have heq : Set.Iic c ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 c := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨ht, h0, _⟩; exact ⟨h0, ht⟩
      · rintro ⟨h0, htc⟩; exact ⟨htc, h0, htc.trans hc1⟩
    change volume.real (Set.Iic c ∩ Set.Icc (0 : ℝ) 1) = _
    rw [heq, measureReal_def, Real.volume_Icc]
    simpa using ENNReal.toReal_ofReal hc0
  refine ⟨q, ⟨fun A ↦ measureReal_nonneg, ?_⟩, ?_, ?_⟩
  · have h := hevent (fun _ ↦ True)
    simpa [μ, measureReal_def, Real.volume_Icc] using h
  · intro i
    trans μ.real {t | i ∈ f t}
    · exact hevent (fun A ↦ i ∈ A)
    simpa only [f, mem_filter, mem_univ, true_and] using hmass (a i) (ha0 i) (ha1 i)
  · intro i j
    trans μ.real {t | i ∈ f t ∧ j ∈ f t}
    · exact hevent (fun A ↦ i ∈ A ∧ j ∈ A)
    simpa only [f, mem_filter, mem_univ, true_and, le_min_iff] using
      hmass (min (a i) (a j)) (le_min (ha0 i) (ha0 j)) ((min_le_left _ _).trans (ha1 i))

/-- A finite version of the first-accepted-trial construction, with states the
set of unfinished rows. The recursion strictly decreases that finite set. -/
lemma joint_of_trials [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i))
    (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (A : E → Finset I) (label : E → J)
    (hmarg : ∀ i y, (∑ e, if i ∈ A e ∧ label e = y then t e else 0) = p i y)
    (D : I → I → ℝ)
    (hpair : ∀ i j,
      (∑ e, if Xor (i ∈ A e) (j ∈ A e) then t e else 0) ≤
        D i j * (∑ e, if i ∈ A e ∨ j ∈ A e then t e else 0)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤ D i j) := by
  have hacc (i : I) : (∑ e, if i ∈ A e then t e else 0) = 1 := by
    have h := congrArg (fun g : J → ℝ ↦ ∑ y, g y) (funext (hmarg i))
    change (∑ y, ∑ e, if i ∈ A e ∧ label e = y then t e else 0) = ∑ y, p i y at h
    rw [sum_comm, (hp i).2] at h
    convert h using 1
    apply sum_congr rfl
    intro e _
    by_cases hi : i ∈ A e <;> simp [hi]
  let base : I → J := fun _ ↦ Classical.choice (inferInstance : Nonempty J)
  have hpartial (S : Finset I) :
      ∃ q : (I → J) → ℝ, Law q ∧
        (∀ i ∈ S, ∀ y, (∑ f, if f i = y then q f else 0) = p i y) ∧
        (∀ i ∈ S, ∀ j ∈ S, (∑ f, if f i ≠ f j then q f else 0) ≤ D i j) := by
    refine Finset.strongInductionOn S ?_
    intro S ih
    by_cases hS : S.Nonempty
    · let active : E → Prop := fun e ↦ (S ∩ A e).Nonempty
      let r : E → ℝ := fun e ↦ if active e then t e else 0
      let Q : ℝ := ∑ e, r e
      have hr (e : E) : 0 ≤ r e := by dsimp [r]; split_ifs <;> simp_all
      have hactive (i : I) (hi : i ∈ S) (e : E) (ha : i ∈ A e) : active e :=
        ⟨i, mem_inter.2 ⟨hi, ha⟩⟩
      have hQ : 0 < Q := by
        obtain ⟨i, hi⟩ := hS
        have hle : (∑ e, if i ∈ A e then t e else 0) ≤ Q := by
          apply sum_le_sum
          intro e _
          by_cases ha : i ∈ A e
          · simp only [ha, ↓reduceIte, r, hactive i hi e ha, le_refl]
          · simpa only [ha, ↓reduceIte] using hr e
        rw [hacc] at hle
        linarith
      have hrec (e : E) : ∃ q : (I → J) → ℝ, Law q ∧
          (active e →
            (∀ i ∈ S \ A e, ∀ y, (∑ f, if f i = y then q f else 0) = p i y) ∧
            (∀ i ∈ S \ A e, ∀ j ∈ S \ A e,
              (∑ f, if f i ≠ f j then q f else 0) ≤ D i j)) := by
        by_cases he : active e
        · have hlt : S \ A e ⊂ S := by
            refine Finset.ssubset_iff_subset_ne.2 ⟨sdiff_subset, ?_⟩
            intro heq
            obtain ⟨i, hi⟩ := he
            obtain ⟨hiS, hiA⟩ := mem_inter.1 hi
            rw [← heq] at hiS
            exact (mem_sdiff.1 hiS).2 hiA
          obtain ⟨q, hq, hqm, hqd⟩ := ih (S \ A e) hlt
          exact ⟨q, hq, fun _ ↦ ⟨hqm, hqd⟩⟩
        · exact ⟨_, law_dirac base, fun h ↦ (he h).elim⟩
      choose q hq hqrec using hrec
      let update : E → (I → J) → (I → J) :=
        fun e f i ↦ if i ∈ A e then label e else f i
      let coeff : E → ℝ := fun e ↦ r e / Q
      have hcoeff : Law coeff := by
        refine ⟨fun e ↦ div_nonneg (hr e) hQ.le, ?_⟩
        dsimp [coeff]
        rw [← sum_div]
        exact div_self hQ.ne'
      let out : (I → J) → ℝ := mix coeff (fun e ↦ push (q e) (update e))
      refine ⟨out, law_mix hcoeff (fun e ↦ law_push (hq e) (update e)), ?_, ?_⟩
      · intro i hi y
        change (∑ f, if f i = y then mix coeff (fun e ↦ push (q e) (update e)) f else 0) = _
        rw [expected_indicator_mix]
        simp_rw [expected_indicator_push]
        have heq (e : E) :
            r e * (∑ f, if update e f i = y then q e f else 0) =
              (if i ∈ A e ∧ label e = y then t e else 0) +
                p i y * (r e - if i ∈ A e then t e else 0) := by
          by_cases ha : i ∈ A e
          · have hb := hactive i hi e ha
            simp only [update, ha, ↓reduceIte, r, hb, true_and, sub_self, mul_zero, add_zero,
              sum_ite_irrel, (hq e).2]
            split_ifs <;> simp
          · have hni : i ∈ S \ A e := mem_sdiff.2 ⟨hi, ha⟩
            by_cases hb : active e
            · have hm := (hqrec e hb).1 i hni y
              simp only [update, ha, ↓reduceIte, false_and, r, hb, sub_zero, zero_add] at *
              rw [hm]
              ring
            · simp [r, hb, ha]
        simp only [coeff, div_mul_eq_mul_div, ← sum_div]
        simp_rw [heq]
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, hmarg, hacc]
        change (p i y + p i y * (Q - 1)) / Q = p i y
        field_simp
        ring
      · intro i hi j hj
        change (∑ f, if f i ≠ f j then mix coeff (fun e ↦ push (q e) (update e)) f else 0) ≤ _
        have hem : (∑ f, if f i ≠ f j then mix coeff (fun e ↦ push (q e) (update e)) f else 0) =
            ∑ e, coeff e * ∑ f, if f i ≠ f j then push (q e) (update e) f else 0 :=
          expected_indicator_mix coeff (fun e ↦ push (q e) (update e)) (fun f ↦ f i ≠ f j)
        rw [hem]
        simp_rw [expected_indicator_push]
        have he (e : E) :
            r e * (∑ f, if update e f i ≠ update e f j then q e f else 0) ≤
              D i j * r e + (if Xor (i ∈ A e) (j ∈ A e) then t e else 0) -
                D i j * (if i ∈ A e ∨ j ∈ A e then t e else 0) := by
          by_cases hai : i ∈ A e <;> by_cases haj : j ∈ A e
          · have hb := hactive i hi e hai
            simp [update, hai, haj, r, hb, Xor]
          · have hb := hactive i hi e hai
            have hle := mul_le_mul_of_nonneg_left
              (prob_event_le_one (hq e) (fun f ↦ label e ≠ f j)) (ht e)
            simpa [update, hai, haj, r, hb, Xor] using hle
          · have hb := hactive j hj e haj
            have hle := mul_le_mul_of_nonneg_left
              (prob_event_le_one (hq e) (fun f ↦ f i ≠ label e)) (ht e)
            simpa [update, hai, haj, r, hb, Xor] using hle
          · by_cases hb : active e
            · have hle := mul_le_mul_of_nonneg_left
                ((hqrec e hb).2 i (mem_sdiff.2 ⟨hi, hai⟩) j (mem_sdiff.2 ⟨hj, haj⟩)) (ht e)
              simpa [update, hai, haj, r, hb, Xor, mul_comm] using hle
            · simp [r, hb, hai, haj, Xor]
        have hsum := sum_le_sum (s := univ) (fun e _ ↦ he e)
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
        have hbound : (∑ e, r e * ∑ f, if update e f i ≠ update e f j then q e f else 0) ≤
            D i j * Q := by
          have hpij := hpair i j
          dsimp [Q]
          linarith
        simp only [coeff, div_mul_eq_mul_div, ← sum_div]
        exact (div_le_iff₀ hQ).2 (by nlinarith [hbound])
    · refine ⟨_, law_dirac base, ?_, ?_⟩ <;> simp_all
  obtain ⟨q, hq, hm, hd⟩ := hpartial univ
  exact ⟨q, hq, fun i ↦ hm i (mem_univ i), fun i j ↦ hd i (mem_univ i) j (mem_univ j)⟩

lemma sum_abs_eq (a b : ℝ) : a + b - 2 * min a b = |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring

/-- The joint finite law in the shared rejection lemma, with its sharp bound. -/
lemma shared_rejection [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤
        2 * dist (p i) (p j) / (1 + dist (p i) (p j))) := by
  have hbound (i : I) (y : J) : p i y ≤ 1 := by
    rw [← (hp i).2]
    exact single_le_sum (fun z _ ↦ (hp i).1 z) (mem_univ y)
  have hex (y : J) := exists_threshold_law (fun i ↦ p i y) (fun i ↦ (hp i).1 y) (fun i ↦ hbound i y)
  choose q hq hsingle hboth using hex
  let t : J × Finset I → ℝ := fun e ↦ q e.1 e.2
  have hmarg (i : I) (y : J) :
      (∑ e : J × Finset I, if i ∈ e.2 ∧ e.1 = y then t e else 0) = p i y := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ z, if z = y then (∑ A, if i ∈ A then q z A else 0) else 0 := by
        apply sum_congr rfl
        intro z _
        by_cases hz : z = y <;> simp [hz, t]
      _ = _ := by simp [hsingle]
  have hxor (i j : I) (y : J) :
      (∑ A, if Xor (i ∈ A) (j ∈ A) then q y A else 0) = |p i y - p j y| := by
    calc
      _ = ∑ A, ((if i ∈ A then q y A else 0) + (if j ∈ A then q y A else 0) -
          2 * (if i ∈ A ∧ j ∈ A then q y A else 0)) := by
        apply sum_congr rfl
        intro A _
        by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj, Xor]
        ring
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hsingle, hsingle, hboth]
        exact sum_abs_eq _ _
  have hor (i j : I) (y : J) :
      (∑ A, if i ∈ A ∨ j ∈ A then q y A else 0) =
        (p i y + p j y + |p i y - p j y|) / 2 := by
    calc
      _ = ∑ A, ((if i ∈ A then q y A else 0) + (if j ∈ A then q y A else 0) -
          (if i ∈ A ∧ j ∈ A then q y A else 0)) := by
        apply sum_congr rfl
        intro A _
        by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj]
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, hsingle, hsingle, hboth]
        linarith [sum_abs_eq (p i y) (p j y)]
  have hdist0 (i j : I) : 0 ≤ dist (p i) (p j) :=
    div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
  apply joint_of_trials p hp t (fun e ↦ (hq e.1).1 e.2) Prod.snd Prod.fst hmarg
    (fun i j ↦ 2 * dist (p i) (p j) / (1 + dist (p i) (p j)))
  intro i j
  have hden : 1 + dist (p i) (p j) ≠ 0 := by linarith [hdist0 i j]
  have hX : (∑ e : J × Finset I, if Xor (i ∈ e.2) (j ∈ e.2) then t e else 0) =
      2 * dist (p i) (p j) := by
    rw [Fintype.sum_prod_type]
    simp only [t, hxor, dist]
    ring
  have hU : (∑ e : J × Finset I, if i ∈ e.2 ∨ j ∈ e.2 then t e else 0) =
      1 + dist (p i) (p j) := by
    rw [Fintype.sum_prod_type]
    simp only [t, hor, ← sum_div, sum_add_distrib, (hp i).2, (hp j).2, dist]
    ring
  change (∑ e : J × Finset I, if Xor (i ∈ e.2) (j ∈ e.2) then t e else 0) ≤ _
  rw [hX, hU, div_mul_cancel₀ _ hden]

lemma sharp_bound_le (p q : I → ℝ) : 2 * dist p q / (1 + dist p q) ≤ 2 * dist p q := by
  have hd : 0 ≤ dist p q := div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
  apply div_le_self (by positivity) (by linarith)

lemma positive_output {p : I → J → ℝ} {q : (I → J) → ℝ} (hq : Law q)
    (hm : ∀ i y, (∑ f, if f i = y then q f else 0) = p i y)
    {f : I → J} (hf : 0 < q f) (i : I) : 0 < p i (f i) := by
  rw [← hm]
  exact hf.trans_le (by
    have h := single_le_sum (s := univ) (a := f)
      (f := fun g ↦ if g i = f i then q g else 0)
      (fun g _ ↦ by split_ifs <;> simp_all [hq.1 g]) (mem_univ f)
    simpa using h)

lemma marginal_expectation {p : I → J → ℝ} {q : (I → J) → ℝ}
    (hm : ∀ i y, (∑ f, if f i = y then q f else 0) = p i y) (i : I) (g : J → ℝ) :
    (∑ f, q f * g (f i)) = ∑ y, p i y * g y := by
  have h := sum_push q (fun f ↦ f i) g
  simpa only [push, hm] using h.symm

lemma exists_positive_ge {q : I → ℝ} (hq : Law q) (f : I → ℝ) {L : ℝ}
    (hL : L ≤ ∑ i, q i * f i) : ∃ i, 0 < q i ∧ L ≤ f i := by
  by_contra h
  have hf : ∀ i, 0 < q i → f i < L := by
    intro i hi
    by_contra hn
    exact h ⟨i, hi, le_of_not_gt hn⟩
  obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg (fun j (_ : j ∈ univ) ↦ hq.1 j)).1
    (show 0 < ∑ j, q j by rw [hq.2]; norm_num)
  have hlt : (∑ j, q j * f j) < ∑ j, q j * L := by
    apply sum_lt_sum
    · intro j _
      rcases (hq.1 j).eq_or_lt with hj | hj
      · simp [← hj]
      · exact (mul_lt_mul_of_pos_left (hf j hj) hj).le
    · exact ⟨i, mem_univ i, mul_lt_mul_of_pos_left (hf i hi) hi⟩
  rw [← sum_mul, hq.2, one_mul] at hlt
  linarith

noncomputable def bad (p : Prop) : ℝ := if p then 0 else 1

lemma bad_and (p q : Prop) : bad (p ∧ q) ≤ bad p + bad q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bad, hp, hq]

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI
