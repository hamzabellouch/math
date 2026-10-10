import Mathlib
import OAI.Combinatorics.BalancedRyser.Probability.FiniteKernelPotential
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionScales

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

def PrescriptionsAgree (J : Finset I) (a : I → V) (S : State I V) : Prop :=
  ∀ i ∈ J, i ∉ S.remaining → S.recorded i = some (a i)

def cylinderPotential (J : Finset I) (a : I → V) (c : ℝ) (S : State I V) : ℝ :=
  if PrescriptionsAgree J a S then c ^ (J ∩ S.remaining).card else 0

def outcomePotential (J : Finset I) (a : I → V) (c : ℝ) : Option (State I V) → ℝ
  | none => 0
  | some S => cylinderPotential J a c S

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_nonneg (J : Finset I) (a : I → V) {c : ℝ} (hc : 0 ≤ c)
    (S : State I V) : 0 ≤ cylinderPotential J a c S := by
  unfold cylinderPotential
  split_ifs <;> positivity

lemma cylinderPotential_initial (J : Finset I) (a : I → V) (c : ℝ) :
    cylinderPotential J a c initialState = c ^ J.card := by
  simp [cylinderPotential, PrescriptionsAgree, initialState]

omit [Fintype I] [Fintype V] in
lemma prescriptionsAgree_update_iff (G : Input I V) (J : Finset I) (a : I → V)
    (S : State I V) (i : I) (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    PrescriptionsAgree J a (update G S i w flags) ↔
      PrescriptionsAgree J a S ∧ (i ∈ J → w = a i) := by
  constructor
  · intro h
    constructor
    · intro j hj hjR
      have hji : j ≠ i := by intro hji; subst j; contradiction
      have h' := h j hj (by simp [update, hjR])
      simpa [update, Function.update_of_ne hji] using h'
    · intro hiJ
      have h' := h i hiJ (by simp [update])
      simpa [update] using h'
  · rintro ⟨h, hw⟩ j hj hjR
    by_cases hji : j = i
    · subst j
      simp [update, hw hj]
    · have hjR' : j ∉ S.remaining := by
        simpa [update, Finset.mem_erase, hji] using hjR
      have h' := h j hj hjR'
      simpa [update, Function.update_of_ne hji] using h'

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_update_flags (G : Input I V) (J : Finset I) (a : I → V)
    (c : ℝ) (S : State I V) (i : I) (w : V) (flags flags' : V → Bool) :
    cylinderPotential J a c (update G S i w flags) =
      cylinderPotential J a c (update G S i w flags') := rfl

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_update_unprescribed (G : Input I V) (J : Finset I)
    (a : I → V) (c : ℝ) (S : State I V) (i : I) (hi : i ∈ S.remaining)
    (hiJ : i ∉ J) (w : V) (flags : V → Bool) :
    cylinderPotential J a c (update G S i w flags) = cylinderPotential J a c S := by
  have hset : J ∩ S.remaining.erase i = J ∩ S.remaining := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase]
    aesop
  simp only [cylinderPotential, prescriptionsAgree_update_iff G J a S i hi w flags,
    hiJ, false_implies, and_true]
  change (if PrescriptionsAgree J a S then c ^ (J ∩ S.remaining.erase i).card else 0) = _
  rw [hset]

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_update_prescribed (G : Input I V) (J : Finset I)
    (a : I → V) (c : ℝ) (S : State I V) (i : I) (hi : i ∈ S.remaining)
    (hiJ : i ∈ J) (w : V) (flags : V → Bool) :
    cylinderPotential J a c (update G S i w flags) =
      if w = a i then cylinderPotential J a c (update G S i (a i) (fun _ => false)) else 0 := by
  simp only [cylinderPotential, prescriptionsAgree_update_iff G J a S i hi,
    hiJ, true_implies]
  by_cases hw : w = a i <;> simp [hw, update]

omit [Fintype I] [Fintype V] in
lemma cylinderPotential_pay_one (G : Input I V) (J : Finset I)
    (a : I → V) (c : ℝ) (S : State I V) (i : I) (hi : i ∈ S.remaining)
    (hiJ : i ∈ J) :
    c * cylinderPotential J a c (update G S i (a i) (fun _ => false)) =
      cylinderPotential J a c S := by
  have hmem : i ∈ J ∩ S.remaining := Finset.mem_inter.mpr ⟨hiJ, hi⟩
  have hset : J ∩ S.remaining.erase i = (J ∩ S.remaining).erase i := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have hcard := Finset.card_erase_add_one hmem
  simp only [cylinderPotential, prescriptionsAgree_update_iff G J a S i hi,
    hiJ, true_implies, and_true]
  by_cases h : PrescriptionsAgree J a S
  · simp only [h, ite_true]
    change c * c ^ (J ∩ S.remaining.erase i).card = c ^ (J ∩ S.remaining).card
    rw [hset, ← hcard, pow_succ]
    ring
  · simp [h]

omit [Fintype I] in
lemma sum_flagsWeight_potential (p : Parameters) (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (S : State I V) (i : I) (w : V) :
    (∑ flags : V → Bool, flagsWeight p q G S flags *
      cylinderPotential J a c (update G S i w flags)) =
        cylinderPotential J a c (update G S i w (fun _ => false)) := by
  simp_rw [cylinderPotential_update_flags G J a c S i w _ (fun _ => false)]
  rw [← Finset.sum_mul, sum_flagsWeight, one_mul]

omit [Fintype I] in
lemma sum_drawWeight_potential_le (G : Input I V) (J : Finset I) (a : I → V)
    (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (i : I) (hi : i ∈ S.remaining) (hbound : ((domain G S i).card : ℝ)⁻¹ ≤ c) :
    (∑ w : V, drawWeight G S i w *
      cylinderPotential J a c (update G S i w (fun _ => false))) ≤
        (S.remaining.card : ℝ)⁻¹ * cylinderPotential J a c S := by
  by_cases hiJ : i ∈ J
  · have hsum : (∑ w : V, drawWeight G S i w *
        cylinderPotential J a c (update G S i w (fun _ => false))) =
        ∑ w : V, if w = a i then drawWeight G S i w *
          cylinderPotential J a c (update G S i (a i) (fun _ => false)) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [cylinderPotential_update_prescribed G J a c S i hi hiJ]
      split_ifs <;> simp
    rw [hsum, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    by_cases ha : a i ∈ domain G S i
    · have hnonneg := cylinderPotential_nonneg J a hc (update G S i (a i) (fun _ => false))
      have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbound hnonneg)
        (by positivity : (0 : ℝ) ≤ (S.remaining.card : ℝ)⁻¹)
      rw [cylinderPotential_pay_one G J a c S i hi hiJ] at hb
      simpa [drawWeight, hi, ha, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hb
    · simp only [drawWeight, hi, ha, and_false, ite_false, zero_mul]
      exact mul_nonneg (by positivity) (cylinderPotential_nonneg J a hc S)
  · simp_rw [cylinderPotential_update_unprescribed G J a c S i hi hiJ]
    rw [← Finset.sum_mul, sum_drawWeight_vertex G S hS hdom, ite_eq_left hi]

lemma sum_noiseWeight_potential_le (p : Parameters) (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (hbound : ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      cylinderPotential J a c (update G S r.1 r.2.1 r.2.2)) ≤
        cylinderPotential J a c S := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight, mul_assoc]
  simp_rw [← Finset.mul_sum, sum_flagsWeight_potential]
  calc
    (∑ i : I, ∑ w : V, drawWeight G S i w *
      cylinderPotential J a c (update G S i w (fun _ => false))) ≤
        ∑ i : I, if i ∈ S.remaining then
          (S.remaining.card : ℝ)⁻¹ * cylinderPotential J a c S else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiR : i ∈ S.remaining
      · rw [ite_eq_left hiR]
        exact sum_drawWeight_potential_le G J a c hc S hS hdom i hiR (hbound i hiR)
      · simp [drawWeight, hiR]
    _ = cylinderPotential J a c S := by
      have hcardS : (S.remaining.card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr hS
      rw [← Finset.sum_filter]
      simp [hcardS]

omit [Fintype I] [Fintype V] in
lemma outcomePotential_nonneg (J : Finset I) (a : I → V) {c : ℝ} (hc : 0 ≤ c)
    (out : Option (State I V)) : 0 ≤ outcomePotential J a c out := by
  cases out with
  | none => exact le_rfl
  | some S => exact cylinderPotential_nonneg J a hc S

omit [Fintype I] in
lemma outcomePotential_performedResult_le (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (r : Noise I V) :
    outcomePotential J a c (performedResult q G S r) ≤
      cylinderPotential J a c (update G S r.1 r.2.1 r.2.2) := by
  unfold performedResult
  split_ifs
  · exact le_rfl
  · exact cylinderPotential_nonneg J a hc _

lemma sum_stepWeight_potential_eq (p : Parameters) (q t : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (S : State I V)
    (hp : Precheck p q t G S) :
    (∑ out, stepWeight p q t G S out * outcomePotential J a c out) =
      ∑ r : Noise I V, noiseWeight p q G S r *
        outcomePotential J a c (performedResult q G S r) := by
  simp only [stepWeight, hp, ite_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp_rw [ite_mul, zero_mul]
  simp

lemma sum_stepWeight_potential_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c) (S : State I V)
    (hbound : Precheck p q t G S →
      ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c) :
    (∑ out, stepWeight p q t G S out * outcomePotential J a c out) ≤
      cylinderPotential J a c S := by
  by_cases hp : Precheck p q t G S
  · rw [sum_stepWeight_potential_eq p q t G J a c S hp]
    calc
      (∑ r : Noise I V, noiseWeight p q G S r *
        outcomePotential J a c (performedResult q G S r)) ≤
          ∑ r : Noise I V, noiseWeight p q G S r *
            cylinderPotential J a c (update G S r.1 r.2.1 r.2.2) := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left
          (outcomePotential_performedResult_le q G J a c hc S r)
          (noiseWeight_nonnegative_of_precheck p q t G S hp r)
      _ ≤ cylinderPotential J a c S :=
        sum_noiseWeight_potential_le p q G J a c hc S hp.1
          (fun i hi => (hp.2.2.2.1 i hi).1) (hbound hp)
  · simpa [stepWeight, hp, outcomePotential] using cylinderPotential_nonneg J a hc S

lemma sum_transitionWeight_potential_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ S : State I V, Precheck p q t G S →
      ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c)
    (before : Option (State I V)) :
    (∑ out, transitionWeight p q t G before out * outcomePotential J a c out) ≤
      outcomePotential J a c before := by
  cases before with
  | none => simp [transitionWeight, outcomePotential]
  | some S => exact sum_stepWeight_potential_le p q t G J a c hc S (hbound S)

omit [Fintype I] in

lemma domain_reciprocal_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (hc : 0 < p.c) (hq : 0 < q)
    (hs : p.smin ≤ p.sizeScale q t) (i : I) (hi : i ∈ S.remaining) :
    ((domain G S i).card : ℝ)⁻¹ ≤ 2 / (p.smin * p.c * q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hbase : 0 < p.smin * p.c * q / 2 := by positivity
  have hbarrier : p.smin * p.c * q / 2 ≤ ((domain G S i).card : ℝ) := by
    calc
      p.smin * p.c * q / 2 ≤ p.sizeScale q t * p.c * q / 2 := by
        gcongr
      _ ≤ _ := (hp.2.2.2.1 i hi).2
  have h := one_div_le_one_div_of_le hbase hbarrier
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using h

lemma historyWeight_payoff_le (p : Parameters) (q T : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ t < T, ∀ S : State I V, Precheck p q t G S →
      ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c)
    (payoff : Option (State I V) → ℝ)
    (hpayoff : ∀ out, payoff out ≤ outcomePotential J a c out) :
    (∑ out, historyWeight p q G T out * payoff out) ≤ c ^ J.card := by
  let Φ : ℕ → Option (State I V) → ℝ :=
    fun t out => if t ≤ T then outcomePotential J a c out else 0
  have hstep : ∀ t before,
      (∑ out, transitionWeight p q t G before out * Φ (t + 1) out) ≤ Φ t before := by
    intro t before
    by_cases ht : t < T
    · have ht1 : t + 1 ≤ T := ht
      simpa [Φ, ht.le, ht1] using
        sum_transitionWeight_potential_le p q t G J a c hc (hbound t ht) before
    · have ht1 : ¬ t + 1 ≤ T := by omega
      by_cases ht0 : t ≤ T
      · simpa [Φ, ht0, ht1] using outcomePotential_nonneg J a hc before
      · simp [Φ, ht0, ht1]
  have h := FiniteKernelPotential.evolution_payoff_le
    (fun t => transitionWeight p q t G) (historyWeight p q G) Φ payoff
    (fun _ _ => rfl) (transitionWeight_nonnegative p q · G)
    (historyWeight_nonnegative p q G 0) hstep T (by simpa [Φ] using hpayoff)
  simpa [Φ, historyWeight, outcomePotential, cylinderPotential_initial] using h

lemma historyWeight_potential_le (p : Parameters) (q T : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ t < T, ∀ S : State I V, Precheck p q t G S →
      ∀ i ∈ S.remaining, ((domain G S i).card : ℝ)⁻¹ ≤ c) :
    (∑ out, historyWeight p q G T out * outcomePotential J a c out) ≤ c ^ J.card :=
  historyWeight_payoff_le p q T G J a c hc hbound _ (fun _ => le_rfl)

def cylinderConstant (p : Parameters) : ℝ :=
  max 1 (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c))

lemma cylinderConstant_pos (p : Parameters) : 0 < cylinderConstant p :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

lemma main_cost_le_cylinderConstant (p : Parameters) (q : ℕ)
    (hc : 0 < p.c) (hq : 0 < q) :
    2 / (p.smin * p.c * q) ≤ cylinderConstant p / q := by
  have hden : 0 < p.smin * p.c := mul_pos (Real.exp_pos _) hc
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hexp : 1 ≤ Real.exp (1 / 2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hmain : 2 / (p.smin * p.c) ≤
      2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c) := by
    apply div_le_div_of_nonneg_right _ hden.le
    linarith
  have hK : 2 / (p.smin * p.c) ≤ cylinderConstant p :=
    hmain.trans (le_max_right _ _)
  simpa only [div_div] using div_le_div_of_nonneg_right hK hqR.le

lemma historyWeight_payoff_source_bound (p : Parameters) (q T : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (hc : 0 < p.c) (hP : 0 ≤ p.Pstar)
    (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hT : T ≤ 3 * q)
    (payoff : Option (State I V) → ℝ)
    (hpayoff : ∀ out, payoff out ≤
      outcomePotential J a (cylinderConstant p / q) out) :
    (∑ out, historyWeight p q G T out * payoff out) ≤
      (cylinderConstant p / q) ^ J.card := by
  apply historyWeight_payoff_le p q T G J a _
    (div_nonneg (cylinderConstant_pos p).le (Nat.cast_nonneg q)) _ payoff hpayoff
  intro t ht S hp i hi
  have hscale : p.smin ≤ p.sizeScale q t := by
    exact (SelectionScales.domain_bounds hP hq hPq (ht.le.trans hT)).1
  exact (domain_reciprocal_le p q t G S hp hc hq hscale i hi).trans
    (main_cost_le_cylinderConstant p q hc hq)

lemma tail_cost_le_cylinderConstant (p : Parameters) (q : ℕ) :
    Real.exp (1 / 2 : ℝ) * (2 / (p.smin * p.c * q)) ≤ cylinderConstant p / q := by
  have h := div_le_div_of_nonneg_right
    (le_max_right 1 (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c))) (Nat.cast_nonneg q)
  change Real.exp (1 / 2 : ℝ) * (2 / (p.smin * p.c * q)) ≤
    max 1 (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c)) / q
  calc
    _ = (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c)) / q := by ring
    _ ≤ _ := h

omit [Fintype I] [Fintype V] in
lemma tail_product_source_bound (p : Parameters) (q : ℕ) (hc : 0 < p.c) (hq : 0 < q)
    (U : Finset I) (D : I → Finset V)
    (hsize : ∀ i ∈ U, p.smin * p.c * q / 2 ≤ ((D i).card : ℝ)) :
    Real.exp ((U.card : ℝ) / 2) * (∏ i ∈ U, ((D i).card : ℝ)⁻¹) ≤
      (cylinderConstant p / q) ^ U.card := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hbase : 0 < p.smin * p.c * q / 2 := by positivity
  have hbound (i : I) (hi : i ∈ U) :
      ((D i).card : ℝ)⁻¹ ≤ 2 / (p.smin * p.c * q) := by
    have h := one_div_le_one_div_of_le hbase (hsize i hi)
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using h
  have hprod : (∏ i ∈ U, ((D i).card : ℝ)⁻¹) ≤
      (2 / (p.smin * p.c * q)) ^ U.card := by
    calc
      _ ≤ ∏ _i ∈ U, (2 / (p.smin * p.c * q)) := by
        exact Finset.prod_le_prod₀ (fun index _ => by positivity) hbound
      _ = _ := by simp only [Finset.prod_const]
  have hexp : Real.exp ((U.card : ℝ) / 2) = Real.exp (1 / 2 : ℝ) ^ U.card := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ ≤ Real.exp (1 / 2 : ℝ) ^ U.card *
        (2 / (p.smin * p.c * q)) ^ U.card :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (Real.exp (1 / 2 : ℝ) * (2 / (p.smin * p.c * q))) ^ U.card :=
      (mul_pow _ _ _).symm
    _ ≤ (cylinderConstant p / q) ^ U.card :=
      pow_le_pow_left₀ (by positivity) (tail_cost_le_cylinderConstant p q) _

lemma mainStageWeight_payoff_source_bound (p : Parameters) (q : ℕ) (G : Input I V)
    (J : Finset I) (a : I → V) (hp : p.Admissible) (hq : 2 ≤ q)
    (hPq : 2 * p.Pstar ≤ q) (hG : GraphBounds G q p.c p.C)
    (payoff : Option (State I V) → ℝ)
    (hpayoff : ∀ out, payoff out ≤
      outcomePotential J a (cylinderConstant p / q) out) :
    (∑ out, mainStageWeight p q G out * payoff out) ≤
      (cylinderConstant p / q) ^ J.card := by
  have hP : 0 ≤ p.Pstar := by
    unfold Parameters.Pstar
    have hc := hp.1
    have hC := hp.2.1
    positivity
  have hT : p.lastMainTime q (Fintype.card I) ≤ 3 * q := by
    calc
      p.lastMainTime q (Fintype.card I) ≤ Fintype.card I := Nat.sub_le _ _
      _ = 2 * (q + 1) := hG.1
      _ ≤ 3 * q := by omega
  exact historyWeight_payoff_source_bound p q _ G J a hp.1 hP (by omega)
    hPq hT payoff hpayoff

end
end Balanced.Selection.Process

end OAI
