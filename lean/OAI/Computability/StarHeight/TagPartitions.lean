import OAI.Computability.StarHeight.ShiftTable

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uΩ uι uT

namespace FiniteAvoidance

variable {Ω : Type uΩ} {ι : Type uι} [Fintype Ω]

lemma probability_nonneg (E : Set Ω) : 0 ≤ probability E :=
  div_nonneg (mass_nonneg (by intro; norm_num) _) (Nat.cast_nonneg _)

lemma probability_mono {E F : Set Ω} (hEF : E ⊆ F) :
    probability E ≤ probability F :=
  div_le_div_of_nonneg_right (mass_mono (by intro; norm_num) hEF) (Nat.cast_nonneg _)

lemma probability_union_le (E F : Set Ω) :
    probability (E ∪ F) ≤ probability E + probability F := by
  classical
  unfold probability mass
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp [he, hf]

lemma probability_iUnion_finset_le (E : ι → Set Ω) (J : Finset ι) :
    probability (⋃ i ∈ J, E i) ≤ ∑ i ∈ J, probability (E i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [probability, mass]
  | @insert i J hi ih =>
      simp only [Finset.set_biUnion_insert, Finset.sum_insert hi]
      exact (probability_union_le _ _).trans (add_le_add (le_refl _) ih)

lemma exists_avoiding [Nonempty Ω] [Fintype ι] (E : ι → Set Ω)
    (h : ∑ i, probability (E i) < 1) : ∃ x, ∀ i, x ∉ E i := by
  classical
  by_contra hn
  have hcover : (⋃ i ∈ (Finset.univ : Finset ι), E i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_const, Set.mem_univ, iff_true]
    by_contra hx
    exact hn ⟨x, by simpa only [not_exists] using hx⟩
  have hh := probability_iUnion_finset_le E Finset.univ
  rw [hcover, probability_univ] at hh
  linarith

end FiniteAvoidance

namespace TagPartitions

variable {T : Type uT} [DecidableEq T]

def Feasible (a l g n : T) : Prop := a ≠ l ∧ ({a, l} : Finset T) ≠ {g, n}

def Satisfies (a l g n : T) (p : T → Bool) : Prop :=
  p a = false ∧ p l = true ∧ p g = p n

lemma feasible_partition {a l g n : T} (h : Feasible a l g n) :
    ∃ p : T → Bool, Satisfies a l g n p := by
  classical
  obtain ⟨hal, hset⟩ := h
  let p : T → Bool := fun x => decide (x = l ∨ ((g = l ∨ n = l) ∧ (x = g ∨ x = n)))
  refine ⟨p, ?_⟩
  dsimp [Satisfies, p]
  by_cases hgl : g = l <;> by_cases hnl : n = l <;>
    by_cases hag : a = g <;> by_cases han : a = n <;>
    simp_all [Finset.pair_comm]

noncomputable def repetitions (m : ℕ) : ℕ := ⌈64 * Real.log (2 * m)⌉₊

lemma repetitions_estimate {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ 4 * ((15 : ℝ) / 16) ^ repetitions m ≤ 1 / 16 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by nlinarith)
  have hn := Nat.le_ceil (64 * Real.log (2 * m))
  change 64 * Real.log (2 * m) ≤ (repetitions m : ℝ) at hn
  have hpow : ((15 : ℝ) / 16) ^ repetitions m ≤
      Real.exp (-4 * Real.log (2 * m)) := by
    calc
      _ ≤ Real.exp (-(1 / 16 : ℝ)) ^ repetitions m :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.one_sub_le_exp_neg (1 / 16 : ℝ)]) _
      _ = Real.exp ((repetitions m : ℝ) * (-(1 / 16))) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-4 * Real.log (2 * m)) = ((2 * m : ℝ) ^ 4)⁻¹ := by
    rw [show -4 * Real.log (2 * m) = -(4 * Real.log (2 * m)) by ring,
      Real.exp_neg, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by positivity)]
  calc
    (m : ℝ) ^ 4 * ((15 : ℝ) / 16) ^ repetitions m ≤
        (m : ℝ) ^ 4 * ((2 * m : ℝ) ^ 4)⁻¹ := by
          rw [← he]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 1 / 16 := by field_simp; ring

lemma repetitions_bound {m : ℕ} (hm : 0 < m) :
    (repetitions m : ℝ) ≤ 66 * Real.log (2 * m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : (1 / 2 : ℝ) < Real.log (2 * m) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ 2 * m by linarith)
    linarith [Real.log_two_gt_d9]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 64 * Real.log (2 * m) by positivity)
  change (repetitions m : ℝ) < _ at hceil
  linarith

lemma repetitions_pos {m : ℕ} (hm : 0 < m) : 0 < repetitions m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log (2 * m) := Real.log_pos (by linarith)
  have hn := Nat.le_ceil (64 * Real.log (2 * m))
  change 64 * Real.log (2 * m) ≤ (repetitions m : ℝ) at hn
  by_contra hn0
  have hz : repetitions m = 0 := by omega
  simp [hz] at hn
  linarith

lemma probability_satisfies [Fintype T] (N : ℕ) (i : Fin N)
    {a l g n : T} (h : Feasible a l g n) :
    1 / 16 ≤ FiniteAvoidance.probability
      {β : (Fin N × T) → Bool | Satisfies a l g n (fun t => β (i, t))} := by
  classical
  obtain ⟨p, hp⟩ := feasible_partition h
  let s : Finset (Fin N × T) := {(i, a), (i, l), (i, g), (i, n)}
  let d : (Fin N × T) → Bool := fun c => p c.2
  have hsub : {β : (Fin N × T) → Bool | Set.EqOn β d s} ⊆
      {β | Satisfies a l g n (fun t => β (i, t))} := by
    intro β hβ
    obtain ⟨ha, hl, hgn⟩ := hp
    dsimp [Satisfies]
    have he (t) (ht : (i, t) ∈ s) : β (i, t) = p t := hβ ht
    rw [he a (by simp [s]), he l (by simp [s]), he g (by simp [s]), he n (by simp [s])]
    exact ⟨ha, hl, hgn⟩
  have hprob := FiniteAvoidance.probability_mono hsub
  rw [FiniteProduct.probability_agreement] at hprob
  simp only [Fintype.card_bool, Nat.cast_ofNat, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hprob
  have hcard : s.card ≤ 4 := by
    dsimp [s]
    exact (Finset.card_insert_le _ _).trans (by
      have h1 := Finset.card_insert_le (i, l) ({(i, g), (i, n)} : Finset (Fin N × T))
      have h2 := Finset.card_insert_le (i, g) ({(i, n)} : Finset (Fin N × T))
      simp only [Finset.card_singleton] at h2
      omega)
  have hpow : (2 : ℝ) ^ s.card ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hcard
      _ = _ := by norm_num
  have hinv : (1 / 16 : ℝ) ≤ ((2 : ℝ) ^ s.card)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ s.card) hpow
  exact hinv.trans hprob

omit [DecidableEq T] in
lemma satisfies_depends (N : ℕ) (i : Fin N) (a l g n : T) :
    FiniteProduct.DependsOn
      {β : (Fin N × T) → Bool | Satisfies a l g n (fun t => β (i, t))}
      {c | c.1 = i} := by
  intro β γ he
  have hrow : (fun t => β (i, t)) = (fun t => γ (i, t)) :=
    funext (fun t => he (by rfl))
  simp only [Set.mem_ofPred_eq, hrow]

lemma probability_failure [Fintype T] (N : ℕ) {a l g n : T}
    (h : Feasible a l g n) :
    FiniteAvoidance.probability
      {β : (Fin N × T) → Bool | ∀ i, ¬ Satisfies a l g n (fun t => β (i, t))} ≤
      ((15 : ℝ) / 16) ^ N := by
  classical
  let E (i : Fin N) : Set ((Fin N × T) → Bool) :=
    {β | ¬ Satisfies a l g n (fun t => β (i, t))}
  have hdep (i) : FiniteProduct.DependsOn (E i) {c | c.1 = i} :=
    (satisfies_depends N i a l g n).compl
  have hd : Pairwise (fun i j : Fin N => Disjoint {c : Fin N × T | c.1 = i} {c | c.1 = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (by intro c hi hj; exact hij (hi.symm.trans hj))
  have heq : {β : (Fin N × T) → Bool | ∀ i, ¬ Satisfies a l g n (fun t => β (i, t))} =
      FiniteProduct.allEvents E Finset.univ := by ext β; simp [FiniteProduct.allEvents, E]
  rw [heq, FiniteProduct.probability_allEvents E _ hdep hd]
  calc
    _ ≤ ∏ _i : Fin N, ((15 : ℝ) / 16) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact FiniteAvoidance.probability_nonneg _
      · intro i _
        change FiniteAvoidance.probability
          ({β : (Fin N × T) → Bool | Satisfies a l g n (fun t => β (i, t))}ᶜ) ≤ _
        rw [FiniteAvoidance.probability_compl]
        linarith [probability_satisfies N i h]
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem exists_partitions [Fintype T] [Nonempty T] :
    ∃ p : Fin (repetitions (Fintype.card T)) → T → Bool,
      ∀ a l g n, Feasible a l g n → ∃ i,
        Satisfies a l g n (p i) := by
  classical
  let N := repetitions (Fintype.card T)
  let E : (T × T × T × T) → Set ((Fin N × T) → Bool) := fun q =>
    {β | Feasible q.1 q.2.1 q.2.2.1 q.2.2.2 ∧
      ∀ i, ¬ Satisfies q.1 q.2.1 q.2.2.1 q.2.2.2 (fun t => β (i, t))}
  have hbound (q) : FiniteAvoidance.probability (E q) ≤ ((15 : ℝ) / 16) ^ N := by
    by_cases hq : Feasible q.1 q.2.1 q.2.2.1 q.2.2.2
    · exact (FiniteAvoidance.probability_mono (by intro β hβ; exact hβ.2)).trans
        (probability_failure N hq)
    · simp [E, hq, FiniteAvoidance.probability, FiniteAvoidance.mass]
      positivity
  have hsum : ∑ q, FiniteAvoidance.probability (E q) < 1 := by
    calc
      _ ≤ ∑ _q : T × T × T × T, ((15 : ℝ) / 16) ^ N :=
        Finset.sum_le_sum (fun q _ => hbound q)
      _ = (Fintype.card T : ℝ) ^ 4 * ((15 : ℝ) / 16) ^ N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
          Nat.cast_mul]
        ring
      _ ≤ 1 / 16 := repetitions_estimate Fintype.card_pos
      _ < 1 := by norm_num
  obtain ⟨β, hβ⟩ := FiniteAvoidance.exists_avoiding E hsum
  refine ⟨fun i t => β (i, t), ?_⟩
  intro a l g n h
  have hh := hβ (a, l, g, n)
  by_contra hn
  push Not at hn
  exact hh ⟨h, hn⟩

noncomputable def typeCount (m : ℕ) : ℕ := ⌈Real.log m / Real.log 2⌉₊

lemma card_le_binary {m : ℕ} (hm : 0 < m) : m ≤ 2 ^ typeCount m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := Nat.le_ceil (Real.log m / Real.log 2)
  change Real.log m / Real.log 2 ≤ (typeCount m : ℝ) at hn
  have hh : Real.log m ≤ (typeCount m : ℝ) * Real.log 2 := (div_le_iff₀ h2).mp hn
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log hmR, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  exact_mod_cast he

lemma typeCount_bound {m : ℕ} (hm : 0 < m) :
    (typeCount m : ℝ) ≤ 2 * Real.log (2 * m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogm := Real.log_nonneg hm1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log m / Real.log 2 by positivity)
  change (typeCount m : ℝ) < Real.log m / Real.log 2 + 1 at hceil
  have hh : (typeCount m : ℝ) * Real.log 2 < Real.log m + Real.log 2 := by
    have h := (mul_lt_mul_iff_left₀ (show 0 < Real.log 2 by linarith)).mpr hceil
    rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt (show 0 < Real.log 2 by linarith)), one_mul] at h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmR.ne']
  have hcount : (0 : ℝ) ≤ typeCount m := Nat.cast_nonneg _
  nlinarith

omit [DecidableEq T] in
lemma exists_types [Fintype T] [Nonempty T] :
    ∃ p : Fin (typeCount (Fintype.card T)) → T → Bool,
      ∀ a l, a ≠ l → ∃ i, p i a ≠ p i l := by
  classical
  have hcard : Fintype.card T ≤ Fintype.card (Fin (typeCount (Fintype.card T)) → Bool) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using
      card_le_binary (m := Fintype.card T) Fintype.card_pos
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun i a => f a i, ?_⟩
  intro a l hal
  by_contra hn
  push Not at hn
  exact hal (f.injective (funext hn))

lemma total_count_bound {m : ℕ} (hm : 0 < m) :
    ((repetitions m + 4 * 400 ^ 2 * typeCount m : ℕ) : ℝ) ≤
      10000000 * Real.log (2 * m) := by
  have ha := repetitions_bound hm
  have hb := typeCount_bound hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  push_cast
  nlinarith

end TagPartitions

end GeneralizedStarHeight

end OAI
