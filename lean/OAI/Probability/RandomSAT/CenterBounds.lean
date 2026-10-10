import OAI.Probability.RandomSAT.Concentration

namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_exists_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) :
    uniformProbability (fun a => ∃ b, p a b) ≤ ∑ b, uniformProbability (fun a => p a b) := by
  simp only [uniformProbability_eq_mean]
  rw [← uniformMean_sum]
  apply uniformMean_mono
  intro a
  by_cases h : ∃ b, p a b
  · obtain ⟨b, hb⟩ := h
    rw [ite_eq_left ⟨b, hb⟩]
    calc
      1 = (if p a b then (1 : ℝ) else 0) := (ite_eq_left hb).symm
      _ ≤ ∑ b, if p a b then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun b => if p a b then (1 : ℝ) else 0)
          (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ b)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun b _ => by split_ifs <;> norm_num)

theorem uniformProbability_forall_fintype {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → Prop) :
    uniformProbability (fun f : β → α => ∀ b, p (f b)) = uniformProbability p ^ Fintype.card β := by
  unfold uniformProbability
  have hc : Fintype.card {f : β → α // ∀ b, p (f b)} =
      Fintype.card (β → {a : α // p a}) :=
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ : β => p))
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow, div_pow]

@[simp] theorem forcedVariables_singleton {n : ℕ} (σ : Assignment n) :
    forcedVariables ({σ} : Finset (Assignment n)) = Finset.univ := by
  ext i
  simp [forcedVariables]

theorem randomClause_satisfies {n k : ℕ} (hkn : k ≤ n) (σ : Assignment n) :
    uniformProbability (fun C : ProperClause n k => SatisfiesClause σ C) = 1 - (2 : ℝ)⁻¹ ^ k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := killingProbability_of_nonempty (k := k) {σ} (Finset.singleton_nonempty σ)
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkn)
  have hp : killingProbability k {σ} =
      uniformProbability (fun C : ProperClause n k => ¬SatisfiesClause σ C) := by
    apply uniformProbability_congr
    intro C
    simp [KillsSolutions]
  rw [hp, uniformProbability_not, forcedVariables_singleton, Finset.card_univ, Fintype.card_fin] at h
  have hr : (n.choose k : ℝ) / ((n.choose k : ℝ) * 2^k) = (2 : ℝ)⁻¹ ^ k := by
    rw [inv_pow]
    field_simp
  rw [hr] at h
  linarith

theorem first_moment_bound {n k m : ℕ} (hkn : k ≤ n) :
    properSATProbability n k m ≤ (2 : ℝ)^n * (1 - (2 : ℝ)⁻¹ ^ k)^m := by
  change uniformProbability (fun F : Formula n k m => ∃ σ, Satisfies σ F) ≤ _
  have h := uniformProbability_exists_le (fun F : Formula n k m => fun σ => Satisfies σ F)
  have hσ (σ : Assignment n) :
      uniformProbability (fun F : Formula n k m => Satisfies σ F) =
        (1 - (2 : ℝ)⁻¹ ^ k)^m := by
    change uniformProbability (fun F : Formula n k m => ∀ j, SatisfiesClause σ (F j)) = _
    rw [uniformProbability_forall, randomClause_satisfies hkn]
  simp only [hσ, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

theorem uniformMean_lower_tail {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) {t : ℝ} (_ht : 0 ≤ t) :
    t * uniformProbability (fun a => t ≤ f a) ≤ uniformMean f := by
  rw [uniformProbability_eq_mean, ← uniformMean_const_mul]
  apply uniformMean_mono
  intro a
  by_cases h : t ≤ f a
  · simpa only [ite_eq_left h, mul_one] using h
  · simpa only [ite_eq_right h, mul_zero] using hf a

theorem uniformMean_upper_cutoff {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) {M t : ℝ} (hf : ∀ a, f a ≤ M) (ht : 0 ≤ t) :
    uniformMean f ≤ t + M * uniformProbability (fun a => t ≤ f a) := by
  calc
    _ ≤ uniformMean (fun a => t + M * if t ≤ f a then (1 : ℝ) else 0) := by
      apply uniformMean_mono
      intro a
      by_cases h : t ≤ f a
      · simp only [ite_eq_left h, mul_one]
        linarith [hf a]
      · simp only [ite_eq_right h, mul_zero, add_zero]
        exact le_of_not_ge h
    _ = _ := by rw [uniformMean_add, uniformMean_const, uniformMean_const_mul,
      ← uniformProbability_eq_mean]

theorem center_lower_by_probability {n k m : ℕ} (hkn : k ≤ n) (hm : m ≤ mainCap n k) :
    (m : ℝ) / n * properSATProbability n k m ≤ center n k := by
  have h := uniformMean_lower_tail (lifetime k (mainCap n k) (Finset.univ : Finset (Assignment n)))
    (fun F => lifetime_nonneg _ F) (show 0 ≤ (m : ℝ) by positivity)
  rw [← properSATProbability_eq_lifetime_tail hkn hm] at h
  unfold center lifetimeMean
  have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [div_mul_eq_mul_div] using hh

theorem center_upper_by_probability {n k m : ℕ} (hkn : k ≤ n) (hn : 0 < n)
    (hm : m ≤ mainCap n k) :
    center n k ≤ (m : ℝ) / n + capMultiplier k * properSATProbability n k m := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := uniformMean_upper_cutoff (lifetime k (mainCap n k) (Finset.univ : Finset (Assignment n)))
    (fun F => lifetime_le _ F) (show 0 ≤ (m : ℝ) by positivity)
  rw [← properSATProbability_eq_lifetime_tail hkn hm] at h
  unfold center lifetimeMean
  have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  apply hh.trans_eq
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [mainCap, Nat.cast_mul]
  field_simp

theorem satisfiable_of_matching {n k m : ℕ} (F : Formula n k m)
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (hmem : ∀ j, f j ∈ clauseSupport (F j)) : Satisfiable F := by
  let b : Fin m → Bool := fun j => ((F j).val (f j)).getD false
  let σ : Assignment n := fun i => if h : ∃ j, f j = i then b (Classical.choose h) else false
  refine ⟨σ, fun j => ⟨f j, ?_⟩⟩
  have he : ∃ j', f j' = f j := ⟨j, rfl⟩
  have hc : Classical.choose he = j := hf (Classical.choose_spec he)
  have hs : σ (f j) = b j := by simp [σ, he, hc]
  rw [hs]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((mem_clauseSupport _ _).mp (hmem j))
  simp [b, hv]

theorem unsatisfiable_deficiency {n k m : ℕ} (F : Formula n k m) (hF : ¬Satisfiable F) :
    ∃ J : Finset (Fin m), (J.biUnion fun j => clauseSupport (F j)).card < J.card := by
  by_contra h
  push Not at h
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun j => clauseSupport (F j))).mp h
  exact hF (satisfiable_of_matching F f hf hmem)

def firstMomentBase : ℝ := 2 * Real.exp (-1)

theorem firstMomentBase_nonneg : 0 ≤ firstMomentBase := by
  unfold firstMomentBase
  positivity

theorem firstMomentBase_lt_one : firstMomentBase < 1 := by
  rw [firstMomentBase, Real.exp_neg]
  have h : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  exact (mul_inv_lt_iff₀ (Real.exp_pos 1)).mpr (by simpa using h)

theorem first_moment_linear {n k : ℕ} (hkn : k ≤ n) :
    properSATProbability n k (2^k * n) ≤ firstMomentBase^n := by
  apply (first_moment_bound hkn).trans
  have hq : 0 ≤ 1 - (2 : ℝ)⁻¹^k := by
    have := pow_le_one₀ (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1) (n := k)
    linarith
  have hp := pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg ((2 : ℝ)⁻¹^k)) (2^k * n)
  have he : Real.exp (-((2 : ℝ)⁻¹^k))^(2^k * n) = Real.exp (-1)^n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [inv_pow]
    have hk : (2 : ℝ)^k ≠ 0 := by positivity
    field_simp
  rw [he] at hp
  simpa only [firstMomentBase, mul_pow] using mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2^n)

theorem center_first_moment {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    center n k ≤ (2 : ℝ)^k + capMultiplier k * firstMomentBase^n := by
  have hm : 2^k * n ≤ mainCap n k := by
    dsimp [mainCap, capMultiplier]
    gcongr
    omega
  have h := center_upper_by_probability hkn hn hm
  have he : ((2^k * n : ℕ) : ℝ) / n = (2 : ℝ)^k := by
    push_cast
    exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.ne_of_gt hn)
  rw [he] at h
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left (first_moment_linear hkn)
    (Nat.cast_nonneg (capMultiplier k) : (0 : ℝ) ≤ capMultiplier k)) _)

theorem uniformProbability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) :
    uniformProbability (fun a => p (e a)) = uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl)), Fintype.card_congr e]

theorem uniformProbability_prod_first {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (p : α → Prop) : uniformProbability (fun x : α × β => p x.1) = uniformProbability p := by
  let e : {x : α × β // p x.1} ≃ {a : α // p a} × β := {
    toFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
    invFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul]
  have hb : (Nat.card β : ℝ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero (α := β)
  field_simp

theorem uniformProbability_forall_mem {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (J : Finset β) (p : α → Prop) :
    uniformProbability (fun f : β → α => ∀ j ∈ J, p (f j)) = uniformProbability p ^ J.card := by
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ J) (fun _ : β => α)
  calc
    _ = uniformProbability (fun f : β → α => ∀ j : ↥J, p ((e f).1 j)) :=
      uniformProbability_congr (fun f => by simp [e])
    _ = uniformProbability (fun f : (↥J → α) × ({j : β // j ∉ J} → α) =>
        ∀ j, p (f.1 j)) := uniformProbability_equiv
          (α := β → α) (β := (↥J → α) × ({j : β // j ∉ J} → α)) e
          (fun f => ∀ j, p (f.1 j))
    _ = uniformProbability (fun f : ↥J → α => ∀ j, p (f j)) :=
      uniformProbability_prod_first (α := ↥J → α) (β := {j : β // j ∉ J} → α)
        (fun f : ↥J → α => ∀ j, p (f j))
    _ = _ := by
      have h := uniformProbability_forall_fintype (α := α) (β := ↥J) p
      simpa only [Fintype.card_coe] using h

theorem uniformMean_support {n k : ℕ} (f : Finset (Fin n) → ℝ) :
    uniformMean (fun C : ProperClause n k => f (clauseSupport C)) =
      uniformMean (fun s : VariableSet n k => f s.val) := by
  have he := uniformMean_equiv (properClauseEquiv n k) (fun s => f s.1.val)
  change uniformMean (fun C : ProperClause n k => f (clauseSupport C)) = _ at he
  rw [he]
  have hc (s : VariableSet n k) : Fintype.card (↥s.val → Bool) = 2^k := by
    simp [(Finset.mem_powersetCard.mp s.property).2]
  simp only [uniformMean, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sigma, hc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  have h2 : (2 : ℝ)^k ≠ 0 := by positivity
  push_cast
  field_simp

theorem uniformProbability_support_subset {n k : ℕ} (T : Finset (Fin n)) :
    uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) =
      (T.card.choose k : ℝ) / n.choose k := by
  have hm := uniformMean_support (k := k) (fun S => if S ⊆ T then (1 : ℝ) else 0)
  have hp : uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) =
      uniformProbability (fun s : VariableSet n k => s.val ⊆ T) := by
    rw [uniformProbability_eq_mean, uniformProbability_eq_mean]
    calc
      _ = uniformMean (fun C : ProperClause n k =>
          if clauseSupport C ⊆ T then (1 : ℝ) else 0) := by
            apply uniformMean_congr
            intro C
            by_cases h : clauseSupport C ⊆ T <;> simp only [h, ite_true, ite_false]
      _ = _ := hm
      _ = _ := by
        apply uniformMean_congr
        intro C
        by_cases h : C.val ⊆ T <;> simp only [h, ite_true, ite_false]
  rw [hp]
  let e : {s : VariableSet n k // s.val ⊆ T} ≃ ↥(T.powersetCard k) := {
    toFun := fun s => ⟨s.val.val, Finset.mem_powersetCard.mpr
      ⟨s.property, (Finset.mem_powersetCard.mp s.val.property).2⟩⟩
    invFun := fun s => ⟨⟨s.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp s.property).2⟩⟩,
        (Finset.mem_powersetCard.mp s.property).1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem choose_quotient_le_pow {b n k : ℕ} (hbn : b ≤ n) (hkn : k ≤ n) (hn : 0 < n) :
    (b.choose k : ℝ) / n.choose k ≤ ((b : ℝ) / n)^k := by
  have h := mul_le_mul_of_nonneg_right (killFraction_le_pow hbn hkn hn)
    (by positivity : (0 : ℝ) ≤ 2^k)
  have h2 : (2 : ℝ)^k ≠ 0 := by positivity
  calc
    _ = killFraction b n k * 2^k := by
      unfold killFraction
      field_simp
    _ ≤ ((b : ℝ) / (2 * n))^k * 2^k := h
    _ = _ := by
      rw [← mul_pow]
      congr 1
      field_simp

theorem clause_subset_bound {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) (T : Finset (Fin n)) :
    uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) ≤
      ((T.card : ℝ) / n)^k := by
  rw [uniformProbability_support_subset]
  exact choose_quotient_le_pow (by simpa using Finset.card_le_univ T) hkn hn

theorem unsatisfiable_container {n k m : ℕ} (hmn : m ≤ n) (F : Formula n k m)
    (hF : ¬Satisfiable F) :
    ∃ t : Fin m, ∃ J : VariableSet m (t.val + 1), ∃ T : VariableSet n (t.val + 1),
      ∀ j ∈ J.val, clauseSupport (F j) ⊆ T.val := by
  obtain ⟨J, hdef⟩ := unsatisfiable_deficiency F hF
  have ht : 0 < J.card := lt_of_le_of_lt (Nat.zero_le _) hdef
  have htm : J.card ≤ m := by simpa using Finset.card_le_univ J
  obtain ⟨T, hUT, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (J.biUnion fun j => clauseSupport (F j))) hdef.le
      (show J.card ≤ (Finset.univ : Finset (Fin n)).card by simpa using htm.trans hmn)
  have hts : J.card - 1 + 1 = J.card := Nat.sub_add_cancel ht
  refine ⟨⟨J.card - 1, by omega⟩,
    ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hts.symm⟩⟩,
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT.trans hts.symm⟩⟩, ?_⟩
  intro j hj i hi
  exact hUT (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)

theorem deficiency_union_bound {n k m : ℕ} (hkn : k ≤ n) (hn : 0 < n) (hmn : m ≤ n) :
    1 - properSATProbability n k m ≤
      ∑ t ∈ Finset.range m, (m.choose (t + 1) : ℝ) * n.choose (t + 1) *
        (((t + 1 : ℕ) : ℝ) / n)^(k * (t + 1)) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  let E (F : Formula n k m) (t : Fin m) (J : VariableSet m (t.val + 1))
      (T : VariableSet n (t.val + 1)) : Prop := ∀ j ∈ J.val, clauseSupport (F j) ⊆ T.val
  have hsat : 1 - properSATProbability n k m =
      uniformProbability (fun F : Formula n k m => ¬Satisfiable F) :=
    (uniformProbability_not (fun F : Formula n k m => Satisfiable F)).symm
  have hE (t : Fin m) (J : VariableSet m (t.val + 1)) (T : VariableSet n (t.val + 1)) :
      uniformProbability (fun F : Formula n k m => E F t J T) ≤
        (((t.val + 1 : ℕ) : ℝ) / n)^(k * (t.val + 1)) := by
    dsimp [E]
    rw [uniformProbability_forall_mem (α := ProperClause n k) (β := Fin m) J.val
      (fun C => clauseSupport C ⊆ T.val)]
    have ht := (Finset.mem_powersetCard.mp T.property).2
    have hj := (Finset.mem_powersetCard.mp J.property).2
    rw [hj]
    have h := pow_le_pow_left₀ (uniformProbability_nonneg _)
      (clause_subset_bound hkn hn T.val) (t.val + 1)
    rwa [ht, ← pow_mul] at h
  rw [hsat]
  calc
    _ ≤ uniformProbability (fun F : Formula n k m => ∃ t, ∃ J, ∃ T, E F t J T) :=
      uniformProbability_mono (fun F hF => unsatisfiable_container hmn F hF)
    _ ≤ ∑ t : Fin m, uniformProbability (fun F : Formula n k m => ∃ J, ∃ T, E F t J T) :=
      uniformProbability_exists_le _
    _ ≤ ∑ t : Fin m, ∑ J : VariableSet m (t.val + 1),
        ∑ T : VariableSet n (t.val + 1),
          uniformProbability (fun F : Formula n k m => E F t J T) := by
      apply Finset.sum_le_sum
      intro t _
      apply (uniformProbability_exists_le _).trans
      apply Finset.sum_le_sum
      intro J _
      exact uniformProbability_exists_le _
    _ ≤ ∑ t : Fin m, ∑ _ : VariableSet m (t.val + 1), ∑ _ : VariableSet n (t.val + 1),
        (((t.val + 1 : ℕ) : ℝ) / n)^(k * (t.val + 1)) := by
      gcongr with t _ J _ T _
      exact hE t J T
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_variableSet, nsmul_eq_mul]
      simp only [← mul_assoc]
      exact Fin.sum_univ_eq_sum_range (fun t => (m.choose (t+1) : ℝ) * n.choose (t+1) *
        (((t+1 : ℕ) : ℝ) / n)^(k*(t+1))) m

theorem choose_exp_bound (N t : ℕ) (ht : 0 < t) :
    (N.choose t : ℝ) ≤ (Real.exp 1 * N / t)^t := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hf0 : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  have he : (t : ℝ)^t / t.factorial ≤ (Real.exp 1)^t := by
    have h := Real.pow_div_factorial_le_exp (x := (t : ℝ)) (Nat.cast_nonneg t) t
    simpa only [← Real.exp_nat_mul, mul_one] using h
  have hinv : (t.factorial : ℝ)⁻¹ ≤ (Real.exp 1 / t)^t := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos ht0 t)).mpr
    simpa only [div_eq_mul_inv, mul_comm] using he
  calc
    (N.choose t : ℝ) ≤ (N : ℝ)^t / t.factorial := Nat.choose_le_pow_div t N
    _ ≤ (N : ℝ)^t * (Real.exp 1 / t)^t := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

def smallDensity : ℝ := Real.exp (-2) / 4

theorem smallDensity_pos : 0 < smallDensity := by unfold smallDensity; positivity

theorem smallDensity_le_one : smallDensity ≤ 1 := by
  unfold smallDensity
  have : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

theorem smallDensity_calibration : Real.exp 1 ^ 2 * smallDensity = 1 / 4 := by
  unfold smallDensity
  rw [← Real.exp_nat_mul]
  norm_num
  rw [← mul_div_assoc, ← Real.exp_add]
  norm_num

theorem hall_summand_bound {n k m t : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (ht : 0 < t)
    (htn : t ≤ n) (hm : (m : ℝ) ≤ smallDensity * n) :
    (m.choose t : ℝ) * n.choose t * ((t : ℝ) / n)^(k * t) ≤
      (1 / n : ℝ) * (1 / 2 : ℝ)^t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hr0 : 0 ≤ (t : ℝ) / n := by positivity
  have hr1 : (t : ℝ) / n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast htn)
  have hc : (m.choose t : ℝ) * n.choose t * ((t : ℝ) / n)^(k * t) ≤
      ((1 / 4 : ℝ) * ((t : ℝ) / n))^t := by
    calc
      _ ≤ (Real.exp 1 * m / t)^t * (Real.exp 1 * n / t)^t *
          ((t : ℝ) / n)^(3 * t) := by
        apply mul_le_mul
        · exact mul_le_mul (choose_exp_bound m t ht) (choose_exp_bound n t ht)
            (Nat.cast_nonneg _) (by positivity)
        · exact pow_le_pow_of_le_one hr0 hr1 (Nat.mul_le_mul_right t hk)
        · positivity
        · positivity
      _ = (Real.exp 1 ^ 2 * (m / n) * ((t : ℝ) / n))^t := by
        rw [pow_mul, ← mul_pow, ← mul_pow]
        congr 1
        field_simp
      _ ≤ (Real.exp 1 ^ 2 * smallDensity * ((t : ℝ) / n))^t := by
        apply pow_le_pow_left₀ (by positivity)
        gcongr
        exact (div_le_iff₀ hn0).mpr hm
      _ = _ := by rw [smallDensity_calibration]
  apply hc.trans
  calc
    ((1 / 4 : ℝ) * ((t : ℝ) / n))^t = (1 / 4 : ℝ)^t * ((t : ℝ) / n)^t := mul_pow _ _ _
    _ ≤ (1 / 4 : ℝ)^t * ((t : ℝ) / n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_one] using pow_le_pow_of_le_one hr0 hr1 ht
    _ ≤ (1 / 4 : ℝ)^t * ((2 : ℝ)^t / n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n := t)).le) hn0.le
    _ = (1 / n : ℝ) * (1 / 2 : ℝ)^t := by
      rw [← mul_div_assoc, ← mul_pow]
      norm_num
      ring

theorem half_geometric_sum_le (m : ℕ) : ∑ t ∈ Finset.range m, (1 / 2 : ℝ)^(t+1) ≤ 1 := by
  have h := geom_sum_mul (1 / 2 : ℝ) m
  have he : ∑ t ∈ Finset.range m, (1 / 2 : ℝ)^(t+1) =
      (∑ t ∈ Finset.range m, (1 / 2 : ℝ)^t) * (1 / 2) := by
    simp_rw [pow_succ]
    rw [Finset.sum_mul]
  rw [he]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m]

theorem small_density_probability_bound {n k m : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n)
    (hm : (m : ℝ) ≤ smallDensity * n) :
    1 - (1 / n : ℝ) ≤ properSATProbability n k m := by
  have hn : 0 < n := by omega
  have hmn : m ≤ n := by
    have h := mul_le_mul_of_nonneg_right smallDensity_le_one (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    exact_mod_cast (show (m : ℝ) ≤ n from hm.trans (by simpa using h))
  have h := deficiency_union_bound hkn hn hmn
  have hs : (∑ t ∈ Finset.range m, (m.choose (t + 1) : ℝ) * n.choose (t + 1) *
      (((t + 1 : ℕ) : ℝ) / n)^(k * (t + 1))) ≤ 1 / n := by
    calc
      _ ≤ ∑ t ∈ Finset.range m, (1 / n : ℝ) * (1 / 2 : ℝ)^(t+1) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hall_summand_bound hk hn (by omega) (by have := Finset.mem_range.mp ht; omega) hm
      _ = (1 / n : ℝ) * ∑ t ∈ Finset.range m, (1 / 2 : ℝ)^(t+1) := (Finset.mul_sum ..).symm
      _ ≤ 1 / n := by
        simpa using mul_le_mul_of_nonneg_left (half_geometric_sum_le m) (by positivity : (0 : ℝ) ≤ 1/n)
  linarith

def lowerCenterBound : ℝ := smallDensity / 4

theorem lowerCenterBound_pos : 0 < lowerCenterBound := div_pos smallDensity_pos (by norm_num)

theorem center_lower_explicit {n k : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n)
    (hn : 2 ≤ n) (hlarge : 2 ≤ smallDensity * n) : lowerCenterBound ≤ center n k := by
  let m : ℕ := ⌊smallDensity * n⌋₊
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : (m : ℝ) ≤ smallDensity * n := Nat.floor_le (by positivity)
  have hmn : m ≤ n := by
    have h := mul_le_mul_of_nonneg_right smallDensity_le_one hn0.le
    exact_mod_cast (show (m : ℝ) ≤ n from hm.trans (by simpa using h))
  have hmcap : m ≤ mainCap n k := hmn.trans (by
    unfold mainCap
    exact Nat.le_mul_of_pos_left _ (by unfold capMultiplier; positivity))
  have hprob := small_density_probability_bound hk hkn hm
  have hinv : (1 / n : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast hn
  have hhalf : (1 / 2 : ℝ) ≤ properSATProbability n k m := by linarith
  have hfloor : smallDensity * n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hratio : smallDensity / 2 ≤ (m : ℝ) / n := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith
  have hl := center_lower_by_probability hkn hmcap
  have hmul := mul_le_mul hratio hhalf (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (div_nonneg (Nat.cast_nonneg m) hn0.le)
  unfold lowerCenterBound
  nlinarith

theorem center_bounds_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop, lowerCenterBound ≤ center n k ∧ center n k ≤ (2 : ℝ)^k + 1 := by
  have hlin : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ smallDensity * n := by
    have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop smallDensity_pos
    exact ht.eventually (Filter.eventually_ge_atTop 2)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one firstMomentBase_nonneg firstMomentBase_lt_one
  have ht : Filter.Tendsto (fun n : ℕ => (capMultiplier k : ℝ) * firstMomentBase^n)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hpow.const_mul (capMultiplier k : ℝ)
  have hu := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hn : ∀ᶠ n : ℕ in Filter.atTop, k + 1 ≤ n := Filter.eventually_ge_atTop _
  filter_upwards [hlin, hu, hn] with n hlarge hu hn
  exact ⟨center_lower_explicit hk (by omega) (by omega) hlarge,
    (center_first_moment (by omega) (by omega)).trans (by linarith)⟩

end


end FixedClauseThreshold

end OAI
