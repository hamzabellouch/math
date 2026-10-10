import OAI.Probability.SATVariance.Model

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma support_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = n.choose k := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro s; simp)]
  simp

lemma clause_card (n k : ℕ) : Fintype.card (Clause n k) = n.choose k * 2 ^ k := by
  classical
  change Fintype.card ((s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  trans ∑ _ : {s : Finset (Fin n) // s.card = k}, 2 ^ k
  · apply Finset.sum_congr rfl
    intro s _
    rw [s.property]
  · rw [Finset.sum_const, Finset.card_univ, support_card, smul_eq_mul]

lemma clause_nonempty (n k : ℕ) (hkn : k ≤ n) : Nonempty (Clause n k) := by
  rw [← Fintype.card_pos_iff, clause_card]
  exact Nat.mul_pos (Nat.choose_pos hkn) (pow_pos (by decide) _)

lemma clauseLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (clauseLaw n k) := by
  let := clause_nonempty n k hkn
  unfold clauseLaw
  infer_instance

lemma streamLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (streamLaw n k) := by
  let := clauseLaw_probability n k hkn
  unfold streamLaw
  infer_instance

def frozen {n : ℕ} (S : Finset (Assignment n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∀ a ∈ S, ∀ b ∈ S, a v = b v

def Kills {n k : ℕ} (S : Finset (Assignment n)) (c : Clause n k) : Prop :=
  ∀ a ∈ S, ¬ Satisfies c a

lemma bool_ne_iff (x y : Bool) : x ≠ y ↔ y = !x := by
  cases x <;> cases y <;> decide

lemma kills_iff {n k : ℕ} {S : Finset (Assignment n)} {a₀ : Assignment n}
    (ha₀ : a₀ ∈ S) (c : Clause n k) :
    Kills S c ↔ c.1.1 ⊆ frozen S ∧ ∀ v : c.1.1, c.2 v = !(a₀ v) := by
  classical
  constructor
  · intro h
    have hn : ∀ a ∈ S, ∀ v : c.1.1, a v ≠ c.2 v := by
      intro a ha v he
      exact h a ha ⟨v, he⟩
    refine ⟨?_, fun v => (bool_ne_iff _ _).mp (hn a₀ ha₀ v)⟩
    intro v hv
    simp only [frozen, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha b hb
    have h₁ := (bool_ne_iff _ _).mp (hn a ha ⟨v, hv⟩)
    have h₂ := (bool_ne_iff _ _).mp (hn b hb ⟨v, hv⟩)
    exact Bool.not_injective (h₁.symm.trans h₂)
  · rintro ⟨hs, ht⟩ a ha ⟨v, hv⟩
    have hf := (Finset.mem_filter.mp (hs v.property)).2 a ha a₀ ha₀
    have hne := (bool_ne_iff (a₀ v) (c.2 v)).mpr (ht v)
    exact hne (hf.symm.trans hv)

def killingEquiv {n k : ℕ} {S : Finset (Assignment n)} {a₀ : Assignment n}
    (ha₀ : a₀ ∈ S) :
    {c : Clause n k // Kills S c} ≃
      {s : Finset (Fin n) // s ⊆ frozen S ∧ s.card = k} where
  toFun c := ⟨c.1.1.1, (kills_iff ha₀ c.1).mp c.2 |>.1, c.1.1.2⟩
  invFun s := ⟨⟨⟨s.1, s.2.2⟩, fun v => !(a₀ v)⟩,
    (kills_iff ha₀ _).mpr ⟨s.2.1, fun _ => rfl⟩⟩
  left_inv c := by
    apply Subtype.ext
    rcases c with ⟨⟨s, f⟩, hc⟩
    have hf := (kills_iff ha₀ ⟨s, f⟩).mp hc |>.2
    dsimp
    congr 1
    exact funext fun v => (hf v).symm
  right_inv s := by
    apply Subtype.ext
    rfl

lemma killing_card {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    Fintype.card {c : Clause n k // Kills S c} = (frozen S).card.choose k := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS
  rw [Fintype.card_congr (killingEquiv ha₀)]
  rw [Fintype.card_of_subtype ((frozen S).powersetCard k) (by intro s; simp)]
  exact Finset.card_powersetCard _ _

lemma count_set_fintype.{u_1} {α : Type u_1} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (s : Set α) :
    Measure.count s = (Fintype.card s : ℝ≥0∞) := by
  rw [Measure.count_apply (Set.toFinite s).measurableSet,
    Set.encard_eq_coe_toFinset_card]
  simp

lemma clauseLaw_kills {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    clauseLaw n k {c | Kills S c} =
      ((frozen S).card.choose k : ℝ≥0∞) / ((n.choose k : ℝ≥0∞) * 2 ^ k) := by
  rw [clauseLaw, uniformOn_univ, count_set_fintype]
  have hc : Fintype.card ↑{c : Clause n k | Kills S c} = (frozen S).card.choose k := by
    simpa only [Fintype.card_subtype, Set.mem_ofPred_eq] using (killing_card hS)
  rw [hc, clause_card]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

lemma frozen_singleton {n : ℕ} (a : Assignment n) : frozen {a} = Finset.univ := by
  ext v
  simp [frozen]

lemma clauseLaw_not_satisfies {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) :
    clauseLaw n k {c | ¬ Satisfies c a} = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  have he : {c : Clause n k | ¬ Satisfies c a} = {c | Kills {a} c} := by
    ext c
    simp [Kills]
  rw [he, clauseLaw_kills (Finset.singleton_nonempty a), frozen_singleton,
    Finset.card_univ, Fintype.card_fin]
  have hc : (n.choose k : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc)
    (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
    ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), one_mul]

lemma clauseLaw_satisfies {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) :
    clauseLaw n k {c | Satisfies c a} = 1 - ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  let := clauseLaw_probability n k hkn
  have he : {c : Clause n k | Satisfies c a} = {c | ¬ Satisfies c a}ᶜ := by
    ext c
    simp
  rw [he, measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _),
    measure_univ, clauseLaw_not_satisfies hkn]

end RandomKSAT

end

end OAI
