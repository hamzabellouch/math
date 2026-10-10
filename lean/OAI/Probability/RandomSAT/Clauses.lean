import OAI.Probability.RandomSAT.Model

namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def clauseSupport {n k : ℕ} (C : ProperClause n k) : Finset (Fin n) :=
  Finset.univ.filter fun i => (C.val i).isSome

@[simp] theorem clauseSupport_card {n k : ℕ} (C : ProperClause n k) :
    (clauseSupport C).card = k := C.property

@[simp] theorem mem_clauseSupport {n k : ℕ} (C : ProperClause n k) (i : Fin n) :
    i ∈ clauseSupport C ↔ (C.val i).isSome := by
  simp [clauseSupport]

abbrev VariableSet (n k : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard k)

abbrev SignedVariableSet (n k : ℕ) := Σ s : VariableSet n k, ↥s.val → Bool

def clauseFromSigns {n k : ℕ} (s : VariableSet n k) (b : ↥s.val → Bool) :
    ProperClause n k :=
  ⟨fun i => if h : i ∈ s.val then some (b ⟨i, h⟩) else none, by
    have hs : (Finset.univ.filter fun i : Fin n =>
        (if h : i ∈ s.val then some (b ⟨i, h⟩) else none).isSome) = s.val := by
      ext i
      by_cases hi : i ∈ s.val <;> simp [hi]
    rw [hs]
    exact (Finset.mem_powersetCard.mp s.property).2⟩

@[simp] theorem clauseSupport_fromSigns {n k : ℕ} (s : VariableSet n k)
    (b : ↥s.val → Bool) : clauseSupport (clauseFromSigns s b) = s.val := by
  ext i
  by_cases hi : i ∈ s.val <;> simp [clauseSupport, clauseFromSigns, hi]

def clauseToSigns {n k : ℕ} (C : ProperClause n k) : SignedVariableSet n k :=
  ⟨⟨clauseSupport C, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, clauseSupport_card C⟩⟩,
    fun i => (C.val i.val).getD false⟩

def properClauseEquiv (n k : ℕ) : ProperClause n k ≃ SignedVariableSet n k where
  toFun := clauseToSigns
  invFun := fun t => clauseFromSigns t.1 t.2
  left_inv C := by
    apply Subtype.ext
    funext i
    dsimp [clauseToSigns, clauseFromSigns]
    by_cases hi : i ∈ clauseSupport C
    · rw [ite_eq_left hi]
      exact Option.getD_of_ne_none (Option.isSome_iff_ne_none.mp
        ((mem_clauseSupport C i).mp hi)) false
    · rw [ite_eq_right hi]
      exact ((Option.not_isSome_iff_eq_none).mp (by simpa using hi)).symm
  right_inv t := by
    rcases t with ⟨s, b⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact clauseSupport_fromSigns s b
    · apply Function.hfunext (by
        change ↥(clauseSupport (clauseFromSigns s b)) = ↥s.val
        rw [clauseSupport_fromSigns])
      intro i j hij
      apply heq_of_eq
      have hv : i.val = j.val := by
        exact (Subtype.heq_iff_coe_eq (fun x => by
          change x ∈ clauseSupport (clauseFromSigns s b) ↔ x ∈ s.val
          rw [clauseSupport_fromSigns])).mp hij
      simp [clauseToSigns, clauseFromSigns, hv, j.property]

@[simp] theorem card_variableSet (n k : ℕ) :
    Fintype.card (VariableSet n k) = n.choose k := by
  simp [VariableSet]

@[simp] theorem card_properClause (n k : ℕ) :
    Fintype.card (ProperClause n k) = n.choose k * 2 ^ k := by
  rw [Fintype.card_congr (properClauseEquiv n k), Fintype.card_sigma]
  have hc (s : VariableSet n k) : Fintype.card (↥s.val → Bool) = 2 ^ k := by
    simp [(Finset.mem_powersetCard.mp s.property).2]
  simp_rw [hc]
  simp

@[simp] theorem card_formula (n k m : ℕ) :
    Fintype.card (Formula n k m) = (n.choose k * 2 ^ k) ^ m := by
  simp [Formula]

theorem nonempty_properClause {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (ProperClause n k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_properClause]
  exact Nat.mul_pos (Nat.choose_pos hkn) (by positivity)

theorem satisfiable_empty (n k : ℕ) (F : Formula n k 0) : Satisfiable F := by
  exact ⟨fun _ => false, fun i => Fin.elim0 i⟩

@[simp] theorem properSATProbability_zero (n k : ℕ) : properSATProbability n k 0 = 1 := by
  classical
  simp [properSATProbability, Fintype.card_subtype, satisfiable_empty]

theorem properSATProbability_nonneg (n k m : ℕ) :
    0 ≤ properSATProbability n k m := by
  unfold properSATProbability
  positivity

theorem properSATProbability_le_one (n k m : ℕ) :
    properSATProbability n k m ≤ 1 := by
  classical
  unfold properSATProbability
  by_cases h : Fintype.card (Formula n k m) = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast Fintype.card_subtype_le (fun F : Formula n k m => Satisfiable F)

def frozenCoordinates {n : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ σ ∈ S, σ i = σ₀ i

def KillsSolutions {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) : Prop :=
  ∀ σ ∈ S, ¬ SatisfiesClause σ C

theorem kills_iff {n k : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n)
    (hσ₀ : σ₀ ∈ S) (C : ProperClause n k) :
    KillsSolutions S C ↔
      clauseSupport C ⊆ frozenCoordinates S σ₀ ∧
      ∀ i ∈ clauseSupport C, C.val i = some (!(σ₀ i)) := by
  constructor
  · intro h
    have hop (σ : Assignment n) (hσ : σ ∈ S) (i : Fin n)
        (hi : i ∈ clauseSupport C) : C.val i = some (!(σ i)) := by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((mem_clauseSupport C i).mp hi)
      have hne : b ≠ σ i := by
        intro heq
        exact h σ hσ ⟨i, hb.trans (congrArg some heq)⟩
      cases hb' : b <;> cases hv : σ i <;> simp_all
    refine ⟨?_, hop σ₀ hσ₀⟩
    intro i hi
    simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    intro σ hσ
    have heq := (hop σ hσ i hi).symm.trans (hop σ₀ hσ₀ i hi)
    simpa using heq
  · rintro ⟨hsub, hsign⟩ σ hσ ⟨i, hi⟩
    have his : i ∈ clauseSupport C := by
      rw [mem_clauseSupport, hi]
      rfl
    have hf : σ i = σ₀ i := by
      have hf := hsub his
      simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact hf σ hσ
    have heq := hi.symm.trans (hsign i his)
    cases hv : σ₀ i <;> simp_all

def forcedVariables {n : ℕ} (S : Finset (Assignment n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => S.Nonempty ∧ ∃ b : Bool, ∀ σ ∈ S, σ i = b

@[simp] theorem forcedVariables_empty (n : ℕ) :
    forcedVariables (∅ : Finset (Assignment n)) = ∅ := by
  simp [forcedVariables]

theorem forcedVariables_eq_frozen {n : ℕ} {S : Finset (Assignment n)}
    {σ₀ : Assignment n} (hσ₀ : σ₀ ∈ S) :
    forcedVariables S = frozenCoordinates S σ₀ := by
  ext i
  simp only [forcedVariables, frozenCoordinates, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, b, hb⟩ σ hσ
    exact (hb σ hσ).trans (hb σ₀ hσ₀).symm
  · intro h
    exact ⟨⟨σ₀, hσ₀⟩, σ₀ i, h⟩

def opposingClause {n k : ℕ} (σ : Assignment n) (s : VariableSet n k) :
    ProperClause n k := clauseFromSigns s (fun i => !(σ i.val))

@[simp] theorem support_opposingClause {n k : ℕ} (σ : Assignment n)
    (s : VariableSet n k) : clauseSupport (opposingClause σ s) = s.val :=
  clauseSupport_fromSigns _ _

def killingClauseEquiv {n k : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n)
    (hσ₀ : σ₀ ∈ S) :
    {C : ProperClause n k // KillsSolutions S C} ≃
      ↥((frozenCoordinates S σ₀).powersetCard k) where
  toFun C := ⟨clauseSupport C.val, Finset.mem_powersetCard.mpr
    ⟨((kills_iff S σ₀ hσ₀ C.val).mp C.property).1, clauseSupport_card C.val⟩⟩
  invFun s := ⟨opposingClause σ₀ ⟨s.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp s.property).2⟩⟩, by
    apply (kills_iff S σ₀ hσ₀ _).mpr
    simp only [support_opposingClause]
    refine ⟨(Finset.mem_powersetCard.mp s.property).1, ?_⟩
    intro i hi
    simp [opposingClause, clauseFromSigns, hi]⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (if i ∈ clauseSupport C.val then some (!(σ₀ i)) else none) = C.val.val i
    by_cases hi : i ∈ clauseSupport C.val
    · rw [ite_eq_left hi]
      exact (((kills_iff S σ₀ hσ₀ C.val).mp C.property).2 i hi).symm
    · rw [ite_eq_right hi]
      apply Eq.symm
      apply Option.not_isSome_iff_eq_none.mp
      simpa only [mem_clauseSupport] using hi
  right_inv s := by
    apply Subtype.ext
    exact support_opposingClause _ _

theorem card_killingClauses {n k : ℕ} (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    Fintype.card {C : ProperClause n k // KillsSolutions S C} =
      (forcedVariables S).card.choose k := by
  obtain ⟨σ₀, hσ₀⟩ := hS
  rw [Fintype.card_congr (killingClauseEquiv S σ₀ hσ₀),
    Fintype.card_coe, Finset.card_powersetCard, forcedVariables_eq_frozen hσ₀]

noncomputable def uniformProbability {α : Type*} [Fintype α] (p : α → Prop) : ℝ := by
  classical
  exact (Fintype.card {a : α // p a} : ℝ) / Fintype.card α

theorem uniformProbability_nonneg {α : Type*} [Fintype α] (p : α → Prop) :
    0 ≤ uniformProbability p := by
  unfold uniformProbability
  positivity

theorem uniformProbability_le_one {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p ≤ 1 := by
  classical
  unfold uniformProbability
  by_cases h : Fintype.card α = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast Fintype.card_subtype_le p

theorem uniformProbability_mono {α : Type*} [Fintype α] {p q : α → Prop}
    (hpq : ∀ a, p a → q a) : uniformProbability p ≤ uniformProbability q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective
    (fun a : {a // p a} => (⟨a.val, hpq a.val a.property⟩ : {a // q a}))
    (fun _ _ h => Subtype.ext (congrArg (fun t : {a // q a} => t.val) h))

noncomputable def killingProbability {n : ℕ} (k : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformProbability (fun C : ProperClause n k => S.Nonempty ∧ KillsSolutions S C)

theorem killingProbability_of_nonempty {n k : ℕ} (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    killingProbability k S = ((forcedVariables S).card.choose k : ℝ) /
      ((n.choose k : ℝ) * 2 ^ k) := by
  classical
  unfold killingProbability uniformProbability
  simp only [hS, true_and, card_killingClauses S hS, card_properClause,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

@[simp] theorem killingProbability_empty (n k : ℕ) :
    killingProbability k (∅ : Finset (Assignment n)) = 0 := by
  classical
  simp [killingProbability, uniformProbability]

theorem killingProbability_eq {n k : ℕ} (hk : 0 < k) (S : Finset (Assignment n)) :
    killingProbability k S = ((forcedVariables S).card.choose k : ℝ) /
      ((n.choose k : ℝ) * 2 ^ k) := by
  by_cases hS : S.Nonempty
  · exact killingProbability_of_nonempty S hS
  · have h : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [Nat.choose_eq_zero_of_lt hk]

end


end FixedClauseThreshold

end OAI
