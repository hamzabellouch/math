import OAI.Probability.RandomSAT.FiniteMean

namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem support_card_cons {v : ℕ} (b : Option Bool) (C : Fin v → Option Bool) :
    (Finset.univ.filter fun i : Fin (v + 1) => (Fin.cons (α := fun _ => Option Bool) b C i).isSome).card =
      (if b.isSome then 1 else 0) + (Finset.univ.filter fun i => (C i).isSome).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp

def prependAbsent {v k : ℕ} (C : ProperClause v k) : ProperClause (v + 1) k :=
  ⟨Fin.cons none C.val, by simpa [support_card_cons] using C.property⟩

def prependPresent {v k : ℕ} (hk : 0 < k) (C : ProperClause v (k - 1)) (b : Bool) :
    ProperClause (v + 1) k :=
  ⟨Fin.cons (some b) C.val, by
    rw [support_card_cons]
    simp only [Option.isSome_some, ↓reduceIte, C.property]
    omega⟩

def clauseHeadSplit {v k : ℕ} (hk : 0 < k) (C : ProperClause (v + 1) k) :
    ProperClause v k ⊕ (ProperClause v (k - 1) × Bool) :=
  match hb : C.val 0 with
  | none => Sum.inl ⟨Fin.tail C.val, by
      have h := C.property
      conv_lhs at h => rw [← Fin.cons_self_tail C.val]
      rw [support_card_cons, hb] at h
      simpa using h⟩
  | some b => Sum.inr (⟨Fin.tail C.val, by
      have h := C.property
      conv_lhs at h => rw [← Fin.cons_self_tail C.val]
      rw [support_card_cons, hb] at h
      simp at h
      omega⟩, b)

def clauseHeadEquiv {v k : ℕ} (hk : 0 < k) :
    ProperClause (v + 1) k ≃ ProperClause v k ⊕ (ProperClause v (k - 1) × Bool) where
  toFun := clauseHeadSplit hk
  invFun := Sum.elim prependAbsent (fun p => prependPresent hk p.1 p.2)
  left_inv C := by
    apply Subtype.ext
    simp only [clauseHeadSplit]
    split <;> simp only [Sum.elim_inl, Sum.elim_inr, prependAbsent, prependPresent]
    all_goals simpa only [*] using Fin.cons_self_tail C.val
  right_inv C := by
    cases C with
    | inl C => rfl
    | inr C =>
      rcases C with ⟨C, b⟩
      rfl

@[simp] theorem satisfiesClause_prependAbsent {v k : ℕ}
    (σ : Assignment v) (b : Bool) (C : ProperClause v k) :
    SatisfiesClause (Fin.cons b σ) (prependAbsent C) ↔ SatisfiesClause σ C := by
  simp [SatisfiesClause, prependAbsent, Fin.exists_fin_succ]

@[simp] theorem satisfiesClause_prependPresent {v k : ℕ} (hk : 0 < k)
    (σ : Assignment v) (b t : Bool) (C : ProperClause v (k - 1)) :
    SatisfiesClause (Fin.cons b σ) (prependPresent hk C t) ↔ t = b ∨ SatisfiesClause σ C := by
  simp [SatisfiesClause, prependPresent, Fin.exists_fin_succ]

def addClause {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    Finset (Assignment n) := S.filter (fun σ => SatisfiesClause σ C)

@[simp] theorem mem_addClause {n k : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (σ : Assignment n) :
    σ ∈ addClause S C ↔ σ ∈ S ∧ SatisfiesClause σ C := by
  simp [addClause]

theorem addClause_comm {n k r : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (D : ProperClause n r) :
    addClause (addClause S C) D = addClause (addClause S D) C := by
  ext σ
  simp only [mem_addClause]
  tauto

def restrictSolutions {n k : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Assignment n)) (F : ι → ProperClause n k) : Finset (Assignment n) :=
  S.filter (fun σ => ∀ i, SatisfiesClause σ (F i))

@[simp] theorem mem_restrictSolutions {n k : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Assignment n)) (F : ι → ProperClause n k) (σ : Assignment n) :
    σ ∈ restrictSolutions S F ↔ σ ∈ S ∧ ∀ i, SatisfiesClause σ (F i) := by
  simp [restrictSolutions]

theorem restrictSolutions_zero {n k : ℕ} (S : Finset (Assignment n))
    (F : Formula n k 0) : restrictSolutions S F = S := by
  ext σ
  simp only [mem_restrictSolutions, Fin.forall_fin_zero, and_true]

theorem restrictSolutions_cons {n k m : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (F : Formula n k m) :
    restrictSolutions S (Fin.cons C F) = restrictSolutions (addClause S C) F := by
  ext σ
  simp only [mem_restrictSolutions, mem_addClause, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ]
  tauto

theorem restrictSolutions_comm {n k r : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Finset (Assignment n)) (F : ι → ProperClause n k) (G : κ → ProperClause n r) :
    restrictSolutions (restrictSolutions S F) G = restrictSolutions (restrictSolutions S G) F := by
  ext σ
  simp only [mem_restrictSolutions]
  tauto

theorem uniformMean_fin_succ {α : Type*} [Fintype α] {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun F : Fin m → α =>
      f (Fin.cons a F))) := by
  calc
    _ = uniformMean (fun p : α × (Fin m → α) => f (Fin.cons p.1 p.2)) :=
      (uniformMean_equiv (Fin.consEquiv (fun _ => α)) f).symm
    _ = _ := uniformMean_prod _

def alive {n : ℕ} (S : Finset (Assignment n)) : ℝ := if S.Nonempty then 1 else 0

theorem alive_nonneg {n : ℕ} (S : Finset (Assignment n)) : 0 ≤ alive S := by
  unfold alive
  split <;> norm_num

theorem alive_le_one {n : ℕ} (S : Finset (Assignment n)) : alive S ≤ 1 := by
  unfold alive
  split <;> norm_num

theorem alive_mono {n : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T) :
    alive S ≤ alive T := by
  unfold alive
  by_cases hS : S.Nonempty
  · have hT := hS.mono hST
    simp [hS, hT]
  · simp only [ite_eq_right hS]
    split <;> norm_num

def clauseAverage {n : ℕ} (k : ℕ) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) : ℝ :=
  uniformMean (fun C : ProperClause n k => f (addClause S C))

def survival {n : ℕ} (k : ℕ) (m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  ((clauseAverage k)^[m] alive) S

@[simp] theorem survival_zero {n k : ℕ} (S : Finset (Assignment n)) :
    survival k 0 S = alive S := rfl

theorem survival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k (m + 1) S = uniformMean (fun C : ProperClause n k =>
      survival k m (addClause S C)) := by
  rw [survival, Function.iterate_succ_apply']
  rfl

theorem survival_eq_mean {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k m S = uniformMean (fun F : Formula n k m => alive (restrictSolutions S F)) := by
  induction m generalizing S with
  | zero =>
    simp only [survival_zero, restrictSolutions_zero]
    exact (uniformMean_const _).symm
  | succ m ih =>
    rw [survival_succ, uniformMean_fin_succ]
    apply uniformMean_congr
    intro C
    rw [ih]
    apply uniformMean_congr
    intro F
    rw [restrictSolutions_cons]

theorem properSATProbability_eq_survival (n k m : ℕ) :
    properSATProbability n k m = survival k m (Finset.univ : Finset (Assignment n)) := by
  rw [survival_eq_mean]
  change uniformProbability (fun F : Formula n k m => Satisfiable F) = _
  rw [uniformProbability_eq_mean]
  apply uniformMean_congr
  intro F
  unfold alive
  congr 1
  simp only [Finset.nonempty_iff_ne_empty]
  apply propext
  rw [← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty, Satisfiable, Satisfies]

theorem survival_nonneg {n k m : ℕ} (S : Finset (Assignment n)) : 0 ≤ survival k m S := by
  rw [survival_eq_mean]
  exact uniformMean_nonneg (fun _ => alive_nonneg _)

theorem survival_le_one {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    survival k m S ≤ 1 := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [survival_eq_mean, ← uniformMean_const (α := Formula n k m) (1 : ℝ)]
  exact uniformMean_mono (fun _ => alive_le_one _)

theorem survival_mono_solutions {n k m : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T) :
    survival k m S ≤ survival k m T := by
  rw [survival_eq_mean, survival_eq_mean]
  apply uniformMean_mono
  intro F
  apply alive_mono
  intro σ hσ
  rw [mem_restrictSolutions] at hσ ⊢
  exact ⟨hST hσ.1, hσ.2⟩

theorem survival_antitone {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    Antitone (fun m => survival k m S) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  apply antitone_nat_of_succ_le
  intro m
  rw [survival_succ, ← uniformMean_const (α := ProperClause n k) (survival k m S)]
  apply uniformMean_mono
  intro C
  exact survival_mono_solutions (Finset.filter_subset _ _)

theorem properSATProbability_antitone {n k : ℕ} (hkn : k ≤ n) :
    Antitone (properSATProbability n k) := by
  intro i j hij
  rw [properSATProbability_eq_survival, properSATProbability_eq_survival]
  exact survival_antitone hkn _ hij

theorem clauseAverage_mono {n k : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S, clauseAverage k f S ≤ clauseAverage k g S := by
  intro S
  exact uniformMean_mono (fun C => hfg (addClause S C))

theorem clauseAverage_sub_const {n k : ℕ} (hkn : k ≤ n)
    (f : Finset (Assignment n) → ℝ) (c : ℝ) (S : Finset (Assignment n)) :
    clauseAverage k (fun T => f T - c) S = clauseAverage k f S - c := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  exact (uniformMean_sub _ _).trans (by rw [uniformMean_const]; rfl)

theorem clauseAverage_commute {n k r : ℕ} :
    Function.Commute (clauseAverage (n := n) k) (clauseAverage r) := by
  intro f
  funext S
  unfold clauseAverage
  rw [uniformMean_comm]
  apply uniformMean_congr
  intro C
  apply uniformMean_congr
  intro D
  rw [addClause_comm]

theorem clauseAverage_iterate_mono {n k m : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S,
    ((clauseAverage k)^[m] f) S ≤ ((clauseAverage k)^[m] g) S := by
  induction m with
  | zero => exact hfg
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact clauseAverage_mono ih

theorem clauseAverage_iterate_sub_const {n k m : ℕ} (hkn : k ≤ n)
    (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    (clauseAverage k)^[m] (fun T => f T - c) =
      (fun S => ((clauseAverage k)^[m] f) S - c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext S
    exact clauseAverage_sub_const hkn _ _ _

theorem survival_shift {n k r m d : ℕ} (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] (survival r d)) S =
      ((clauseAverage r)^[d] (survival k m)) S := by
  exact congrArg (fun f => f S) ((clauseAverage_commute (n := n) (k := k) (r := r)).iterate_iterate m d alive)

theorem survival_add {n k m d : ℕ} (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] (survival k d)) S = survival k (m + d) S := by
  exact congrArg (fun f => f S) (Function.iterate_add_apply (clauseAverage k) m d alive).symm

theorem survival_eq_probability {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k m S = uniformProbability (fun F : Formula n k m =>
      ∃ σ ∈ S, Satisfies σ F) := by
  rw [survival_eq_mean, uniformProbability_eq_mean]
  apply uniformMean_congr
  intro F
  unfold alive
  congr 1
  apply propext
  simp [Finset.Nonempty, Satisfies]

theorem blockUNSAT_eq {n k g : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    blockUNSATProbability k g S = 1 - survival k g S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [survival_eq_probability]
  exact uniformProbability_not _

theorem kills_iff_addClause {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    KillsSolutions S C ↔ ¬ (addClause S C).Nonempty := by
  change (∀ σ ∈ S, ¬ SatisfiesClause σ C) ↔ ¬ ∃ σ, σ ∈ addClause S C
  simp only [mem_addClause, not_exists, not_and]

theorem singleUNSAT_eq {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    uniformProbability (fun C : ProperClause n k => KillsSolutions S C) =
      1 - survival k 1 S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [uniformProbability_eq_mean, survival_succ]
  simp only [survival_zero]
  calc
    _ = uniformMean (fun C : ProperClause n k => 1 - alive (addClause S C)) := by
      apply uniformMean_congr
      intro C
      rw [kills_iff_addClause]
      unfold alive
      by_cases h : (addClause S C).Nonempty <;> simp [h]
    _ = _ := by rw [uniformMean_sub, uniformMean_const]

theorem shorter_survival_replacement {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    survival k (replacementBlock n k) S - replacementError n k ≤ survival (k - 1) 1 S := by
  have h := shorter_clause_replacement hk hn S
  rw [singleUNSAT_eq (by omega), blockUNSAT_eq (by omega)] at h
  linarith

theorem shorter_survival_replacement_many {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (d : ℕ) (S : Finset (Assignment (n - 1))) :
    survival k (replacementBlock n k * d) S - (d : ℝ) * replacementError n k ≤
      survival (k - 1) d S := by
  induction d generalizing S with
  | zero => simp
  | succ d ih =>
    let g := replacementBlock n k
    let ε := replacementError n k
    have hkn : k ≤ n - 1 := by omega
    have hshort : k - 1 ≤ n - 1 := by omega
    have ha := clauseAverage_mono (k := k - 1) ih S
    have hb := clauseAverage_iterate_mono (k := k) (m := g * d)
      (shorter_survival_replacement hk hn) S
    rw [clauseAverage_sub_const hshort] at ha
    rw [clauseAverage_iterate_sub_const hkn] at hb
    dsimp only at hb
    rw [survival_add] at hb
    have hcomm : clauseAverage (k - 1) (survival k (g * d)) S =
        ((clauseAverage k)^[g * d] (survival (k - 1) 1)) S := by
      exact survival_shift (m := 1) (d := g * d) S
    rw [← hcomm] at hb
    change _ ≤ survival (k - 1) (d + 1) S
    rw [survival_succ]
    have heq : g * (d + 1) = g * d + g := by ring
    rw [show replacementBlock n k * (d + 1) = g * d + g from heq]
    push_cast
    change survival k (g * d + g) S - ((d : ℝ) + 1) * ε ≤ _
    change _ - (d : ℝ) * ε ≤ _ at ha
    change survival k (g * d + g) S - ε ≤ _ at hb
    dsimp only [g, clauseAverage] at ha hb ⊢
    linarith

theorem uniformMean_sum_type {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α ⊕ β → ℝ) :
    uniformMean f =
      ((Fintype.card α : ℝ) / (Fintype.card α + Fintype.card β)) *
        uniformMean (fun a => f (Sum.inl a)) +
      ((Fintype.card β : ℝ) / (Fintype.card α + Fintype.card β)) *
        uniformMean (fun b => f (Sum.inr b)) := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniformMean, Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add]
  field_simp

theorem head_incidence_ratio {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v) :
    ((v.choose (k - 1) * 2 ^ (k - 1) * 2 : ℕ) : ℝ) /
      ((v.choose k * 2 ^ k + v.choose (k - 1) * 2 ^ (k - 1) * 2 : ℕ) : ℝ) =
      (k : ℝ) / (v + 1) := by
  have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hch : v.choose k + v.choose (k - 1) = (v + 1).choose k := by
    simpa only [Nat.succ_eq_add_one, hks, add_comm] using (Nat.choose_succ_succ v (k - 1)).symm
  have hmult : ((v : ℝ) + 1) * (v.choose (k - 1) : ℝ) =
      ((v + 1).choose k : ℝ) * (k : ℝ) := by
    exact_mod_cast (by simpa only [hks] using Nat.add_one_mul_choose_eq v (k - 1))
  have hpow : (2 : ℝ) ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, hks]
  have hcpos : (0 : ℝ) < (v + 1).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ v + 1)
  have hvpos : (0 : ℝ) < (v : ℝ) + 1 := by positivity
  push_cast
  simp only [mul_assoc, hpow]
  rw [← add_mul]
  have hc : (v.choose k : ℝ) + v.choose (k - 1) = (v + 1).choose k := by
    exact_mod_cast hch
  rw [hc]
  apply (div_eq_div_iff (by positivity) hvpos.ne').mpr
  nlinarith [congrArg (fun z : ℝ => z * 2 ^ k) hmult]

theorem clauseHead_mean {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (f : (ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)) → ℝ) :
    uniformMean (fun C : ProperClause (v + 1) k => f (clauseHeadSplit hk C)) =
      (1 - (k : ℝ) / (v + 1)) * uniformMean (fun C => f (Sum.inl C)) +
      ((k : ℝ) / (v + 1)) *
        uniformMean (fun Q => uniformMean (fun b : Bool => f (Sum.inr (Q, b)))) := by
  let : Nonempty (ProperClause v k) := nonempty_properClause hkv
  let : Nonempty (ProperClause v (k - 1)) := nonempty_properClause (by omega)
  change uniformMean (fun C => f (clauseHeadEquiv hk C)) = _
  rw [uniformMean_equiv, uniformMean_sum_type, uniformMean_prod]
  have hr := head_incidence_ratio hk hkv
  have ht : (0 : ℝ) < Fintype.card (ProperClause v k) +
      Fintype.card (ProperClause v (k - 1) × Bool) := by
    exact add_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hr' : (Fintype.card (ProperClause v (k - 1) × Bool) : ℝ) /
      (Fintype.card (ProperClause v k) + Fintype.card (ProperClause v (k - 1) × Bool)) =
      (k : ℝ) / (v + 1) := by
    simpa only [Fintype.card_prod, Fintype.card_bool, card_properClause, Nat.cast_add] using hr
  rw [hr', ← hr']
  congr 1
  apply congrArg (fun x : ℝ => x * uniformMean (fun C => f (Sum.inl C)))
  field_simp
  ring

end


end FixedClauseThreshold

end OAI
