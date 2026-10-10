import OAI.Probability.RandomSAT.CenterBounds

namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev AuxiliaryClause (n k : ℕ) := Fin k → (Fin n × Bool)

def auxiliarySatisfies {n k : ℕ} (σ : Assignment n) (C : AuxiliaryClause n k) : Prop :=
  ∃ j, σ (C j).1 = (C j).2

def finiteClauseAverage {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) : ℝ := uniformMean (fun c => f (S.filter (sat c)))

theorem finiteClauseAverage_mono {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S, finiteClauseAverage sat f S ≤ finiteClauseAverage sat g S := by
  intro S
  exact uniformMean_mono (fun c => hfg _)

theorem finiteClauseAverage_add {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f g : Finset (Assignment n) → ℝ) :
    finiteClauseAverage sat (fun S => f S + g S) =
      (fun S => finiteClauseAverage sat f S + finiteClauseAverage sat g S) := by
  funext S
  exact uniformMean_add _ _

theorem finiteClauseAverage_const_mul {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    finiteClauseAverage sat (fun S => c * f S) = (fun S => c * finiteClauseAverage sat f S) := by
  funext S
  exact uniformMean_const_mul _ _

theorem finiteClauseAverage_mul_const {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    finiteClauseAverage sat (fun S => f S * c) = (fun S => finiteClauseAverage sat f S * c) := by
  funext S
  exact uniformMean_mul_const _ _

theorem finiteClauseAverage_commute {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop) :
    Function.Commute (finiteClauseAverage satC) (finiteClauseAverage satD) := by
  intro f
  funext S
  unfold finiteClauseAverage
  rw [uniformMean_comm]
  apply uniformMean_congr
  intro d
  apply uniformMean_congr
  intro c
  congr 1
  ext σ
  simp only [Finset.mem_filter]
  tauto

theorem finiteClauseAverage_binomialMean {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (p : ℝ) (m : ℕ)
    (f : ℕ → Finset (Assignment n) → ℝ) :
    finiteClauseAverage sat (fun S => binomialMean p m (fun j => f j S)) =
      (fun S => binomialMean p m (fun j => finiteClauseAverage sat (f j) S)) := by
  funext S
  exact uniformMean_binomialMean _ _ _

theorem iterate_compare_of_commute {X : Type*}
    (A B : (X → ℝ) → (X → ℝ)) (hA : Monotone A) (hB : Monotone B)
    (hcomm : Function.Commute A B) {f : X → ℝ} (hf : B f ≤ A f) (m : ℕ) :
    B^[m] f ≤ A^[m] f := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      B (B^[m] f) ≤ B (A^[m] f) := hB ih
      _ = A^[m] (B f) := (hcomm.symm.iterate_right m f)
      _ ≤ A^[m] (A f) := hA.iterate m hf
      _ = A (A^[m] f) := (Function.iterate_succ_apply A m f).symm.trans
        (Function.iterate_succ_apply' A m f)

def mixedAverage {X : Type*} (p : ℝ) (A B : (X → ℝ) → (X → ℝ))
    (f : X → ℝ) : X → ℝ := fun S => (1 - p) * B f S + p * A f S

theorem mixedAverage_mono {X : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A B : (X → ℝ) → (X → ℝ)} (hA : Monotone A) (hB : Monotone B) :
    Monotone (mixedAverage p A B) := by
  intro f g hfg S
  exact add_le_add (mul_le_mul_of_nonneg_left (hB hfg S) (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left (hA hfg S) hp0)

theorem finiteClauseAverage_commute_mix {n : ℕ} {C D E : Type*}
    [Fintype C] [Fintype D] [Fintype E] (satC : C → Assignment n → Prop)
    (satD : D → Assignment n → Prop) (satE : E → Assignment n → Prop) (p : ℝ) :
    Function.Commute (finiteClauseAverage satC)
      (mixedAverage p (finiteClauseAverage satD) (finiteClauseAverage satE)) := by
  intro f
  unfold mixedAverage
  rw [finiteClauseAverage_add, finiteClauseAverage_const_mul, finiteClauseAverage_const_mul,
    finiteClauseAverage_commute satC satD f, finiteClauseAverage_commute satC satE f]

def embedAuxiliaryClause {n v k : ℕ} (e : Fin v → Fin n) (C : AuxiliaryClause v k) :
    AuxiliaryClause n k := fun j => (e (C j).1, (C j).2)

def embeddedAverage {n v : ℕ} (e : Fin v → Fin n) (k : ℕ) :
    (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
  finiteClauseAverage (fun C : AuxiliaryClause v k => fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C))

def auxiliaryAverage {n : ℕ} (k : ℕ) :
    (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
  embeddedAverage (id : Fin n → Fin n) k

def auxiliarySurvival {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  ((auxiliaryAverage k)^[m] alive) S

def auxiliaryProbability (n k m : ℕ) : ℝ :=
  auxiliarySurvival k m (Finset.univ : Finset (Assignment n))

def embeddedForced {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n) : Finset (Fin v) :=
  Finset.univ.filter (fun i => e i ∈ forcedVariables S)

@[simp] theorem mem_embeddedForced {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n) (i : Fin v) :
    i ∈ embeddedForced S e ↔ e i ∈ forcedVariables S := by simp [embeddedForced]

@[simp] theorem embeddedForced_id {n : ℕ} (S : Finset (Assignment n)) :
    embeddedForced S (id : Fin n → Fin n) = forcedVariables S := by ext i; simp

theorem opposing_literal_iff {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n)
    (σ₀ : Assignment n) (hσ₀ : σ₀ ∈ S) (l : Fin v × Bool) :
    (∀ σ ∈ S, σ (e l.1) ≠ l.2) ↔
      l.1 ∈ embeddedForced S e ∧ l.2 = !(σ₀ (e l.1)) := by
  rw [mem_embeddedForced, forcedVariables_eq_frozen hσ₀]
  simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have h0 := h σ₀ hσ₀
    constructor
    · intro σ hσ
      have hs := h σ hσ
      cases h1 : σ (e l.1) <;> cases h2 : σ₀ (e l.1) <;> cases h3 : l.2 <;> simp_all
    · cases h2 : σ₀ (e l.1) <;> cases h3 : l.2 <;> simp_all
  · rintro ⟨h, hb⟩ σ hσ
    rw [h σ hσ, hb]
    cases σ₀ (e l.1) <;> decide

theorem opposing_literal_probability {n v : ℕ} (S : Finset (Assignment n))
    (e : Fin v → Fin n) (hS : S.Nonempty) :
    uniformProbability (fun l : Fin v × Bool => ∀ σ ∈ S, σ (e l.1) ≠ l.2) =
      ((embeddedForced S e).card : ℝ) / (2 * v) := by
  obtain ⟨σ₀, hσ₀⟩ := hS
  let eqv : {l : Fin v × Bool // ∀ σ ∈ S, σ (e l.1) ≠ l.2} ≃ ↥(embeddedForced S e) := {
    toFun := fun l => ⟨l.val.1, ((opposing_literal_iff S e σ₀ hσ₀ l.val).mp l.property).1⟩
    invFun := fun i => ⟨(i.val, !(σ₀ (e i.val))),
      (opposing_literal_iff S e σ₀ hσ₀ _).mpr ⟨i.property, rfl⟩⟩
    left_inv := fun l => by
      apply Subtype.ext
      change (l.val.1, !(σ₀ (e l.val.1))) = l.val
      apply Prod.ext
      · rfl
      · exact ((opposing_literal_iff S e σ₀ hσ₀ l.val).mp l.property).2.symm
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr eqv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_comm (v : ℝ) 2]

theorem embedded_kill_probability {n v k : ℕ} (S : Finset (Assignment n))
    (e : Fin v → Fin n) (hS : S.Nonempty) :
    uniformProbability (fun C : AuxiliaryClause v k =>
      ¬ (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty) =
      (((embeddedForced S e).card : ℝ) / (2 * v))^k := by
  calc
    _ = uniformProbability (fun C : AuxiliaryClause v k =>
        ∀ j, ∀ σ ∈ S, σ (e (C j).1) ≠ (C j).2) := by
      apply uniformProbability_congr
      intro C
      constructor
      · intro h j σ hσ heq
        apply h
        exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, ⟨j, heq⟩⟩⟩
      · intro h ⟨σ, hσ⟩
        obtain ⟨hσ, j, hj⟩ := Finset.mem_filter.mp hσ
        exact h j σ hσ hj
    _ = _ := by
      change (uniformProbability (fun C : Fin k → Fin v × Bool =>
        ∀ j, (fun l : Fin v × Bool => ∀ σ ∈ S, σ (e l.1) ≠ l.2) (C j))) = _
      have hf := uniformProbability_forall_fintype (α := Fin v × Bool) (β := Fin k)
        (fun l => ∀ σ ∈ S, σ (e l.1) ≠ l.2)
      simpa only [Fintype.card_fin, opposing_literal_probability S e hS] using hf

theorem embeddedAverage_alive {n v k : ℕ} (hv : 0 < v) (e : Fin v → Fin n)
    (S : Finset (Assignment n)) :
    embeddedAverage e k alive S = alive S *
      (1 - (((embeddedForced S e).card : ℝ) / (2 * v))^k) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  by_cases hS : S.Nonempty
  · have ha : alive S = 1 := by simp [alive, hS]
    rw [ha, one_mul]
    have h := uniformProbability_not (fun C : AuxiliaryClause v k =>
      (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty)
    rw [embedded_kill_probability S e hS] at h
    have he : embeddedAverage e k alive S = uniformProbability (fun C : AuxiliaryClause v k =>
        (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty) := by
      rw [uniformProbability_eq_mean]
      unfold embeddedAverage finiteClauseAverage
      apply uniformMean_congr
      intro C
      by_cases hC : (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty
      · simp only [alive, ite_eq_left hC]
      · simp only [alive, ite_eq_right hC]
    rw [he]
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [embeddedAverage, finiteClauseAverage, alive_empty, uniformMean_zero]

theorem auxiliaryAverage_alive {n k : ℕ} (hn : 0 < n) (S : Finset (Assignment n)) :
    auxiliaryAverage k alive S = alive S * (1 - (forcedFraction S / 2)^k) := by
  rw [auxiliaryAverage, embeddedAverage_alive hn, embeddedForced_id]
  congr 2
  unfold forcedFraction
  ring

theorem forced_card_partition {r s : ℕ} (S : Finset (Assignment (r + s))) :
    (forcedVariables S).card = (embeddedForced S (Fin.castAdd s)).card +
      (embeddedForced S (Fin.natAdd r)).card := by
  have h := Fin.sum_univ_add (fun i : Fin (r + s) =>
    if i ∈ forcedVariables S then (1 : ℕ) else 0)
  simpa only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_mem_eq_inter, Finset.univ_inter, embeddedForced] using h

theorem partition_kill_convex {r s k : ℕ} (hr : 0 < r) (hs : 0 < s)
    (S : Finset (Assignment (r + s))) :
    (forcedFraction S / 2)^k ≤
      ((r : ℝ) / (r + s)) * (((embeddedForced S (Fin.castAdd s)).card : ℝ) / (2 * r))^k +
      ((s : ℝ) / (r + s)) * (((embeddedForced S (Fin.natAdd r)).card : ℝ) / (2 * s))^k := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum : (r : ℝ) / (r + s) + (s : ℝ) / (r + s) = 1 := by field_simp
  have h := (convexOn_pow (𝕜 := ℝ) k).2
    (show ((embeddedForced S (Fin.castAdd s)).card : ℝ) / (2 * r) ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; positivity)
    (show ((embeddedForced S (Fin.natAdd r)).card : ℝ) / (2 * s) ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; positivity)
    (show 0 ≤ (r : ℝ) / (r + s) by positivity)
    (show 0 ≤ (s : ℝ) / (r + s) by positivity) hsum
  simp only [smul_eq_mul] at h
  convert h using 1
  congr 1
  unfold forcedFraction
  rw [forced_card_partition, Nat.cast_add, Nat.cast_add]
  field_simp

theorem globalAverage_ge_local {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) :
    mixedAverage ((r : ℝ) / (r + s)) (embeddedAverage (Fin.castAdd s) k)
      (embeddedAverage (Fin.natAdd r) k) alive ≤ auxiliaryAverage k alive := by
  intro S
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hw : 1 - (r : ℝ) / (r + s) = (s : ℝ) / (r + s) := by field_simp; ring
  unfold mixedAverage
  rw [embeddedAverage_alive hr, embeddedAverage_alive hs, auxiliaryAverage_alive (by omega), hw]
  have h := mul_le_mul_of_nonneg_left (partition_kill_convex (k := k) hr hs S) (alive_nonneg S)
  have hsum : (r : ℝ) / (r + s) + (s : ℝ) / (r + s) = 1 := by field_simp
  have hsum_mul := congrArg (fun x : ℝ => alive S * x) hsum
  nlinarith

theorem mixed_finiteAverage_iterate {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop)
    (p : ℝ) (m : ℕ) (f : Finset (Assignment n) → ℝ) :
    (mixedAverage p (finiteClauseAverage satC) (finiteClauseAverage satD))^[m] f =
      (fun S => binomialMean p m (fun j =>
        ((finiteClauseAverage satC)^[j] ((finiteClauseAverage satD)^[m - j] f)) S)) := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold mixedAverage
    rw [finiteClauseAverage_binomialMean, finiteClauseAverage_binomialMean]
    funext S
    rw [binomialMean]
    congr 1
    · congr 1
      apply binomialMean_congr
      intro j hj
      rw [(finiteClauseAverage_commute satD satC).iterate_right j,
        ← Function.iterate_succ_apply' (finiteClauseAverage satD) (m - j) f]
      rw [show (m - j).succ = m.succ - j by omega]
    · congr 1
      apply binomialMean_congr
      intro j hj
      rw [← Function.iterate_succ_apply' (finiteClauseAverage satC) j]
      simp only [Nat.add_sub_add_right]

def blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    Finset (Assignment (r + s)) :=
  Finset.univ.filter (fun σ => (fun i => σ (Fin.castAdd s i)) ∈ S ∧
    (fun i => σ (Fin.natAdd r i)) ∈ T)

@[simp] theorem mem_blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s))
    (σ : Assignment (r + s)) : σ ∈ blockSet S T ↔
      (fun i => σ (Fin.castAdd s i)) ∈ S ∧ (fun i => σ (Fin.natAdd r i)) ∈ T := by
  simp [blockSet]

@[simp] theorem blockSet_univ (r s : ℕ) :
    blockSet (Finset.univ : Finset (Assignment r)) (Finset.univ : Finset (Assignment s)) =
      Finset.univ := by ext σ; simp

theorem blockSet_nonempty {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    (blockSet S T).Nonempty ↔ S.Nonempty ∧ T.Nonempty := by
  constructor
  · rintro ⟨σ, hσ⟩
    have h := (mem_blockSet S T σ).mp hσ
    exact ⟨⟨_, h.1⟩, ⟨_, h.2⟩⟩
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    refine ⟨Fin.addCases σ τ, ?_⟩
    simpa only [mem_blockSet, Fin.addCases_left, Fin.addCases_right] using And.intro hσ hτ

theorem alive_blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    alive (blockSet S T) = alive S * alive T := by
  simp only [alive, blockSet_nonempty]
  split_ifs <;> simp_all

theorem filter_blockSet_left {r s k : ℕ} (S : Finset (Assignment r))
    (T : Finset (Assignment s)) (C : AuxiliaryClause r k) :
    (blockSet S T).filter (fun σ => auxiliarySatisfies σ (embedAuxiliaryClause (Fin.castAdd s) C)) =
      blockSet (S.filter (fun σ => auxiliarySatisfies σ C)) T := by
  ext σ
  constructor
  · intro h
    obtain ⟨hσ, hC⟩ := Finset.mem_filter.mp h
    obtain ⟨hS, hT⟩ := (mem_blockSet S T σ).mp hσ
    exact (mem_blockSet _ _ σ).mpr ⟨Finset.mem_filter.mpr ⟨hS, hC⟩, hT⟩
  · intro h
    obtain ⟨hS, hT⟩ := (mem_blockSet _ _ σ).mp h
    obtain ⟨hS, hC⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨(mem_blockSet S T σ).mpr ⟨hS, hT⟩, hC⟩

theorem filter_blockSet_right {r s k : ℕ} (S : Finset (Assignment r))
    (T : Finset (Assignment s)) (C : AuxiliaryClause s k) :
    (blockSet S T).filter (fun σ => auxiliarySatisfies σ (embedAuxiliaryClause (Fin.natAdd r) C)) =
      blockSet S (T.filter (fun σ => auxiliarySatisfies σ C)) := by
  ext σ
  constructor
  · intro h
    obtain ⟨hσ, hC⟩ := Finset.mem_filter.mp h
    obtain ⟨hS, hT⟩ := (mem_blockSet S T σ).mp hσ
    exact (mem_blockSet _ _ σ).mpr ⟨hS, Finset.mem_filter.mpr ⟨hT, hC⟩⟩
  · intro h
    obtain ⟨hS, hT⟩ := (mem_blockSet _ _ σ).mp h
    obtain ⟨hT, hC⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨(mem_blockSet S T σ).mpr ⟨hS, hT⟩, hC⟩

theorem auxiliarySurvival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    auxiliarySurvival k (m + 1) S = uniformMean (fun C : AuxiliaryClause n k =>
      auxiliarySurvival k m (S.filter (fun σ => auxiliarySatisfies σ C))) := by
  unfold auxiliarySurvival
  rw [Function.iterate_succ_apply']
  rfl

theorem local_iterates_block {r s k : ℕ} (j l : ℕ) (S : Finset (Assignment r))
    (T : Finset (Assignment s)) :
    ((embeddedAverage (Fin.castAdd s) k)^[j]
      ((embeddedAverage (Fin.natAdd r) k)^[l] alive)) (blockSet S T) =
      auxiliarySurvival k j S * auxiliarySurvival k l T := by
  induction j generalizing S T with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    change _ = alive S * auxiliarySurvival k l T
    induction l generalizing T with
    | zero => exact alive_blockSet S T
    | succ l ih =>
      rw [Function.iterate_succ_apply', auxiliarySurvival_succ, ← uniformMean_const_mul]
      unfold embeddedAverage finiteClauseAverage
      apply uniformMean_congr
      intro C
      rw [filter_blockSet_right]
      exact ih _
  | succ j ih =>
    rw [Function.iterate_succ_apply', auxiliarySurvival_succ, ← uniformMean_mul_const]
    unfold embeddedAverage finiteClauseAverage
    apply uniformMean_congr
    intro C
    rw [filter_blockSet_left]
    exact ih _ _

theorem auxiliary_interpolation {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) (m : ℕ) :
    binomialMean ((r : ℝ) / (r + s)) m (fun j =>
      auxiliaryProbability r k j * auxiliaryProbability s k (m - j)) ≤
      auxiliaryProbability (r + s) k m := by
  have hp0 : 0 ≤ (r : ℝ) / (r + s) := by positivity
  have hp1 : (r : ℝ) / (r + s) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < r + s)).mpr
    exact le_add_of_nonneg_right (Nat.cast_nonneg s)
  have h := iterate_compare_of_commute (auxiliaryAverage (n := r + s) k)
    (mixedAverage ((r : ℝ) / (r + s)) (embeddedAverage (Fin.castAdd s) k)
      (embeddedAverage (Fin.natAdd r) k))
    (fun _ _ h => finiteClauseAverage_mono _ h) (mixedAverage_mono hp0 hp1
      (fun _ _ h => finiteClauseAverage_mono _ h) (fun _ _ h => finiteClauseAverage_mono _ h))
    (finiteClauseAverage_commute_mix _ _ _ _) (globalAverage_ge_local hr hs) m Finset.univ
  change _ ≤ auxiliaryProbability (r + s) k m at h
  convert h using 1
  unfold embeddedAverage
  rw [mixed_finiteAverage_iterate]
  apply binomialMean_congr
  intro j hj
  change _ = ((embeddedAverage (Fin.castAdd s) k)^[j]
      ((embeddedAverage (Fin.natAdd r) k)^[m - j] alive)) Finset.univ
  rw [← blockSet_univ r s, local_iterates_block]
  rfl

end


end FixedClauseThreshold

end OAI
