import OAI.Probability.RandomSAT.Binomial

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev SplitClause (v k : ℕ) := ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)

def DeletedSatisfied {v k : ℕ} (σ : Assignment v) : SplitClause v k → Prop
  | .inl C => SatisfiesClause σ C
  | .inr _ => True

def ErasedSatisfied {v k : ℕ} (σ : Assignment v) : SplitClause v k → Prop
  | .inl C => SatisfiesClause σ C
  | .inr Q => SatisfiesClause σ Q.1

def deletedSolutions {v k m : ℕ} (S : Finset (Assignment v)) (F : Fin m → SplitClause v k) :
    Finset (Assignment v) := S.filter (fun σ => ∀ i, DeletedSatisfied σ (F i))

def erasedSolutions {v k m : ℕ} (S : Finset (Assignment v)) (F : Fin m → SplitClause v k) :
    Finset (Assignment v) := S.filter (fun σ => ∀ i, ErasedSatisfied σ (F i))

@[simp] theorem mem_deletedSolutions {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) (σ : Assignment v) :
    σ ∈ deletedSolutions S F ↔ σ ∈ S ∧ ∀ i, DeletedSatisfied σ (F i) := by
  simp [deletedSolutions]

@[simp] theorem mem_erasedSolutions {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) (σ : Assignment v) :
    σ ∈ erasedSolutions S F ↔ σ ∈ S ∧ ∀ i, ErasedSatisfied σ (F i) := by
  simp [erasedSolutions]

theorem erasedSolutions_subset {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) : erasedSolutions S F ⊆ deletedSolutions S F := by
  intro σ hσ
  rw [mem_erasedSolutions] at hσ
  rw [mem_deletedSolutions]
  refine ⟨hσ.1, fun i => ?_⟩
  have hi := hσ.2 i
  cases hFi : F i with
  | inl C => simpa [ErasedSatisfied, DeletedSatisfied, hFi] using hi
  | inr Q => trivial

theorem satisfies_head_split {v k : ℕ} (hk : 0 < k) (σ : Assignment v)
    (b : Bool) (X : SplitClause v k) :
    SatisfiesClause (Fin.cons b σ) ((clauseHeadEquiv hk).symm X) ↔
      match X with
      | .inl C => SatisfiesClause σ C
      | .inr Q => Q.2 = b ∨ SatisfiesClause σ Q.1 := by
  cases X with
  | inl C => exact satisfiesClause_prependAbsent σ b C
  | inr Q => exact satisfiesClause_prependPresent hk σ b Q.2 Q.1

theorem head_erasure_extension {v k m : ℕ} (hk : 0 < k)
    (F : Fin m → SplitClause v k) {σ : Assignment v}
    (hσ : σ ∈ erasedSolutions Finset.univ F) (b : Bool) :
    Satisfies (Fin.cons b σ) (fun i => (clauseHeadEquiv hk).symm (F i)) := by
  intro i
  rw [satisfies_head_split]
  have hi := ((mem_erasedSolutions _ _ _).mp hσ).2 i
  cases hFi : F i with
  | inl C => simpa [ErasedSatisfied, hFi] using hi
  | inr Q => exact Or.inr (by simpa [ErasedSatisfied, hFi] using hi)

theorem head_deletion_projection {v k m : ℕ} (hk : 0 < k)
    (F : Fin m → SplitClause v k) {σ : Assignment (v + 1)}
    (hσ : Satisfies σ (fun i => (clauseHeadEquiv hk).symm (F i))) :
    Fin.tail σ ∈ deletedSolutions Finset.univ F := by
  rw [mem_deletedSolutions]
  refine ⟨Finset.mem_univ _, fun i => ?_⟩
  have hi := hσ i
  rw [← Fin.cons_self_tail σ, satisfies_head_split] at hi
  cases hFi : F i with
  | inl C => simpa [DeletedSatisfied, hFi] using hi
  | inr Q => trivial

theorem head_forced_reduction {v k m : ℕ} (hk : 0 < k) (F : Fin m → SplitClause v k)
    (hf : (0 : Fin (v + 1)) ∈ forcedVariables
      (restrictSolutions Finset.univ (fun i => (clauseHeadEquiv hk).symm (F i)))) :
    (deletedSolutions Finset.univ F).Nonempty ∧ ¬ (erasedSolutions Finset.univ F).Nonempty := by
  simp only [forcedVariables, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  obtain ⟨σ, hσ⟩ := hf.1
  have hsat : Satisfies σ (fun i => (clauseHeadEquiv hk).symm (F i)) :=
    ((mem_restrictSolutions _ _ _).mp hσ).2
  refine ⟨⟨Fin.tail σ, head_deletion_projection hk F hsat⟩, ?_⟩
  rintro ⟨τ, hτ⟩
  obtain ⟨b, hb⟩ := hf.2
  have hext (t : Bool) : Fin.cons t τ ∈
      restrictSolutions Finset.univ (fun i => (clauseHeadEquiv hk).symm (F i)) := by
    rw [mem_restrictSolutions]
    exact ⟨Finset.mem_univ _, head_erasure_extension hk F hτ t⟩
  have hfalse := hb _ (hext false)
  have htrue := hb _ (hext true)
  simp only [Fin.cons_zero] at hfalse htrue
  cases b <;> simp_all

theorem head_forced_indicator_le {v k m : ℕ} (hk : 0 < k) (F : Fin m → SplitClause v k) :
    (if (0 : Fin (v + 1)) ∈ forcedVariables
      (restrictSolutions Finset.univ (fun i => (clauseHeadEquiv hk).symm (F i)))
      then (1 : ℝ) else 0) ≤
      alive (deletedSolutions Finset.univ F) - alive (erasedSolutions Finset.univ F) := by
  split
  · rename_i h
    obtain ⟨hd, he⟩ := head_forced_reduction hk F h
    simp [alive, hd, he]
  · have h := alive_mono (erasedSolutions_subset Finset.univ F)
    linarith

theorem deletedSolutions_cons_inl {v k m : ℕ} (S : Finset (Assignment v))
    (C : ProperClause v k) (F : Fin m → SplitClause v k) :
    deletedSolutions S (Fin.cons (.inl C) F) = deletedSolutions (addClause S C) F := by
  ext σ
  simp only [mem_deletedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, DeletedSatisfied]
  tauto

theorem deletedSolutions_cons_inr {v k m : ℕ} (S : Finset (Assignment v))
    (Q : ProperClause v (k - 1)) (b : Bool) (F : Fin m → SplitClause v k) :
    deletedSolutions S (Fin.cons (.inr (Q, b)) F) = deletedSolutions S F := by
  ext σ
  simp only [mem_deletedSolutions, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, DeletedSatisfied, true_and]

theorem erasedSolutions_cons_inl {v k m : ℕ} (S : Finset (Assignment v))
    (C : ProperClause v k) (F : Fin m → SplitClause v k) :
    erasedSolutions S (Fin.cons (.inl C) F) = erasedSolutions (addClause S C) F := by
  ext σ
  simp only [mem_erasedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, ErasedSatisfied]
  tauto

theorem erasedSolutions_cons_inr {v k m : ℕ} (S : Finset (Assignment v))
    (Q : ProperClause v (k - 1)) (b : Bool) (F : Fin m → SplitClause v k) :
    erasedSolutions S (Fin.cons (.inr (Q, b)) F) = erasedSolutions (addClause S Q) F := by
  ext σ
  simp only [mem_erasedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, ErasedSatisfied]
  tauto

def deletedMean {v k : ℕ} (hk : 0 < k) (m : ℕ) (S : Finset (Assignment v)) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    alive (deletedSolutions S (fun i => clauseHeadSplit hk (F i))))

def erasedMean {v k : ℕ} (hk : 0 < k) (m : ℕ) (S : Finset (Assignment v)) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    alive (erasedSolutions S (fun i => clauseHeadSplit hk (F i))))

@[simp] theorem deletedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    deletedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      deletedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [deletedMean, h, uniformMean_const]

@[simp] theorem erasedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    erasedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      erasedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [erasedMean, h, uniformMean_const]

theorem deletedMean_succ {v k m : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (S : Finset (Assignment v)) :
    deletedMean hk (m + 1) S =
      (1 - (k : ℝ) / (v + 1)) * clauseAverage k (deletedMean hk m) S +
      ((k : ℝ) / (v + 1)) * deletedMean hk m S := by
  let : Nonempty (ProperClause v (k - 1)) := nonempty_properClause (by omega)
  unfold deletedMean
  rw [uniformMean_fin_succ]
  have hcons (C : ProperClause (v + 1) k) (F : Formula (v + 1) k m) :
      (fun i : Fin (m + 1) => clauseHeadSplit hk ((Fin.cons C F : Formula (v + 1) k (m + 1)) i)) =
        Fin.cons (clauseHeadSplit hk C) (fun i => clauseHeadSplit hk (F i)) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  simp only [hcons]
  rw [clauseHead_mean hk hkv (fun X => uniformMean (fun F : Formula (v + 1) k m =>
    alive (deletedSolutions S (Fin.cons X (fun i => clauseHeadSplit hk (F i))))))]
  simp only [deletedSolutions_cons_inl, deletedSolutions_cons_inr,
    uniformMean_const]
  rfl

theorem erasedMean_succ {v k m : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (S : Finset (Assignment v)) :
    erasedMean hk (m + 1) S =
      (1 - (k : ℝ) / (v + 1)) * clauseAverage k (erasedMean hk m) S +
      ((k : ℝ) / (v + 1)) * clauseAverage (k - 1) (erasedMean hk m) S := by
  unfold erasedMean
  rw [uniformMean_fin_succ]
  have hcons (C : ProperClause (v + 1) k) (F : Formula (v + 1) k m) :
      (fun i : Fin (m + 1) => clauseHeadSplit hk ((Fin.cons C F : Formula (v + 1) k (m + 1)) i)) =
        Fin.cons (clauseHeadSplit hk C) (fun i => clauseHeadSplit hk (F i)) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  simp only [hcons]
  rw [clauseHead_mean hk hkv (fun X => uniformMean (fun F : Formula (v + 1) k m =>
    alive (erasedSolutions S (Fin.cons X (fun i => clauseHeadSplit hk (F i))))))]
  simp only [erasedSolutions_cons_inl, erasedSolutions_cons_inr,
    uniformMean_const]
  rfl

theorem clauseAverage_binomialMean {v k : ℕ} (p : ℝ) (m : ℕ)
    (f : ℕ → Finset (Assignment v) → ℝ) (S : Finset (Assignment v)) :
    clauseAverage k (fun T => binomialMean p m (fun d => f d T)) S =
      binomialMean p m (fun d => clauseAverage k (f d) S) :=
  uniformMean_binomialMean p m _

theorem clauseAverage_survival {v k t : ℕ} (S : Finset (Assignment v)) :
    clauseAverage k (survival k t) S = survival k (t + 1) S :=
  (survival_succ S).symm

theorem clauseAverage_short_survival {n k t : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    survival k (t + replacementBlock n k) S - replacementError n k ≤
      clauseAverage (k - 1) (survival k t) S := by
  have h := clauseAverage_iterate_mono (k := k) (m := t)
    (shorter_survival_replacement hk hn) S
  rw [clauseAverage_iterate_sub_const (by omega)] at h
  dsimp only at h
  rw [survival_add] at h
  have he : clauseAverage (k - 1) (survival k t) S =
      ((clauseAverage k)^[t] (survival (k - 1) 1)) S :=
    survival_shift (m := 1) (d := t) S
  rw [he]
  simpa using h

theorem deletedMean_eq_binomial {v k m : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (S : Finset (Assignment v)) :
    deletedMean hk m S = binomialMean ((k : ℝ) / (v + 1)) m
      (fun d => survival k (m - d) S) := by
  induction m generalizing S with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [deletedMean_succ hk hkv]
    have hfun : deletedMean hk m =
        (fun T : Finset (Assignment v) => binomialMean ((k : ℝ) / (v + 1)) m
          (fun d => survival k (m - d) T)) := funext ih
    rw [hfun, clauseAverage_binomialMean]
    change _ = (1 - (k : ℝ) / (v + 1)) * _ + ((k : ℝ) / (v + 1)) * _
    congr 1
    · congr 1
      apply binomialMean_congr
      intro d hd
      rw [clauseAverage_survival]
      congr 1
      omega
    · congr 1
      apply binomialMean_congr
      intro d _
      congr 1
      omega

theorem erasedMean_replacement {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    binomialMean ((k : ℝ) / n) m (fun d =>
      survival k (m - d + replacementBlock n k * d) S -
        (d : ℝ) * replacementError n k) ≤ erasedMean (by omega : 0 < k) m S := by
  have hkn : k ≤ n - 1 := by omega
  have hshort : k - 1 ≤ n - 1 := by omega
  have hn1 : n - 1 + 1 = n := by omega
  have hp0 : 0 ≤ (k : ℝ) / n := by positivity
  have hp1 : (k : ℝ) / n ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (by omega : 0 < n))).mpr
    exact_mod_cast (by omega : k ≤ n)
  induction m generalizing S with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [erasedMean_succ (by omega) hkn]
    have hden : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hn1
    rw [hden]
    have hlong := clauseAverage_mono (k := k) ih S
    have hshorter := clauseAverage_mono (k := k - 1) ih S
    rw [clauseAverage_binomialMean] at hlong hshorter
    have ha : binomialMean ((k : ℝ) / n) m (fun d =>
        survival k (m + 1 - d + replacementBlock n k * d) S -
          (d : ℝ) * replacementError n k) ≤ clauseAverage k (erasedMean (by omega : 0 < k) m) S := by
      calc
        _ = binomialMean ((k : ℝ) / n) m (fun d => clauseAverage k
            (fun T => survival k (m - d + replacementBlock n k * d) T -
              (d : ℝ) * replacementError n k) S) := by
          apply binomialMean_congr
          intro d hd
          rw [clauseAverage_sub_const hkn, clauseAverage_survival]
          congr 2
          omega
        _ ≤ _ := hlong
    have hb : binomialMean ((k : ℝ) / n) m (fun d =>
        survival k (m + 1 - (d + 1) + replacementBlock n k * (d + 1)) S -
          ((d + 1 : ℕ) : ℝ) * replacementError n k) ≤
        clauseAverage (k - 1) (erasedMean (by omega : 0 < k) m) S := by
      apply le_trans _ hshorter
      apply binomialMean_mono hp0 hp1
      intro d _
      rw [clauseAverage_sub_const hshort]
      have h := clauseAverage_short_survival (t := m - d + replacementBlock n k * d) hk hn S
      have he : m + 1 - (d + 1) + replacementBlock n k * (d + 1) =
          m - d + replacementBlock n k * d + replacementBlock n k := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [he]
      push_cast
      linarith
    exact add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left hb hp0)

theorem replacementBlock_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    1 ≤ replacementBlock n k := by
  have hp : 0 < 2 * (k : ℝ) * replacementScale n k :=
    mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk)) (replacementScale_pos hn)
  exact Nat.ceil_pos.mpr hp

theorem replacementError_nonneg (n k : ℕ) : 0 ≤ replacementError n k := by
  unfold replacementError replacementScale
  positivity

def headForcedMean (v k m : ℕ) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    if (0 : Fin (v + 1)) ∈ forcedVariables (restrictSolutions Finset.univ F)
      then (1 : ℝ) else 0)

theorem headForcedMean_le_difference {v k m : ℕ} (hk : 0 < k) :
    headForcedMean v k m ≤ deletedMean (v := v) hk m Finset.univ - erasedMean (v := v) hk m Finset.univ := by
  unfold headForcedMean deletedMean erasedMean
  rw [← uniformMean_sub]
  apply uniformMean_mono
  intro F
  have he : (fun i => (clauseHeadEquiv hk).symm (clauseHeadSplit hk (F i))) = F := by
    funext i
    exact (clauseHeadEquiv hk).symm_apply_apply (F i)
  have h := head_forced_indicator_le hk (fun i => clauseHeadSplit hk (F i))
  simpa only [he] using h

theorem headForcedMean_replacement {v k m : ℕ} (hk : 3 ≤ k) (hkv : k ≤ v) :
    headForcedMean v k m ≤
      binomialMean ((k : ℝ) / (v + 1)) m
        (replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) m) +
      ((m : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k := by
  have hdel := deletedMean_eq_binomial (m := m) (by omega : 0 < k) hkv Finset.univ
  have her := erasedMean_replacement (n := v + 1) (m := m) hk (by omega) Finset.univ
  simp only [Nat.cast_add, Nat.cast_one] at her
  have hforced := headForcedMean_le_difference (v := v) (m := m) (by omega : 0 < k)
  rw [hdel] at hforced
  have hsub : (binomialMean ((k : ℝ) / (v + 1)) m (fun d => survival k (m - d)
      (Finset.univ : Finset (Assignment v)))) -
      binomialMean ((k : ℝ) / (v + 1)) m (fun d =>
        survival k (m - d + replacementBlock (v + 1) k * d)
          (Finset.univ : Finset (Assignment v)) -
          (d : ℝ) * replacementError (v + 1) k) =
      binomialMean ((k : ℝ) / (v + 1)) m
        (replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) m) +
      ((m : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k := by
    rw [← binomialMean_sub]
    have hg : 1 ≤ replacementBlock (v + 1) k := replacementBlock_pos (by omega) (by omega)
    calc
      _ = binomialMean ((k : ℝ) / (v + 1)) m (fun d =>
          replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) m d +
            (d : ℝ) * replacementError (v + 1) k) := by
        apply binomialMean_congr
        intro d hd
        unfold replacementDifference
        rw [properSATProbability_eq_survival, properSATProbability_eq_survival]
        have he : m - d + replacementBlock (v + 1) k * d =
            m + (replacementBlock (v + 1) k - 1) * d := by
          have hh := Nat.sub_add_cancel hg
          have := congrArg (fun a : ℕ => a * d) hh
          simp only [Nat.add_mul, Nat.one_mul] at this
          omega
        rw [he]
        ring
      _ = _ := by rw [binomialMean_add, binomialMean_mul_const, binomialMean_id]
  rw [← hsub]
  linarith

theorem integrated_head_forcing {v k : ℕ} (hk : 3 ≤ k) (hkv : k ≤ v) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), headForcedMean v k j ≤
      (replacementBlock (v + 1) k : ℝ) * M * ((k : ℝ) / (v + 1)) +
      ((M + 1 : ℕ) : ℝ) * M * ((k : ℝ) / (v + 1)) * replacementError (v + 1) k := by
  have hp0 : 0 ≤ (k : ℝ) / (v + 1) := by positivity
  have hp1 : (k : ℝ) / (v + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (by omega : k ≤ v + 1)
  calc
    _ ≤ ∑ j ∈ Finset.range (M + 1),
        (binomialMean ((k : ℝ) / (v + 1)) j
          (replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) j) +
        ((j : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k) :=
      Finset.sum_le_sum (fun _ _ => headForcedMean_replacement hk hkv)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by
      apply add_le_add
      · exact binomial_replacement_sum_le hp0 hp1 (properSATProbability_antitone hkv)
          (fun j => properSATProbability_nonneg v k j) (fun j => properSATProbability_le_one v k j)
          (replacementBlock_pos (by omega) (by omega)) M
      · calc
          _ ≤ ∑ _j ∈ Finset.range (M + 1),
              ((M : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k := by
            apply Finset.sum_le_sum
            intro j hj
            have hjM : (j : ℝ) ≤ M := by
              exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjM hp0)
              (replacementError_nonneg (v + 1) k)
          _ = _ := by simp; ring

def renameClause {n k : ℕ} (e : Fin n ≃ Fin n) (C : ProperClause n k) : ProperClause n k :=
  ⟨fun i => C.val (e i), by
    have h := Fintype.card_congr
      (e.subtypeEquivOfSubtype (p := fun i => (C.val i).isSome))
    simp only [Fintype.card_subtype] at h
    exact h.trans C.property⟩

def renameClauseEquiv {n k : ℕ} (e : Fin n ≃ Fin n) : ProperClause n k ≃ ProperClause n k where
  toFun := renameClause e
  invFun := renameClause e.symm
  left_inv C := by apply Subtype.ext; funext i; simp [renameClause]
  right_inv C := by apply Subtype.ext; funext i; simp [renameClause]

def renameAssignment {n : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n) : Assignment n :=
  fun i => σ (e i)

def renameFormula {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) : Formula n k m :=
  fun i => renameClause e (F i)

def renameFormulaEquiv {n k m : ℕ} (e : Fin n ≃ Fin n) : Formula n k m ≃ Formula n k m :=
  Equiv.piCongrRight (fun _ => renameClauseEquiv e)

theorem renameFormulaEquiv_apply {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) :
    renameFormulaEquiv e F = renameFormula e F := rfl

theorem satisfiesClause_rename {n k : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n)
    (C : ProperClause n k) :
    SatisfiesClause (renameAssignment e σ) (renameClause e C) ↔ SatisfiesClause σ C := by
  change (∃ i, C.val (e i) = some (σ (e i))) ↔ ∃ i, C.val i = some (σ i)
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa using hi⟩

theorem satisfies_rename {n k m : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n)
    (F : Formula n k m) :
    Satisfies (renameAssignment e σ) (renameFormula e F) ↔ Satisfies σ F := by
  simp only [Satisfies, renameFormula, satisfiesClause_rename]

theorem satisfies_rename_inverse {n k m : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n)
    (F : Formula n k m) :
    Satisfies σ (renameFormula e F) ↔ Satisfies (renameAssignment e.symm σ) F := by
  have h := satisfies_rename e (renameAssignment e.symm σ) F
  have he : renameAssignment e (renameAssignment e.symm σ) = σ := by
    funext i
    exact congrArg σ (e.symm_apply_apply i)
  rw [he] at h
  exact h

theorem satisfiable_rename {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) :
    Satisfiable (renameFormula e F) ↔ Satisfiable F := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨renameAssignment e.symm σ, (satisfies_rename_inverse e σ F).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨renameAssignment e σ, (satisfies_rename e σ F).mpr hσ⟩

theorem mem_forced_formula {n k m : ℕ} (F : Formula n k m) (i : Fin n) :
    i ∈ forcedVariables (restrictSolutions Finset.univ F) ↔
      Satisfiable F ∧ ∃ b, ∀ σ, Satisfies σ F → σ i = b := by
  simp [forcedVariables, Finset.Nonempty, Satisfiable, Satisfies]

theorem forcedVariables_rename {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) (i : Fin n) :
    i ∈ forcedVariables (restrictSolutions Finset.univ (renameFormula e F)) ↔
      e i ∈ forcedVariables (restrictSolutions Finset.univ F) := by
  rw [mem_forced_formula, mem_forced_formula, satisfiable_rename]
  constructor
  · rintro ⟨hS, b, hb⟩
    refine ⟨hS, b, fun σ hσ => ?_⟩
    exact hb (renameAssignment e σ) ((satisfies_rename e σ F).mpr hσ)
  · rintro ⟨hS, b, hb⟩
    refine ⟨hS, b, fun σ hσ => ?_⟩
    have h := hb (renameAssignment e.symm σ) ((satisfies_rename_inverse e σ F).mp hσ)
    simpa only [renameAssignment, Equiv.symm_apply_apply] using h

theorem forced_coordinate_mean {v k m : ℕ} (i : Fin (v + 1)) :
    uniformMean (fun F : Formula (v + 1) k m =>
      if i ∈ forcedVariables (restrictSolutions Finset.univ F) then (1 : ℝ) else 0) =
        headForcedMean v k m := by
  let e : Fin (v + 1) ≃ Fin (v + 1) := Equiv.swap 0 i
  calc
    _ = uniformMean (fun F : Formula (v + 1) k m =>
        if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ (renameFormula e F)) then (1 : ℝ) else 0) := by
      apply uniformMean_congr
      intro F
      simp only [forcedVariables_rename, e, Equiv.swap_apply_left]
    _ = _ := by
      have h := uniformMean_equiv (renameFormulaEquiv (n := v + 1) (k := k) (m := m) e)
        (fun F : Formula (v + 1) k m => if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ F) then (1 : ℝ) else 0)
      have heq : (fun F : Formula (v + 1) k m => if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ (renameFormula e F)) then (1 : ℝ) else 0) =
          (fun F : Formula (v + 1) k m => if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ (renameFormulaEquiv e F)) then (1 : ℝ) else 0) := by
        funext F
        apply ite_congr
        · rfl
        · intro _; rfl
        · intro _; rfl
      rw [heq]
      exact h

def forcedFractionMean (n k m : ℕ) : ℝ :=
  uniformMean (fun F : Formula n k m =>
    ((forcedVariables (restrictSolutions Finset.univ F)).card : ℝ) / n)

theorem forcedFractionMean_eq_head (v k m : ℕ) :
    forcedFractionMean (v + 1) k m = headForcedMean v k m := by
  have hc (F : Formula (v + 1) k m) :
      ((forcedVariables (restrictSolutions Finset.univ F)).card : ℝ) =
        ∑ i : Fin (v + 1), if i ∈ forcedVariables (restrictSolutions Finset.univ F)
          then (1 : ℝ) else 0 := by simp
  unfold forcedFractionMean
  simp_rw [hc, div_eq_mul_inv]
  rw [uniformMean_mul_const, uniformMean_sum]
  simp only [forced_coordinate_mean, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hv : ((v + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem integrated_forcing_finite {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), forcedFractionMean n k j ≤
      (replacementBlock n k : ℝ) * M * ((k : ℝ) / n) +
      ((M + 1 : ℕ) : ℝ) * M * ((k : ℝ) / n) * replacementError n k := by
  cases n with
  | zero => omega
  | succ v =>
    simp only [forcedFractionMean_eq_head]
    simpa only [Nat.cast_add, Nat.cast_one] using integrated_head_forcing hk (by omega) M

end


end FixedClauseThreshold

end OAI
