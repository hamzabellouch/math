import OAI.Probability.RandomSAT.Forcing

namespace OAI

/-!
Stopped satisfiable lifetimes, insertion delays, and the coordinate-omission
variance bound in terms of integrated forcing.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem addClause_subset {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    addClause S C ⊆ S := Finset.filter_subset _ _

theorem addClause_mono {n k : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T)
    (C : ProperClause n k) : addClause S C ⊆ addClause T C := by
  intro σ hσ
  rw [mem_addClause] at hσ ⊢
  exact ⟨hST hσ.1, hσ.2⟩

@[simp] theorem addClause_empty {n k : ℕ} (C : ProperClause n k) :
    addClause ∅ C = ∅ := by simp [addClause]

@[simp] theorem alive_empty {n : ℕ} : alive (∅ : Finset (Assignment n)) = 0 := by simp [alive]

@[simp] theorem survival_empty {n k m : ℕ} : survival k m (∅ : Finset (Assignment n)) = 0 := by
  rw [survival_eq_mean]
  have h (F : Formula n k m) : restrictSolutions ∅ F = ∅ := by simp [restrictSolutions]
  simp only [h, alive_empty, uniformMean_zero]

def lifetime {n : ℕ} (k : ℕ) : (m : ℕ) → Finset (Assignment n) → Formula n k m → ℝ
  | 0, _, _ => 0
  | m + 1, S, F => alive (addClause S (F 0)) +
      lifetime k m (addClause S (F 0)) (Fin.tail F)

@[simp] theorem lifetime_zero {n k : ℕ} (S : Finset (Assignment n)) (F : Formula n k 0) :
    lifetime k 0 S F = 0 := rfl

@[simp] theorem lifetime_cons {n k m : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k)
    (F : Formula n k m) : lifetime k (m + 1) S (Fin.cons C F) =
      alive (addClause S C) + lifetime k m (addClause S C) F := rfl

@[simp] theorem lifetime_empty {n k m : ℕ} (F : Formula n k m) : lifetime k m ∅ F = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [lifetime, ih]

theorem lifetime_nonneg {n k m : ℕ} (S : Finset (Assignment n)) (F : Formula n k m) :
    0 ≤ lifetime k m S F := by
  induction m generalizing S with
  | zero => exact le_rfl
  | succ m ih => exact add_nonneg (alive_nonneg _) (ih _ _)

theorem lifetime_le {n k m : ℕ} (S : Finset (Assignment n)) (F : Formula n k m) :
    lifetime k m S F ≤ m := by
  induction m generalizing S with
  | zero => simp [lifetime]
  | succ m ih =>
    simp only [lifetime, Nat.cast_add, Nat.cast_one]
    linarith [alive_le_one (addClause S (F 0)), ih (addClause S (F 0)) (Fin.tail F)]

theorem lifetime_mono {n k m : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T)
    (F : Formula n k m) : lifetime k m S F ≤ lifetime k m T F := by
  induction m generalizing S T with
  | zero => exact le_rfl
  | succ m ih =>
    exact add_le_add (alive_mono (addClause_mono hST (F 0)))
      (ih (addClause_mono hST (F 0)) (Fin.tail F))

def lifetimeMean {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformMean (lifetime k m S)

def lifetimeVariance {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformVariance (lifetime k m S)

theorem lifetimeMean_succ {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    lifetimeMean k (m + 1) S = clauseAverage k (fun T => alive T + lifetimeMean k m T) S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  unfold lifetimeMean
  rw [uniformMean_fin_succ]
  simp only [lifetime_cons, uniformMean_add, uniformMean_const]
  simp only [clauseAverage, uniformMean_add]

theorem clauseAverage_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Finset (Assignment n) → ℝ) (S : Finset (Assignment n)) :
    clauseAverage k (fun T => ∑ i ∈ s, f i T) S =
      ∑ i ∈ s, clauseAverage k (f i) S := uniformMean_sum s _

theorem lifetimeMean_eq_sum {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    lifetimeMean k m S = ∑ j ∈ Finset.range m, survival k (j + 1) S := by
  induction m generalizing S with
  | zero => exact uniformMean_zero
  | succ m ih =>
    rw [lifetimeMean_succ hkn]
    have hfun : (fun T : Finset (Assignment n) => alive T + lifetimeMean k m T) =
        fun T => ∑ j ∈ Finset.range (m + 1), survival k j T := by
      funext T
      rw [Finset.sum_range_succ', ih, survival_zero]
      ring
    rw [hfun, clauseAverage_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact clauseAverage_survival S

def killingChance {n : ℕ} (k : ℕ) (S : Finset (Assignment n)) : ℝ :=
  alive S - survival k 1 S

theorem killingChance_nonneg {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    0 ≤ killingChance k S := by
  have h := survival_antitone hkn S (Nat.zero_le 1)
  exact sub_nonneg.mpr h

theorem killingChance_le_one {n k : ℕ} (S : Finset (Assignment n)) : killingChance k S ≤ 1 := by
  unfold killingChance
  linarith [alive_le_one S, survival_nonneg (k := k) (m := 1) S]

theorem killingChance_eq_mean {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    killingChance k S = uniformMean (fun C : ProperClause n k => alive S - alive (addClause S C)) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [uniformMean_sub, uniformMean_const]
  rfl

theorem killingChance_eq_probability {n k : ℕ} (hkn : k ≤ n) {S : Finset (Assignment n)}
    (hS : S.Nonempty) :
    killingChance k S = uniformProbability (fun C : ProperClause n k => KillsSolutions S C) := by
  rw [singleUNSAT_eq hkn]
  simp [killingChance, alive, hS]

theorem survival_le_geometric {n k d : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    survival k d S ≤ (1 - killingChance k S) ^ d := by
  by_cases hS : S.Nonempty
  · have h := blockUNSAT_lower (g := d) hkn S
    rw [blockUNSAT_eq hkn, ← killingChance_eq_probability hkn hS] at h
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [survival_empty]
    exact pow_nonneg (sub_nonneg.mpr (killingChance_le_one ∅)) _

def insertionDelay {n : ℕ} (k m : ℕ) (S : Finset (Assignment n))
    (C : ProperClause n k) (F : Formula n k m) : ℝ :=
  (alive S + lifetime k m S F) - (alive (addClause S C) + lifetime k m (addClause S C) F)

def insertionSecond {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformMean (fun C : ProperClause n k => uniformMean (fun F : Formula n k m =>
    insertionDelay k m S C F ^ 2))

theorem insertionDelay_zero {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k)
    (F : Formula n k 0) : insertionDelay k 0 S C F = alive S - alive (addClause S C) := by
  simp [insertionDelay]

theorem insertionDelay_cons {n k m : ℕ} (S : Finset (Assignment n)) (C D : ProperClause n k)
    (F : Formula n k m) : insertionDelay k (m + 1) S C (Fin.cons D F) =
      alive S - alive (addClause S C) + insertionDelay k m (addClause S D) C F := by
  simp only [insertionDelay, lifetime_cons, addClause_comm S C D]
  ring

theorem pivot_sq {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    (alive S - alive (addClause S C)) ^ 2 = alive S - alive (addClause S C) := by
  have hsub := alive_mono (addClause_subset S C)
  unfold alive at hsub ⊢
  split_ifs at hsub ⊢ <;> norm_num at *

theorem insertionDelay_cross {n k m : ℕ} {S T : Finset (Assignment n)} (hTS : T ⊆ S)
    (C : ProperClause n k) (F : Formula n k m) :
    (alive S - alive (addClause S C)) * insertionDelay k m T C F =
      (alive S - alive (addClause S C)) * (alive T + lifetime k m T F) := by
  by_cases hzero : alive S - alive (addClause S C) = 0
  · rw [hzero, zero_mul, zero_mul]
  · have he : addClause S C = ∅ := by
      by_contra hn
      have hSC := Finset.nonempty_iff_ne_empty.mpr hn
      have hS := hSC.mono (addClause_subset S C)
      simp [alive, hSC, hS] at hzero
    have hf : addClause T C = ∅ := Finset.subset_empty.mp (by
      rw [← he]
      exact addClause_mono hTS C)
    simp [insertionDelay, hf]

theorem insertionDelay_cons_sq {n k m : ℕ} (S : Finset (Assignment n)) (C D : ProperClause n k)
    (F : Formula n k m) : insertionDelay k (m + 1) S C (Fin.cons D F) ^ 2 =
      insertionDelay k m (addClause S D) C F ^ 2 + (alive S - alive (addClause S C)) +
      2 * (alive S - alive (addClause S C)) *
        (alive (addClause S D) + lifetime k m (addClause S D) F) := by
  rw [insertionDelay_cons]
  have h := insertionDelay_cross (addClause_subset S D) C F
  have hs := pivot_sq S C
  nlinarith [hs, h]

theorem insertionSecond_zero {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    insertionSecond k 0 S = killingChance k S := by
  rw [killingChance_eq_mean hkn]
  unfold insertionSecond
  apply uniformMean_congr
  intro C
  simp only [insertionDelay_zero, pivot_sq, uniformMean_const]

theorem insertionSecond_succ {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    insertionSecond k (m + 1) S = clauseAverage k (insertionSecond k m) S +
      killingChance k S * (1 + 2 * lifetimeMean k (m + 1) S) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  unfold insertionSecond
  simp_rw [uniformMean_fin_succ, insertionDelay_cons_sq, uniformMean_add,
    uniformMean_const_mul, uniformMean_const]
  rw [uniformMean_comm (fun C D => uniformMean
    (fun F : Formula n k m => insertionDelay k m (addClause S D) C F ^ 2))]
  rw [← killingChance_eq_mean hkn]
  have hmean : (uniformMean fun D : ProperClause n k =>
      alive (addClause S D) + uniformMean (lifetime k m (addClause S D))) =
      lifetimeMean k (m + 1) S := (lifetimeMean_succ hkn S).symm
  simp_rw [uniformMean_add, uniformMean_const]
  simp only [uniformMean_add] at hmean
  rw [hmean]
  simp only [uniformMean_mul_const, uniformMean_const_mul,
    ← killingChance_eq_mean hkn]
  dsimp only [clauseAverage]
  ring

theorem killing_geometric_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℕ) :
    q * ∑ j ∈ Finset.range t, (1 - q)^j ≤ min ((t : ℝ) * q) 1 := by
  have hgeom : q * ∑ j ∈ Finset.range t, (1 - q)^j = 1 - (1 - q)^t := by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  apply le_min
  · calc
      _ ≤ q * ∑ _j ∈ Finset.range t, (1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
          pow_le_one₀ (by linarith) (by linarith))) hq0
      _ = _ := by simp; ring
  · rw [hgeom]
    linarith [pow_nonneg (sub_nonneg.mpr hq1) t]

def truncatedKilling {n : ℕ} (k M : ℕ) (S : Finset (Assignment n)) : ℝ :=
  min ((M : ℝ) * killingChance k S) 1

theorem pivotal_local_bound {n k m M : ℕ} (hkn : k ≤ n) (hm : m + 1 ≤ M)
    (S : Finset (Assignment n)) :
    killingChance k S * (1 + 2 * lifetimeMean k m S) ≤ 2 * truncatedKilling k M S := by
  have hq0 := killingChance_nonneg hkn S
  have hq1 := killingChance_le_one (k := k) S
  have hsum : 1 + lifetimeMean k m S ≤
      ∑ j ∈ Finset.range (m + 1), (1 - killingChance k S)^j := by
    rw [lifetimeMean_eq_sum hkn, Finset.sum_range_succ']
    simp only [pow_zero]
    simpa only [add_comm] using add_le_add_left
      (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range m) =>
        survival_le_geometric (d := j + 1) hkn S)) 1
  have hgeom := killing_geometric_sum hq0 hq1 (m + 1)
  have hmin : min (((m + 1 : ℕ) : ℝ) * killingChance k S) 1 ≤ truncatedKilling k M S := by
    exact min_le_min (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hq0) le_rfl
  have hh := mul_le_mul_of_nonneg_left hsum hq0
  nlinarith

def occupation {n : ℕ} (k : ℕ) (f : Finset (Assignment n) → ℝ) :
    ℕ → Finset (Assignment n) → ℝ
  | 0, _ => 0
  | m + 1, S => f S + clauseAverage k (occupation k f m) S

theorem occupation_eq_sum {n k m : ℕ} (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    occupation k f m S = ∑ j ∈ Finset.range m, ((clauseAverage k)^[j] f) S := by
  induction m generalizing S with
  | zero => simp [occupation]
  | succ m ih =>
    simp only [occupation]
    have he : occupation k f m = fun T => ∑ j ∈ Finset.range m, ((clauseAverage k)^[j] f) T :=
      funext ih
    rw [he, clauseAverage_sum, Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    ring

theorem occupation_nonneg {n k m : ℕ} {f : Finset (Assignment n) → ℝ}
    (hf : ∀ S, 0 ≤ f S) (S : Finset (Assignment n)) : 0 ≤ occupation k f m S := by
  induction m generalizing S with
  | zero => exact le_rfl
  | succ m ih => exact add_nonneg (hf S) (uniformMean_nonneg (fun C => ih _))

theorem insertionSecond_le_occupation {n k m M : ℕ} (hkn : k ≤ n) (hm : m + 1 ≤ M)
    (S : Finset (Assignment n)) :
    insertionSecond k m S ≤ 2 * occupation k (truncatedKilling k M) (m + 1) S := by
  induction m generalizing S with
  | zero =>
    rw [insertionSecond_zero hkn]
    have hp := pivotal_local_bound (m := 0) hkn hm S
    simpa [occupation, clauseAverage, uniformMean_zero, lifetimeMean, lifetime, uniformMean] using hp
  | succ m ih =>
    rw [insertionSecond_succ hkn, occupation]
    have hp := pivotal_local_bound (m := m + 1) hkn hm S
    have havg := clauseAverage_mono (k := k) (fun T => ih (by omega) T) S
    change clauseAverage k (insertionSecond k m) S ≤
      uniformMean (fun C : ProperClause n k => 2 * occupation k (truncatedKilling k M) (m + 1)
        (addClause S C)) at havg
    rw [uniformMean_const_mul] at havg
    change clauseAverage k (insertionSecond k m) S ≤
      2 * clauseAverage k (occupation k (truncatedKilling k M) (m + 1)) S at havg
    linarith

theorem uniformVariance_const_add {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) : uniformVariance (fun a => c + f a) = uniformVariance f := by
  unfold uniformVariance
  rw [uniformMean_add, uniformMean_const]
  apply uniformMean_congr
  intro a
  congr 1
  ring

theorem uniformVariance_product {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → β → ℝ) :
    uniformVariance (fun p : α × β => f p.1 p.2) =
      uniformMean (fun a => uniformVariance (f a)) +
        uniformVariance (fun a => uniformMean (f a)) := by
  simp only [uniformVariance_eq, uniformMean_prod, uniformMean_sub]
  ring

theorem uniformVariance_fin_succ {α : Type*} [Fintype α] [Nonempty α] {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    uniformVariance f = uniformMean (fun C => uniformVariance (fun F : Fin m → α =>
      f (Fin.cons C F))) + uniformVariance (fun C => uniformMean (fun F : Fin m → α =>
      f (Fin.cons C F))) := by
  simp only [uniformVariance_eq, uniformMean_fin_succ, uniformMean_sub]
  ring

theorem lifetimeVariance_succ_le {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    lifetimeVariance k (m + 1) S ≤
      clauseAverage k (lifetimeVariance k m) S + insertionSecond k m S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  unfold lifetimeVariance
  rw [uniformVariance_fin_succ]
  simp only [lifetime_cons, uniformVariance_const_add]
  apply add_le_add le_rfl
  let c := alive S + lifetimeMean k m S
  calc
    _ ≤ uniformMean (fun C : ProperClause n k =>
        (uniformMean (fun F : Formula n k m =>
          alive (addClause S C) + lifetime k m (addClause S C) F) - c)^2) :=
        uniformVariance_le_sq_dist _ c
    _ ≤ insertionSecond k m S := by
      apply uniformMean_mono
      intro C
      have h := uniformMean_sq_ge (fun F : Formula n k m => insertionDelay k m S C F)
      have he : uniformMean (fun F : Formula n k m => insertionDelay k m S C F) =
          c - uniformMean (fun F : Formula n k m =>
            alive (addClause S C) + lifetime k m (addClause S C) F) := by
        simp only [insertionDelay, uniformMean_sub, uniformMean_add, uniformMean_const,
          c, lifetimeMean]
      rw [he] at h
      nlinarith

theorem clauseAverage_const_mul {n k : ℕ} (c : ℝ) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    clauseAverage k (fun T => c * f T) S = c * clauseAverage k f S :=
  uniformMean_const_mul c _

theorem lifetimeVariance_le_occupation {n k m M : ℕ} (hkn : k ≤ n) (hm : m ≤ M)
    (S : Finset (Assignment n)) :
    lifetimeVariance k m S ≤ 2 * m * occupation k (truncatedKilling k M) m S := by
  induction m generalizing S with
  | zero => simp [lifetimeVariance, lifetime, uniformVariance, uniformMean]
  | succ m ih =>
    have hv := lifetimeVariance_succ_le (m := m) hkn S
    have hi := insertionSecond_le_occupation hkn hm S
    have havg := clauseAverage_mono (k := k) (fun T => ih (by omega) T) S
    rw [clauseAverage_const_mul] at havg
    have hq : 0 ≤ truncatedKilling k M S :=
      le_min (mul_nonneg (Nat.cast_nonneg _) (killingChance_nonneg hkn S)) zero_le_one
    have he : occupation k (truncatedKilling k M) (m + 1) S =
        truncatedKilling k M S + clauseAverage k (occupation k (truncatedKilling k M) m) S := rfl
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hq]

theorem killingChance_eq_killingProbability {n k : ℕ} (hkn : k ≤ n)
    (S : Finset (Assignment n)) : killingChance k S = killingProbability k S := by
  by_cases hS : S.Nonempty
  · rw [killingChance_eq_probability hkn hS]
    simp [killingProbability, hS]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [killingChance]

def forcedFraction {n : ℕ} (S : Finset (Assignment n)) : ℝ :=
  ((forcedVariables S).card : ℝ) / n

theorem forcedFraction_nonneg {n : ℕ} (S : Finset (Assignment n)) : 0 ≤ forcedFraction S := by
  unfold forcedFraction
  positivity

theorem forcedFraction_le_one {n : ℕ} (S : Finset (Assignment n)) : forcedFraction S ≤ 1 := by
  by_cases hn : n = 0
  · simp [forcedFraction, hn]
  · rw [forcedFraction, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    exact_mod_cast (show (forcedVariables S).card ≤ n by simpa using Finset.card_le_univ (forcedVariables S))

theorem killingChance_le_forced_pow {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (S : Finset (Assignment n)) : killingChance k S ≤ forcedFraction S ^ k := by
  rw [killingChance_eq_killingProbability hkn, killingProbability_eq hk]
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hbn : (forcedVariables S).card ≤ n := by simpa using Finset.card_le_univ (forcedVariables S)
  have h := killFraction_le_pow hbn hkn hn
  apply h.trans
  apply pow_le_pow_left₀ (by positivity)
  unfold forcedFraction
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hn)
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem truncatedKilling_le_forced {n k M : ℕ} {L : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (hL : 1 ≤ L) (hM : (M : ℝ) ≤ L * n)
    (S : Finset (Assignment n)) :
    truncatedKilling k M S ≤ L * replacementScale n k * forcedFraction S := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have ha := replacementScale_pos (k := k) hn
  have hr := forcedFraction_nonneg S
  have ht : 0 ≤ replacementScale n k * forcedFraction S := mul_nonneg ha.le hr
  by_cases hsmall : replacementScale n k * forcedFraction S ≤ 1
  · calc
      truncatedKilling k M S ≤ (M : ℝ) * killingChance k S := min_le_left _ _
      _ ≤ (L * n) * forcedFraction S ^ k :=
        mul_le_mul hM (killingChance_le_forced_pow hk hkn S)
          (killingChance_nonneg hkn S) (by positivity)
      _ = L * (replacementScale n k * forcedFraction S)^k := by
        rw [mul_pow, replacementScale_pow hn hk]
        ring
      _ ≤ L * (replacementScale n k * forcedFraction S) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have he : (replacementScale n k * forcedFraction S)^k =
            (replacementScale n k * forcedFraction S)^(k - 1) *
              (replacementScale n k * forcedFraction S) := by
          rw [← pow_succ, Nat.sub_add_cancel hk]
        rw [he]
        exact mul_le_of_le_one_left ht (pow_le_one₀ ht hsmall)
      _ = _ := by ring
  · calc
      truncatedKilling k M S ≤ 1 := min_le_right _ _
      _ ≤ L * (replacementScale n k * forcedFraction S) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hL) ht]
      _ = _ := by ring

theorem clauseAverage_iterate_eq_mean {n k m : ℕ} (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] f) S = uniformMean (fun F : Formula n k m =>
      f (restrictSolutions S F)) := by
  induction m generalizing S with
  | zero =>
    simp only [Function.iterate_zero, id_eq, restrictSolutions_zero, uniformMean_const]
  | succ m ih =>
    rw [Function.iterate_succ_apply', uniformMean_fin_succ]
    change uniformMean (fun C : ProperClause n k =>
      ((clauseAverage k)^[m] f) (addClause S C)) = _
    apply uniformMean_congr
    intro C
    rw [ih]
    apply uniformMean_congr
    intro F
    rw [restrictSolutions_cons]

theorem occupation_forced_eq {n k m : ℕ} :
    occupation k (forcedFraction (n := n)) m Finset.univ =
      ∑ j ∈ Finset.range m, forcedFractionMean n k j := by
  rw [occupation_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact clauseAverage_iterate_eq_mean _ _

theorem occupation_mono {n k m : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) (S : Finset (Assignment n)) :
    occupation k f m S ≤ occupation k g m S := by
  rw [occupation_eq_sum, occupation_eq_sum]
  exact Finset.sum_le_sum fun _ _ => clauseAverage_iterate_mono hfg S

theorem occupation_const_mul {n k m : ℕ} (c : ℝ) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    occupation k (fun T => c * f T) m S = c * occupation k f m S := by
  induction m generalizing S with
  | zero => simp [occupation]
  | succ m ih =>
    simp only [occupation]
    have he : occupation k (fun T => c * f T) m = fun T => c * occupation k f m T := funext ih
    rw [he, clauseAverage_const_mul]
    ring

theorem lifetimeVariance_forcing_bound {n k M : ℕ} {L : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (hL : 1 ≤ L) (hM : (M : ℝ) ≤ L * n) :
    lifetimeVariance k M (Finset.univ : Finset (Assignment n)) ≤
      (2 * M * L * replacementScale n k) *
        ∑ j ∈ Finset.range M, forcedFractionMean n k j := by
  have hv := lifetimeVariance_le_occupation hkn (le_refl M) (Finset.univ : Finset (Assignment n))
  have ho := occupation_mono (k := k) (m := M)
    (fun S => truncatedKilling_le_forced hk hkn hL hM S) Finset.univ
  rw [occupation_const_mul, occupation_forced_eq] at ho
  have hmul := mul_le_mul_of_nonneg_left ho (by positivity : (0 : ℝ) ≤ 2 * M)
  nlinarith

end


end FixedClauseThreshold

end OAI
