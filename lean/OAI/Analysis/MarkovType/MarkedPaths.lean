import OAI.Analysis.MarkovType.MarkedChains
import OAI.Analysis.MarkovType.FinitePaths

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E]

def markedTransition (C : FiniteMarkedChain S E) (s t : S) : ℝ := by
  classical
  exact ∑ e, if C.src e = s ∧ C.tgt e = t then C.q e else 0

theorem markedTransition_nonneg (C : FiniteMarkedChain S E) (s t : S) :
    0 ≤ markedTransition C s t := by
  classical
  exact Finset.sum_nonneg fun e _ => by
    split_ifs
    · exact C.q_nonneg e
    · exact le_rfl

theorem sum_markedTransition (C : FiniteMarkedChain S E) (s : S) :
    ∑ t, markedTransition C s t = 1 := by
  classical
  unfold markedTransition
  rw [Finset.sum_comm]
  have h (e : E) :
      (∑ t, if C.src e = s ∧ C.tgt e = t then C.q e else 0) =
        if C.src e = s then C.q e else 0 := by
    by_cases hs : C.src e = s <;> simp [hs]
  simp_rw [h]
  exact C.sum_q s

theorem markedTransition_balance (C : FiniteMarkedChain S E) (s t : S) :
    C.π s * markedTransition C s t = C.π t * markedTransition C t s := by
  classical
  unfold markedTransition
  simp only [Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.ofBijective C.rev C.rev_rev.bijective)
  intro e
  change C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) =
    C.π t * (if C.src (C.rev e) = t ∧ C.tgt (C.rev e) = s then C.q (C.rev e) else 0)
  rw [C.src_rev, C.tgt_rev]
  by_cases hs : C.src e = s
  · by_cases ht : C.tgt e = t
    · simpa [hs, ht] using C.balance e
    · simp [hs, ht]
  · simp [hs]

def FiniteMarkedChain.toStateChain (C : FiniteMarkedChain S E) :
    FiniteReversibleChain S where
  π := C.π
  P := markedTransition C
  π_nonneg := C.π_nonneg
  sum_π := C.sum_π
  P_nonneg := markedTransition_nonneg C
  sum_P := sum_markedTransition C
  balance := markedTransition_balance C

@[simp] theorem markedState_zero (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) : markedState C ω 0 = ω.1 := by
  simp [markedState]

@[simp] theorem markedState_succ (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (i : Fin n) :
    markedState C ω i.succ = C.tgt (ω.2 i) := by
  simp [markedState]

def markedSnoc {n : ℕ} (ω : MarkedPath S E n) (e : E) : MarkedPath S E (n + 1) :=
  (ω.1, Fin.snoc ω.2 e)

theorem markedState_snoc_castSucc (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) (i : Fin (n + 1)) :
    markedState C (markedSnoc ω e) i.castSucc = markedState C ω i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [markedSnoc]
  · rw [← Fin.succ_castSucc]
    simp [markedSnoc]

theorem markedState_snoc (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) :
    markedState C (markedSnoc ω e) = Fin.snoc (markedState C ω) (C.tgt e) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change markedState C (markedSnoc ω e) (Fin.succ (Fin.last n)) = _
    rw [markedState_succ]
    simp only [markedSnoc, Fin.snoc_last]
  · simp only [markedState_snoc_castSucc, Fin.snoc_castSucc]

theorem markedValid_snoc (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) :
    markedValid C (markedSnoc ω e) ↔
      markedValid C ω ∧ C.src e = markedState C ω (Fin.last n) := by
  constructor
  · intro h
    constructor
    · intro i
      have hi := h i.castSucc
      rw [markedState_snoc_castSucc] at hi
      simpa only [markedSnoc, Fin.snoc_castSucc] using hi
    · have hi := h (Fin.last n)
      rw [markedState_snoc_castSucc] at hi
      simpa only [markedSnoc, Fin.snoc_last] using hi
  · rintro ⟨h, he⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [markedState_snoc_castSucc]
      simpa only [markedSnoc, Fin.snoc_last] using he
    · rw [markedState_snoc_castSucc]
      simpa only [markedSnoc, Fin.snoc_castSucc] using h j

theorem markedPathWeight_nonneg (C : FiniteMarkedChain S E) (n : ℕ)
    (ω : MarkedPath S E n) : 0 ≤ markedPathWeight C n ω := by
  classical
  unfold markedPathWeight
  split_ifs
  · exact mul_nonneg (C.π_nonneg _) (Finset.prod_nonneg fun i _ => C.q_nonneg _)
  · exact le_rfl

theorem markedPathWeight_eq_zero_of_not_valid (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (h : ¬markedValid C ω) : markedPathWeight C n ω = 0 := by
  simp [markedPathWeight, h]

theorem markedPathWeight_of_valid (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (h : markedValid C ω) :
    markedPathWeight C n ω = C.π ω.1 * ∏ i, C.q (ω.2 i) := by
  simp [markedPathWeight, h]

theorem markedPathWeight_snoc (C : FiniteMarkedChain S E) (n : ℕ)
    (ω : MarkedPath S E n) (e : E) :
    markedPathWeight C (n + 1) (markedSnoc ω e) =
      markedPathWeight C n ω *
        (if C.src e = markedState C ω (Fin.last n) then C.q e else 0) := by
  classical
  by_cases hv : markedValid C ω
  · by_cases he : C.src e = markedState C ω (Fin.last n)
    · have hve : markedValid C (markedSnoc ω e) := (markedValid_snoc C ω e).2 ⟨hv, he⟩
      rw [markedPathWeight_of_valid C (markedSnoc ω e) hve,
        markedPathWeight_of_valid C ω hv, ite_eq_left he]
      simp [markedSnoc, Fin.prod_univ_castSucc, mul_assoc]
    · simp [markedPathWeight, markedValid_snoc, hv, he]
  · simp [markedPathWeight, markedValid_snoc, hv]

theorem markedExpect_snoc (C : FiniteMarkedChain S E) (n : ℕ)
    (F : MarkedPath S E (n + 1) → ℝ) :
    markedExpect C (n + 1) F =
      ∑ ω : MarkedPath S E n, ∑ e,
        (markedPathWeight C n ω *
          (if C.src e = markedState C ω (Fin.last n) then C.q e else 0)) *
          F (markedSnoc ω e) := by
  classical
  unfold markedExpect
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => E)).sum_comp
    (fun w => markedPathWeight C (n + 1) (s, w) * F (s, w))]
  change (∑ z : E × (Fin n → E),
    markedPathWeight C (n + 1) (markedSnoc (s, z.2) z.1) *
      F (markedSnoc (s, z.2) z.1)) = _
  simp only [Fintype.sum_prod_type, markedPathWeight_snoc]
  exact Finset.sum_comm

theorem sum_markedPathWeight (C : FiniteMarkedChain S E) (n : ℕ) :
    ∑ ω : MarkedPath S E n, markedPathWeight C n ω = 1 := by
  classical
  induction n with
  | zero =>
      simpa [markedPathWeight, markedValid, Fintype.sum_prod_type] using C.sum_π
  | succ n ih =>
      have h := markedExpect_snoc C n (fun _ => 1)
      simp only [markedExpect, mul_one] at h
      rw [h]
      simp_rw [← Finset.mul_sum, C.sum_q, mul_one]
      exact ih

def markedLaw (C : FiniteMarkedChain S E) (n : ℕ) : FiniteLaw (MarkedPath S E n) where
  mass := markedPathWeight C n
  mass_nonneg := markedPathWeight_nonneg C n
  sum_mass := sum_markedPathWeight C n

theorem sum_outgoing_target (C : FiniteMarkedChain S E) (s : S) (H : S → ℝ) :
    (∑ e, (if C.src e = s then C.q e else 0) * H (C.tgt e)) =
      ∑ t, markedTransition C s t * H t := by
  classical
  unfold markedTransition
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : C.src e = s <;> simp [hs]

theorem markedExpect_state (C : FiniteMarkedChain S E) (n : ℕ)
    (F : StatePath S n → ℝ) :
    markedExpect C n (fun ω => F (markedState C ω)) =
      ∑ η : StatePath S n, pathWeight C.toStateChain n η * F η := by
  classical
  induction n with
  | zero =>
      let e : S ≃ StatePath S 0 :=
        { toFun := fun s _ => s
          invFun := fun ω => ω 0
          left_inv := fun _ => rfl
          right_inv := fun ω => funext fun i => congrArg ω (Fin.subsingleton_one.elim _ _) }
      have hz (s : S) (w : Fin 0 → E) :
          markedState C (s, w) = fun _ => s := by
        funext i
        have hi : i = 0 := Fin.subsingleton_one.elim _ _
        subst i
        exact markedState_zero C (s, w)
      rw [← e.sum_comp (fun η => pathWeight C.toStateChain 0 η * F η)]
      simp [markedExpect, Fintype.sum_prod_type, markedPathWeight,
        markedValid, hz, pathWeight, e, FiniteMarkedChain.toStateChain]
  | succ n ih =>
      calc
        _ = ∑ ω : MarkedPath S E n, ∑ e,
            (markedPathWeight C n ω *
              (if C.src e = markedState C ω (Fin.last n) then C.q e else 0)) *
              F (Fin.snoc (markedState C ω) (C.tgt e)) := by
          rw [markedExpect_snoc]
          simp only [markedState_snoc]
        _ = markedExpect C n (fun ω =>
            ∑ t, markedTransition C (markedState C ω (Fin.last n)) t *
              F (Fin.snoc (markedState C ω) t)) := by
          simp only [markedExpect, mul_assoc]
          simp_rw [← Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          congr 1
          exact sum_outgoing_target C (markedState C ω (Fin.last n))
            (fun t => F (Fin.snoc (markedState C ω) t))
        _ = ∑ η : StatePath S n, pathWeight C.toStateChain n η *
            (∑ t, markedTransition C (η (Fin.last n)) t * F (Fin.snoc η t)) :=
          ih (fun η => ∑ t, markedTransition C (η (Fin.last n)) t * F (Fin.snoc η t))
        _ = _ := by
          rw [sum_pathWeight_snoc]
          simp only [FiniteMarkedChain.toStateChain, Finset.mul_sum, mul_assoc]

def markedTake {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (ω : MarkedPath S E n) : MarkedPath S E k :=
  (ω.1, fun i => ω.2 (Fin.castLE hk i))

omit sectionFintypeS sectionFintypeE in
@[simp] theorem markedTake_self [Fintype S] [Fintype E] {n : ℕ} (ω : MarkedPath S E n) :
    markedTake n le_rfl ω = ω := by
  apply Prod.ext rfl
  funext i
  rfl

omit sectionFintypeS sectionFintypeE in
@[simp] theorem markedTake_snoc [Fintype S] [Fintype E] {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (ω : MarkedPath S E n) (e : E) :
    markedTake k (Nat.le_trans hk (Nat.le_succ n)) (markedSnoc ω e) =
      markedTake k hk ω := by
  apply Prod.ext
  · rfl
  · funext i
    change Fin.snoc (α := fun _ : Fin (n + 1) => E) ω.2 e (Fin.castLE hk i).castSucc = _
    exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => E) e ω.2 (Fin.castLE hk i)

theorem markedExpect_take (C : FiniteMarkedChain S E) {n : ℕ}
    (k : ℕ) (hk : k ≤ n) (H : MarkedPath S E k → ℝ) :
    markedExpect C n (fun ω => H (markedTake k hk ω)) = markedExpect C k H := by
  classical
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      by_cases hkn : k ≤ n
      · rw [markedExpect_snoc]
        simp only [markedTake_snoc k hkn, mul_assoc]
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul, C.sum_q, one_mul]
        exact ih k hkn H
      · have hnk : n + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hkn)
        have hk' : k = n + 1 := Nat.le_antisymm hk hnk
        subst k
        simp

theorem markedExpect_last_edge (C : FiniteMarkedChain S E) (n : ℕ) (H : E → ℝ) :
    markedExpect C (n + 1) (fun ω => H (ω.2 (Fin.last n))) =
      ∑ e, (C.π (C.src e) * C.q e) * H e := by
  classical
  let G : S → ℝ := fun s => ∑ e, (if C.src e = s then C.q e else 0) * H e
  calc
    _ = markedExpect C n (fun ω => G (markedState C ω (Fin.last n))) := by
      rw [markedExpect_snoc]
      simp only [markedSnoc, Fin.snoc_last, mul_assoc, markedExpect, G]
      simp_rw [← Finset.mul_sum]
    _ = ∑ η : StatePath S n, pathWeight C.toStateChain n η * G (η (Fin.last n)) :=
      markedExpect_state C n (fun η => G (η (Fin.last n)))
    _ = ∑ s, C.π s * G s := sum_pathWeight_last C.toStateChain n G
    _ = _ := by
      simp only [G, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simp [mul_ite, ite_mul, mul_assoc]

theorem markedExpect_edge (C : FiniteMarkedChain S E) (n : ℕ)
    (i : Fin n) (H : E → ℝ) :
    markedExpect C n (fun ω => H (ω.2 i)) =
      ∑ e, (C.π (C.src e) * C.q e) * H e := by
  have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  calc
    _ = markedExpect C n (fun ω =>
      (fun η : MarkedPath S E (i.val + 1) => H (η.2 (Fin.last i.val)))
        (markedTake (i.val + 1) hi ω)) := by rfl
    _ = markedExpect C (i.val + 1) (fun η => H (η.2 (Fin.last i.val))) :=
      markedExpect_take C (i.val + 1) hi
        (fun η : MarkedPath S E (i.val + 1) => H (η.2 (Fin.last i.val)))
    _ = _ := markedExpect_last_edge C i.val H

end MarkovSuperreflexivity

end

end OAI
