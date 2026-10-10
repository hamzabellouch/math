import OAI.Combinatorics.ContingencyTables.Transport.LabelledFactorial

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures LabelledFactorial

variable {P C : Type*} [Fintype P] [Fintype C]

def group (cell : P → C) (i : P × Bool) : C × Bool := (cell i.1,i.2)

def pair (p : P) : (P × Bool) × (P × Bool) := ((p,false),(p,true))

noncomputable def pairs : List ((P × Bool) × (P × Bool)) :=
  Finset.univ.toList.map pair

noncomputable def width (cell : P → C) (c : C) : ℕ :=
  (Finset.univ.filter (fun p => cell p=c)).card

noncomputable def viewCount (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) : ℕ :=
  ∑ p, if cell p=c ∧ (p,t) ∈ S then 1 else 0

noncomputable def occupancy (S : Set (P × Bool)) (p : P) : ℕ :=
  (if (p,false) ∈ S then 1 else 0) + (if (p,true) ∈ S then 1 else 0)

lemma pair_mem (p : P) : pair p ∈ (pairs : List ((P × Bool) × (P × Bool))) := by
  simp [pairs]

omit [Fintype P] in
lemma pair_injective : Function.Injective (pair : P → (P × Bool) × (P × Bool)) := by
  intro p q h
  exact congrArg (fun x => x.1.1) h

omit [Fintype C] in
lemma groupCount_eq_viewCount (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) :
    groupCount (group cell) S (c,t) = viewCount cell S c t := by
  unfold groupCount viewCount
  rw [Finset.card_filter]
  simp only [Fintype.sum_prod_type,group,Prod.mk.injEq,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro p _
  cases t <;> simp [and_comm]

omit [Fintype C] in
lemma width_eq_sum (cell : P → C) (c : C) :
    width cell c = ∑ p, if cell p=c then 1 else 0 := Finset.card_filter _ _

omit [Fintype C] in
lemma viewCount_compl (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) :
    viewCount cell S c t + viewCount cell Sᶜ c t = width cell c := by
  rw [width_eq_sum]
  unfold viewCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : cell p=c <;> by_cases hs : (p,t) ∈ S <;> simp [hc,hs]

omit [Fintype C] in
lemma viewCount_le_width (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) :
    viewCount cell S c t ≤ width cell c := by
  have := viewCount_compl cell S c t
  omega

omit [Fintype C] in
lemma viewCounts_eq_occupancy (cell : P → C) (S : Set (P × Bool)) (c : C) :
    viewCount cell S c false + viewCount cell S c true =
      ∑ p, if cell p=c then occupancy S p else 0 := by
  unfold viewCount occupancy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : cell p=c <;> simp [hc]

omit [Fintype P] in
lemma occupancy_single (S : Set (P × Bool)) (p : P) (h : PairSingle (pair p) S) :
    occupancy S p = 1 := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [occupancy,pair] at ha hb ⊢ <;> simp [ha,hb]

omit [Fintype P] in
lemma occupancy_empty (S : Set (P × Bool)) (p : P) (h : PairEmpty (pair p) S) :
    occupancy S p = 0 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

omit [Fintype P] in
lemma occupancy_full (S : Set (P × Bool)) (p : P) (h : PairFull (pair p) S) :
    occupancy S p = 2 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

omit [Fintype C] in
/-- Every actual plain state is balanced in every physical cell. -/
theorem plain_counts (cell : P → C) (S : Set (P × Bool))
    (hS : PlainState pairs S) (c : C) :
    viewCount cell S c false + viewCount cell S c true = width cell c := by
  rw [viewCounts_eq_occupancy,width_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [occupancy_single S p (hS _ (pair_mem p))]

lemma defect_occupancy (S : Set (P × Bool)) (p q : P)
    (hS : DefectState pairs (pair p) (pair q) S) (k : P) :
    occupancy S k + (if k=p then 1 else 0) = 1 + (if k=q then 1 else 0) := by
  have hpq : p ≠ q := fun h => hS.2.2.1 (congrArg pair h)
  by_cases hkp : k=p
  · subst k
    rw [occupancy_empty S p hS.2.2.2.1]
    simp [hpq]
  · by_cases hkq : k=q
    · subst k
      rw [occupancy_full S q hS.2.2.2.2.1]
      simp [hkp]
    · rw [occupancy_single S k (hS.2.2.2.2.2 _ (pair_mem k)
        (fun h => hkp (pair_injective h)) (fun h => hkq (pair_injective h)))]
      simp [hkp,hkq]

omit [Fintype C] in
/-- Cell occupancies of an actual defect have exactly one unit missing at
its hole and one unit extra at its full pair, including coinciding cells. -/
theorem defect_counts (cell : P → C) (S : Set (P × Bool)) (p q : P)
    (hS : DefectState pairs (pair p) (pair q) S) (c : C) :
    viewCount cell S c false + viewCount cell S c true + (if cell p=c then 1 else 0) =
      width cell c + (if cell q=c then 1 else 0) := by
  have hs : (∑ k, if cell k=c then occupancy S k + (if k=p then 1 else 0) else 0) =
      ∑ k, if cell k=c then 1 + (if k=q then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [defect_occupancy S p q hS k]
  have hd (u v : P → ℕ) : (∑ k, if cell k=c then u k+v k else 0) =
      (∑ k, if cell k=c then u k else 0)+(∑ k, if cell k=c then v k else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> rfl
  rw [hd,hd] at hs
  have he (a : P) : (∑ k, if cell k=c then (if k=a then (1:ℕ) else 0) else 0) =
      if cell a=c then 1 else 0 := by
    calc
      _ = ∑ k, if k=a then (if cell k=c then 1 else 0) else 0 := by
        apply Finset.sum_congr rfl; intro k _; split_ifs <;> rfl
      _ = _ := by simp
  rw [he p,he q,← width_eq_sum,← viewCounts_eq_occupancy] at hs
  exact hs

noncomputable def denominator (cell : P → C) : ℝ := ∏ c, ((width cell c).factorial : ℝ)

lemma firstLift_eq_cells (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ) (S : Set (P × Bool)) :
    firstLift (group cell) h (denominator cell) S =
      h (groupCount (group cell) S) *
        ∏ c, cellFactor (width cell c) (viewCount cell S c false) (viewCount cell S c true) := by
  unfold firstLift factorialProduct denominator cellFactor
  simp only [Fintype.prod_prod_type,Fintype.prod_bool,groupCount_eq_viewCount]
  simp only [Finset.prod_div_distrib,Finset.prod_mul_distrib]
  ring

lemma secondLift_eq_cells (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ) (S : Set (P × Bool)) :
    secondLift (group cell) h (denominator cell) S =
      h (groupCount (group cell) S) *
        ∏ c, complementCellFactor (width cell c) (viewCount cell S c false) (viewCount cell S c true) := by
  have he (c : C) (t : Bool) : groupCount (group cell) Sᶜ (c,t) =
      width cell c - viewCount cell S c t := by
    rw [groupCount_eq_viewCount]
    have := viewCount_compl cell S c t
    omega
  unfold secondLift factorialProduct denominator complementCellFactor
  simp only [Fintype.prod_prod_type,Fintype.prod_bool,he]
  simp only [Finset.prod_div_distrib,Finset.prod_mul_distrib]
  ring

/-- Exact agreement of the two literal subset lifts on every plain state. -/
theorem plain_lifts_agree (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : PlainState pairs S) :
    secondLift (group cell) h (denominator cell) S = firstLift (group cell) h (denominator cell) S := by
  rw [firstLift_eq_cells,secondLift_eq_cells]
  exact balanced_lift_agreement _ _ _ (plain_counts cell S hS) _

/-- The paper's exact W² comparison on every actual defect state. -/
theorem defect_lifts_compare (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : ∃ p q, DefectState pairs (pair p) (pair q) S)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ c, width cell c < W)
    (hh : 0 ≤ h (groupCount (group cell) S)) :
    (1/(W:ℝ)^2) * firstLift (group cell) h (denominator cell) S ≤
        secondLift (group cell) h (denominator cell) S ∧
    secondLift (group cell) h (denominator cell) S ≤
        (W:ℝ)^2 * firstLift (group cell) h (denominator cell) S := by
  obtain ⟨p,q,hS⟩ := hS
  rw [firstLift_eq_cells,secondLift_eq_cells]
  by_cases hpq : cell p=cell q
  · have hbal (c : C) : viewCount cell S c false + viewCount cell S c true = width cell c := by
      have ht := defect_counts cell S p q hS c
      rw [hpq] at ht
      omega
    rw [balanced_lift_agreement _ _ _ hbal]
    have hf : 0 ≤ h (groupCount (group cell) S) *
        ∏ c, cellFactor (width cell c) (viewCount cell S c false) (viewCount cell S c true) :=
      mul_nonneg hh (Finset.prod_nonneg fun _ _ => (cellFactor_positive _ _ _).le)
    have hWr : (1:ℝ) ≤ W := by exact_mod_cast hW
    have hsq : (1:ℝ) ≤ (W:ℝ)^2 := by nlinarith
    constructor
    · exact mul_le_of_le_one_left hf ((div_le_one (by positivity)).mpr hsq)
    · exact le_mul_of_one_le_left hf hsq
  · apply defect_lift_comparison _ _ _ (cell p) (cell q) hpq W hW hbW
      (fun c => viewCount_le_width cell S c false) (fun c => viewCount_le_width cell S c true)
    · have ht := defect_counts cell S p q hS (cell p)
      simpa [hpq,Ne.symm hpq] using ht
    · have ht := defect_counts cell S p q hS (cell q)
      simpa [hpq] using ht
    · intro c hcp hcq
      have ht := defect_counts cell S p q hS c
      simpa [Ne.symm hcp,Ne.symm hcq] using ht
    · exact hh

lemma denominator_positive (cell : P → C) : 0 < denominator cell := by
  apply Finset.prod_pos
  intro c _
  exact_mod_cast Nat.factorial_pos (width cell c)

lemma firstLift_nonnegative (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hh : 0 ≤ h (groupCount (group cell) S)) :
    0 ≤ firstLift (group cell) h (denominator cell) S := by
  rw [firstLift_eq_cells]
  exact mul_nonneg hh (Finset.prod_nonneg fun _ _ => (cellFactor_positive _ _ _).le)

/-- Both inequalities hold on every actual chain state, with no extra
assumption about which cells contain the hole and full pair. -/
theorem chain_lifts_compare (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : ChainState pairs S)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ c, width cell c < W)
    (hh : 0 ≤ h (groupCount (group cell) S)) :
    (1/(W:ℝ)^2) * firstLift (group cell) h (denominator cell) S ≤
        secondLift (group cell) h (denominator cell) S ∧
    secondLift (group cell) h (denominator cell) S ≤
        (W:ℝ)^2 * firstLift (group cell) h (denominator cell) S := by
  rcases hS with hS | ⟨p,q,hS⟩
  · rw [plain_lifts_agree cell h S hS]
    have hf := firstLift_nonnegative cell h S hh
    have hWr : (1:ℝ) ≤ W := by exact_mod_cast hW
    have hsq : (1:ℝ) ≤ (W:ℝ)^2 := by nlinarith
    constructor
    · exact mul_le_of_le_one_left hf ((div_le_one (by positivity)).mpr hsq)
    · exact le_mul_of_one_le_left hf hsq
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show p ∈ Finset.univ.toList.map pair from hS.1)
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp (show q ∈ Finset.univ.toList.map pair from hS.2.1)
    exact defect_lifts_compare cell h S ⟨a,b,hS⟩ W hW hbW hh

/-- The pointwise comparison used by the actual original-chain variance
argument is supplied by the factorial state counts. -/
theorem firstLift_le_square_secondLift (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : ChainState pairs S)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ c, width cell c < W)
    (hh : 0 ≤ h (groupCount (group cell) S)) :
    firstLift (group cell) h (denominator cell) S ≤
        (W:ℝ)^2 * secondLift (group cell) h (denominator cell) S := by
  have hl := (chain_lifts_compare cell h S hS W hW hbW hh).1
  have hp : (0:ℝ) < (W:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hW)
  have hdiv : firstLift (group cell) h (denominator cell) S/(W:ℝ)^2 ≤
      secondLift (group cell) h (denominator cell) S := by
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using hl
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hdiv

end ContingencyTables.TwoLiftStates

end OAI
