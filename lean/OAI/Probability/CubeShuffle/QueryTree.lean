import OAI.Probability.CubeShuffle.Basic
import OAI.Probability.CubeShuffle.ButterflyRoutes

namespace OAI

namespace CubeShuffle

open scoped BigOperators
open Filter

/-- A finite adaptive experiment. A `force` instruction aborts on the wrong bit;
it carries likelihood-ratio weight 2 on success. Ordinary queries have no cost.
Freshness is a theorem hypothesis BELOW ON THE ACTUAL QUERY TREE, not an
independence assumption about a subsequently selected event. -/
inductive QueryTree (ι : Type*)
  | reject : QueryTree ι
  | accept : QueryTree ι
  | branch (i : ι) (zero one : QueryTree ι) : QueryTree ι
  | force (i : ι) (b : Bool) (next : QueryTree ι) : QueryTree ι

namespace QueryTree

variable {ι : Type*} [DecidableEq ι]

def queries : QueryTree ι → Finset ι
  | reject => ∅
  | accept => ∅
  | branch i zero one => insert i (queries zero ∪ queries one)
  | force i _ next => insert i (queries next)

/-- No coin is requested twice along any branch of the experiment. -/
def Fresh : QueryTree ι → Prop
  | reject => True
  | accept => True
  | branch i zero one => i ∉ queries zero ∧ i ∉ queries one ∧ Fresh zero ∧ Fresh one
  | force i _ next => i ∉ queries next ∧ Fresh next

def weighted : QueryTree ι → (ι → Bool) → ℝ
  | reject, _ => 0
  | accept, _ => 1
  | branch i zero one, ω => if ω i then weighted one ω else weighted zero ω
  | force i b next, ω => if ω i = b then 2 * weighted next ω else 0

omit [DecidableEq ι] in
lemma weighted_nonneg (T : QueryTree ι) (ω : ι → Bool) : 0 ≤ T.weighted ω := by
  induction T with
  | reject => exact le_rfl
  | accept => exact zero_le_one
  | branch i zero one ih₀ ih₁ => simpa only [weighted] using ite_nonneg ih₁ ih₀
  | force i b next ih => simpa only [weighted] using ite_nonneg (mul_nonneg (by norm_num) ih) le_rfl

lemma weighted_congr (T : QueryTree ι) {ω η : ι → Bool}
    (h : ∀ i ∈ T.queries, ω i = η i) : T.weighted ω = T.weighted η := by
  induction T with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    have hi := h i (Finset.mem_insert_self _ _)
    simp only [weighted, hi]
    rw [ih₀ (fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_left _ hj))),
      ih₁ (fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_right _ hj)))]
  | force i b next ih =>
    have hi := h i (Finset.mem_insert_self _ _)
    simp only [weighted, hi]
    rw [ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

lemma weighted_flip_of_not_mem (T : QueryTree ι) (i : ι) (hi : i ∉ T.queries)
    (ω : ι → Bool) : T.weighted (flipCoin i ω) = T.weighted ω := by
  apply weighted_congr
  intro j hj
  exact flipCoin_apply_ne i j (fun h => hi (h ▸ hj)) ω

/-- Sequential forcing identity/inequality. Its weight is determined by the
realized trace; there is no conditioning on a favorable choice of certificate. -/
lemma mean_weighted_le_one [Fintype ι] (T : QueryTree ι) (hT : T.Fresh) :
    finiteMean T.weighted ≤ 1 := by
  induction T with
  | reject => simp [weighted, finiteMean]
  | accept => simp [weighted, finiteMean]
  | branch i zero one ih₀ ih₁ =>
    obtain ⟨hz, ho, hfz, hfo⟩ := hT
    have h₀ := mean_indicator_bit zero.weighted i false (zero.weighted_flip_of_not_mem i hz)
    have h₁ := mean_indicator_bit one.weighted i true (one.weighted_flip_of_not_mem i ho)
    have he : finiteMean (branch i zero one).weighted =
        finiteMean (fun ω => if ω i = false then zero.weighted ω else 0) +
        finiteMean (fun ω => if ω i = true then one.weighted ω else 0) := by
      unfold finiteMean
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      cases hω : ω i <;> simp [weighted, hω]
    rw [he, h₀, h₁]
    linarith [ih₀ hfz, ih₁ hfo]
  | force i b next ih =>
    obtain ⟨hi, hn⟩ := hT
    have hm := mean_indicator_bit next.weighted i b (next.weighted_flip_of_not_mem i hi)
    have he : finiteMean (force i b next).weighted =
        2 * finiteMean (fun ω => if ω i = b then next.weighted ω else 0) := by
      unfold finiteMean
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ω i = b <;> simp [weighted, h]
    rw [he, hm]
    linarith [ih hn]

def succeeds : QueryTree ι → (ι → Bool) → Bool
  | reject, _ => false
  | accept, _ => true
  | branch i zero one, ω => if ω i then succeeds one ω else succeeds zero ω
  | force i b next, ω => if ω i = b then succeeds next ω else false

/-- Number of successful forced fresh-bit queries along the realized trace. -/
def charge : QueryTree ι → (ι → Bool) → ℕ
  | reject, _ => 0
  | accept, _ => 0
  | branch i zero one, ω => if ω i then charge one ω else charge zero ω
  | force i b next, ω => if ω i = b then charge next ω + 1 else 0

omit [DecidableEq ι] in
lemma weighted_eq (T : QueryTree ι) (ω : ι → Bool) :
    T.weighted ω = if T.succeeds ω then (2 : ℝ) ^ T.charge ω else 0 := by
  induction T with
  | reject => rfl
  | accept => norm_num [weighted, succeeds, charge]
  | branch i zero one ih₀ ih₁ =>
    cases h : ω i <;> simp [weighted, succeeds, charge, h, ih₀, ih₁]
  | force i b next ih =>
    by_cases h : ω i = b
    · simp only [weighted, succeeds, charge, h, ↓reduceIte, ih]
      cases hs : next.succeeds ω <;> simp [pow_succ, mul_comm]
    · simp [weighted, succeeds, h]

/-- Acceptance probability is at most `2^(-K)` whenever every accepted trace
contains at least `K` forced fresh bits; unsuccessful shorter traces need not
make `K` queries. This is precisely the stopping-threshold issue in the fixed
certificate proof (`10-network.tex:84`). -/
lemma success_probability_le [Fintype ι] (T : QueryTree ι) (hT : T.Fresh)
    (K : ℕ) (hK : ∀ ω, T.succeeds ω = true → K ≤ T.charge ω) :
    finiteMean (fun ω => if T.succeeds ω then (1 : ℝ) else 0) ≤ 1 / (2 : ℝ) ^ K := by
  have hw (ω : ι → Bool) :
      (2 : ℝ) ^ K * (if T.succeeds ω then (1 : ℝ) else 0) ≤ T.weighted ω := by
    rw [weighted_eq]
    cases hs : T.succeeds ω
    · simp
    · simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (hK ω hs)
  have hn : 0 ≤ (Fintype.card (ι → Bool) : ℝ) := Nat.cast_nonneg _
  have hm := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hw ω)) hn
  rw [← Finset.mul_sum, mul_div_assoc] at hm
  change (2 : ℝ) ^ K * finiteMean (fun ω => if T.succeeds ω then 1 else 0) ≤
    finiteMean T.weighted at hm
  exact (le_div_iff₀ (pow_pos (by norm_num) K)).mpr (by
    rw [mul_comm]
    exact hm.trans (mean_weighted_le_one T hT))

end QueryTree

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

/-- Eliminate repeated queries against an explicit exposure record. Repeated
forced bits test compatibility but acquire no likelihood-ratio factor. -/
def memo : QueryTree ι → Finset ι → (ι → Bool) → QueryTree ι
  | reject, _, _ => reject
  | accept, _, _ => accept
  | branch i zero one, R, η =>
      if i ∈ R then (if η i then memo one R η else memo zero R η) else
      branch i (memo zero (insert i R) (Function.update η i false))
        (memo one (insert i R) (Function.update η i true))
  | force i b next, R, η =>
      if i ∈ R then (if η i = b then memo next R η else reject) else
      force i b (memo next (insert i R) (Function.update η i b))

lemma memo_queries_disjoint (T : QueryTree ι) (R : Finset ι) (η : ι → Bool) :
    Disjoint (memo T R η).queries R := by
  induction T generalizing R η with
  | reject => simp [memo,queries]
  | accept => simp [memo,queries]
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      cases η i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η
      · exact ih₁ R η
    · simp only [memo,hi,↓reduceIte,queries,Finset.disjoint_insert_left,Finset.disjoint_union_left]
      exact ⟨by simp, (ih₀ (insert i R) _).mono_right (Finset.subset_insert _ _),
        (ih₁ (insert i R) _).mono_right (Finset.subset_insert _ _)⟩
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      by_cases hb : η i = b
      · simpa only [hb,↓reduceIte] using ih R η
      · simp [hb,queries]
    · simp only [memo,hi,↓reduceIte,queries,Finset.disjoint_insert_left]
      exact ⟨by simp,(ih (insert i R) _).mono_right (Finset.subset_insert _ _)⟩

lemma memo_fresh (T : QueryTree ι) (R : Finset ι) (η : ι → Bool) :
    (memo T R η).Fresh := by
  induction T generalizing R η with
  | reject => trivial
  | accept => trivial
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      cases η i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η
      · exact ih₁ R η
    · simp only [memo,hi,↓reduceIte,Fresh]
      exact ⟨fun hm => Finset.disjoint_left.mp (memo_queries_disjoint zero (insert i R) _) hm
          (Finset.mem_insert_self _ _),
        fun hm => Finset.disjoint_left.mp (memo_queries_disjoint one (insert i R) _) hm
          (Finset.mem_insert_self _ _), ih₀ _ _,ih₁ _ _⟩
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      by_cases hb : η i = b
      · simpa only [hb,↓reduceIte] using ih R η
      · simp [hb,Fresh]
    · simp only [memo,hi,↓reduceIte,Fresh]
      exact ⟨fun hm => Finset.disjoint_left.mp (memo_queries_disjoint next (insert i R) _) hm
        (Finset.mem_insert_self _ _),ih _ _⟩

lemma update_agrees {R : Finset ι} {η ω : ι → Bool}
    (h : ∀ i ∈ R, η i = ω i) (i : ι) :
    ∀ j ∈ insert i R, Function.update η i (ω i) j = ω j := by
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simp
  · by_cases hji : j = i
    · subst j; simp
    · rw [Function.update_of_ne hji]
      exact h j hj

lemma memo_succeeds (T : QueryTree ι) (R : Finset ι) (η ω : ι → Bool)
    (h : ∀ i ∈ R, η i = ω i) : (memo T R η).succeeds ω = T.succeeds ω := by
  induction T generalizing R η with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,succeeds,h i hi]
      cases ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η h
      · exact ih₁ R η h
    · simp only [memo,hi,↓reduceIte,succeeds]
      cases hb : ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ _ _ (by simpa only [hb] using update_agrees h i)
      · exact ih₁ _ _ (by simpa only [hb] using update_agrees h i)
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,h i hi]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte,succeeds]
        exact ih R η h
      · simp [hb,succeeds]
    · simp only [memo,hi,↓reduceIte,succeeds]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        exact ih _ _ (by simpa only [hb] using update_agrees h i)
      · simp [hb]

/-- Forced bits counted only when fresh; ordinary path queries insert their
bits into the same record, so subsequent closures cannot charge them twice. -/
def freshCharge : QueryTree ι → Finset ι → (ι → Bool) → ℕ
  | reject, _, _ => 0
  | accept, _, _ => 0
  | branch i zero one, R, ω => if ω i then freshCharge one (insert i R) ω else freshCharge zero (insert i R) ω
  | force i b next, R, ω => if ω i = b then
      freshCharge next (insert i R) ω + (if i ∈ R then 0 else 1) else 0

lemma memo_charge (T : QueryTree ι) (R : Finset ι) (η ω : ι → Bool)
    (h : ∀ i ∈ R, η i = ω i) : (memo T R η).charge ω = freshCharge T R ω := by
  induction T generalizing R η with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,freshCharge,h i hi,Finset.insert_eq_of_mem hi]
      cases ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η h
      · exact ih₁ R η h
    · simp only [memo,hi,↓reduceIte,charge,freshCharge]
      cases hb : ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ _ _ (by simpa only [hb] using update_agrees h i)
      · exact ih₁ _ _ (by simpa only [hb] using update_agrees h i)
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,h i hi,freshCharge,Finset.insert_eq_of_mem hi,Nat.add_zero]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        exact ih R η h
      · simp [hb,charge]
    · simp only [memo,hi,↓reduceIte,charge,freshCharge]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        rw [ih _ _ (by simpa only [hb] using update_agrees h i)]
      · simp [hb]

/-- Adaptive weighted closing constraints remain valid with arbitrary repeated
ordinary/closing queries, after accounting exactly for exposed coins. -/
lemma mean_freshCharge_le_one [Fintype ι] (T : QueryTree ι) :
    finiteMean (fun ω : ι → Bool =>
      if T.succeeds ω then (2:ℝ) ^ T.freshCharge ∅ ω else 0) ≤ 1 := by
  let η : ι → Bool := fun _ => false
  have hm := mean_weighted_le_one (memo T ∅ η) (memo_fresh T ∅ η)
  have he : finiteMean (memo T ∅ η).weighted =
      finiteMean (fun ω : ι → Bool =>
        if T.succeeds ω then (2:ℝ) ^ T.freshCharge ∅ ω else 0) := by
    apply finiteMean_congr
    intro ω
    rw [weighted_eq, memo_succeeds _ _ _ _ (by simp), memo_charge _ _ _ _ (by simp)]
  rw [he] at hm
  exact hm

end QueryTree

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

/-- Query just the switches on one actual butterfly route, then pass its
endpoint to a continuation. The index map permits parallel sub-butterflies. -/
def followPath : (d : ℕ) → (SwitchIndex d → ι) → Card d →
    (Card d → QueryTree ι) → QueryTree ι
  | 0, _, x, k => k x
  | d + 1, e, x, k => followPath d (fun i => e (Sum.inr (x 0,i))) (Fin.tail x)
      (fun y => branch (e (Sum.inl y))
        (k (Fin.cons (Bool.xor (x 0) false) y))
        (k (Fin.cons (Bool.xor (x 0) true) y)))

omit [DecidableEq ι] in
lemma followPath_succeeds (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (ω : ι → Bool) :
    (followPath d e x k).succeeds ω =
      (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).succeeds ω := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    change (if ω (e (Sum.inl y)) then
      (k (Fin.cons (Bool.xor (x 0) true) y)).succeeds ω else
      (k (Fin.cons (Bool.xor (x 0) false) y)).succeeds ω) =
      (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).succeeds ω
    cases ω (e (Sum.inl y)) <;> rfl

lemma followPath_charge (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    freshCharge (followPath d e x k) R ω =
      freshCharge (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x))
        (R ∪ (routeDomain d x (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).image e) ω := by
  classical
  induction d generalizing R with
  | zero => simp only [followPath, routeDomain, Finset.image_empty, Finset.union_empty]; rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    let S := (routeDomain d (Fin.tail x) y).image (fun i => e (Sum.inr (x 0,i)))
    change (if ω (e (Sum.inl y)) then
      freshCharge (k (Fin.cons (Bool.xor (x 0) true) y)) (insert (e (Sum.inl y)) (R ∪ S)) ω else
      freshCharge (k (Fin.cons (Bool.xor (x 0) false) y)) (insert (e (Sum.inl y)) (R ∪ S)) ω) =
      freshCharge (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y))
        (R ∪ (routeDomain (d+1) x
          (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).image e) ω
    have hs : (routeDomain (d+1) x
        (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).image e =
        insert (e (Sum.inl y)) S := by
      let e' : Sum (Card d) (Bool × SwitchIndex d) → ι := e
      change (insert (Sum.inl y)
        ((routeDomain d (Fin.tail x) y).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
          Finset (Sum (Card d) (Bool × SwitchIndex d))).image e' = _
      rw [Finset.image_insert, Finset.image_image]
      rfl
    rw [hs,Finset.union_insert]
    cases ω (e (Sum.inl y)) <;> rfl

/-- Force a finite list of coin requirements; compatibility with previous
ordinary or forced queries is handled by `memo`. -/
def forceList : List ι → (ι → Bool) → QueryTree ι → QueryTree ι
  | [], _, k => k
  | i :: L, v, k => force i (v i) (forceList L v k)

omit [DecidableEq ι] in
lemma forceList_succeeds (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool) :
    (forceList L v k).succeeds ω =
      if ∀ i ∈ L, ω i = v i then k.succeeds ω else false := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    simp only [forceList,succeeds,ih,List.mem_cons,forall_eq_or_imp]
    by_cases h : ω i = v i <;> simp [h]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega

end QueryTree

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

/-- The number of forced queries already determined by earlier exposures. -/
def staleCharge : QueryTree ι → Finset ι → (ι → Bool) → ℕ
  | reject, _, _ => 0
  | accept, _, _ => 0
  | branch i zero one, R, ω => if ω i then staleCharge one (insert i R) ω
      else staleCharge zero (insert i R) ω
  | force i b next, R, ω => if ω i = b then
      staleCharge next (insert i R) ω + (if i ∈ R then 1 else 0) else 0

lemma fresh_add_stale (T : QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    T.freshCharge R ω + T.staleCharge R ω = T.charge ω := by
  induction T generalizing R with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    cases hb : ω i <;> simp [freshCharge,staleCharge,charge,hb,ih₀,ih₁]
  | force i b next ih =>
    by_cases hb : ω i = b
    · simp only [freshCharge,staleCharge,charge,hb,↓reduceIte]
      have he := ih (insert i R)
      by_cases hi : i ∈ R <;> simp only [hi,↓reduceIte] <;> omega
    · simp [freshCharge,staleCharge,charge,hb]

omit [DecidableEq ι] in
lemma followPath_raw_charge (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (ω : ι → Bool) :
    (followPath d e x k).charge ω =
      (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).charge ω := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    change (if ω (e (Sum.inl y)) then
      (k (Fin.cons (Bool.xor (x 0) true) y)).charge ω else
      (k (Fin.cons (Bool.xor (x 0) false) y)).charge ω) =
      (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).charge ω
    cases ω (e (Sum.inl y)) <;> rfl

omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

/-- A closing path has a specified endpoint rather than an adaptively chosen
one. It issues exactly the route's coin requirements. -/
noncomputable def closePath (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d)) :
    QueryTree (SwitchIndex d) :=
  forceList (routeDomain d x y).toList (routeValue d x y) k

lemma closePath_succeeds (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (ω : SwitchIndex d → Bool) :
    (closePath d x y k).succeeds ω =
      if butterflyPerm d (decodeButterfly d ω) x = y then k.succeeds ω else false := by
  unfold closePath
  rw [forceList_succeeds]
  simp only [Finset.mem_toList, ← butterfly_endpoint_iff]

lemma closePath_raw_charge (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (ω : SwitchIndex d → Bool) (h : butterflyPerm d (decodeButterfly d ω) x = y) :
    (closePath d x y k).charge ω = k.charge ω + d := by
  unfold closePath
  rw [forceList_raw_charge _ _ _ _ (by simpa only [Finset.mem_toList] using
    (butterfly_endpoint_iff d ω x y).mp h), Finset.length_toList, card_routeDomain]

lemma closePath_fresh_charge (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (R : Finset (SwitchIndex d)) (ω : SwitchIndex d → Bool)
    (h : butterflyPerm d (decodeButterfly d ω) x = y) :
    (closePath d x y k).freshCharge R ω =
      k.freshCharge (R ∪ routeDomain d x y) ω + (routeDomain d x y \ R).card := by
  unfold closePath
  rw [forceList_charge _ _ _ _ _ (by simpa only [Finset.mem_toList] using
    (butterfly_endpoint_iff d ω x y).mp h), Finset.toList_toFinset]

lemma closePath_stale_charge (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (R : Finset (SwitchIndex d)) (ω : SwitchIndex d → Bool)
    (h : butterflyPerm d (decodeButterfly d ω) x = y) :
    (closePath d x y k).staleCharge R ω =
      k.staleCharge (R ∪ routeDomain d x y) ω + (routeDomain d x y ∩ R).card := by
  have h₀ := fresh_add_stale (closePath d x y k) R ω
  have h₁ := fresh_add_stale k (R ∪ routeDomain d x y) ω
  rw [closePath_raw_charge _ _ _ _ _ h,closePath_fresh_charge _ _ _ _ _ _ h] at h₀
  have h₂ : (routeDomain d x y \ R).card + (routeDomain d x y ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_routeDomain]
  omega

/-- Inspect one proposed length-(r+1) cycle. Every queried input must be in S
and must not have appeared in an earlier slot or earlier in this cycle. -/
noncomputable def seekCycle (d : ℕ) (S : Finset (Card d)) (a : Card d) :
    ℕ → Card d → Finset (Card d) → (Finset (Card d) → QueryTree (SwitchIndex d)) →
      QueryTree (SwitchIndex d)
  | 0, x, V, k => if x ∈ S ∧ x ∉ V then closePath d x a (k (insert x V)) else reject
  | r + 1, x, V, k => if x ∈ S ∧ x ∉ V then followPath d id x
      (fun y => seekCycle d S a r y (insert x V) k) else reject

lemma seekCycle_raw_charge (d : ℕ) (S : Finset (Card d)) (a : Card d) (r : ℕ)
    (x : Card d) (V : Finset (Card d)) (k : Finset (Card d) → QueryTree (SwitchIndex d))
    (ω : SwitchIndex d → Bool) (K : ℕ)
    (hK : ∀ V, (k V).succeeds ω = true → (k V).charge ω = K)
    (hs : (seekCycle d S a r x V k).succeeds ω = true) :
    (seekCycle d S a r x V k).charge ω = K + d := by
  induction r generalizing x V with
  | zero =>
    by_cases hv : x ∈ S ∧ x ∉ V
    · rw [seekCycle,ite_eq_left hv,closePath_succeeds] at hs
      split_ifs at hs with he
      · rw [seekCycle,ite_eq_left hv,closePath_raw_charge _ _ _ _ _ he,hK _ hs]
    · simp [seekCycle,hv,succeeds] at hs
  | succ r ih =>
    by_cases hv : x ∈ S ∧ x ∉ V
    · rw [seekCycle,ite_eq_left hv,followPath_succeeds] at hs
      rw [seekCycle,ite_eq_left hv,followPath_raw_charge]
      exact ih _ _ hs
    · simp [seekCycle,hv,succeeds] at hs

/-- Distinguishable cycle slots, with each requested length encoded as r+1.
Later factorial-moment counting divides by precisely these rotation counts. -/
noncomputable def seekCycles (d : ℕ) (S : Finset (Card d)) :
    List (Card d × ℕ) → Finset (Card d) → QueryTree (SwitchIndex d)
  | [], _ => accept
  | (a,r) :: L, V => seekCycle d S a r a V (fun V => seekCycles d S L V)

lemma seekCycles_raw_charge (d : ℕ) (S : Finset (Card d)) (L : List (Card d × ℕ))
    (V : Finset (Card d)) (ω : SwitchIndex d → Bool)
    (hs : (seekCycles d S L V).succeeds ω = true) :
    (seekCycles d S L V).charge ω = L.length * d := by
  induction L generalizing V with
  | nil => simp [seekCycles,charge]
  | cons ar L ih =>
    obtain ⟨a,r⟩ := ar
    rw [seekCycles]
    rw [seekCycle_raw_charge d S a r a V (fun V => seekCycles d S L V) ω (L.length*d)
      (fun V hs => ih V hs) hs]
    simp [Nat.add_mul]

/-- The actual fixed-start weighted exploration inequality in FAC.3. The
stale charge counts exposed closing-path switches exactly, not a postulated
conditional-independence bound. Failure includes repeats, short cycles and
visiting outside the marked subset, and can occur at ANY earlier query. -/
lemma cycles_weighted_success (d : ℕ) (S : Finset (Card d)) (L : List (Card d × ℕ)) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      if (seekCycles d S L ∅).succeeds ω then
        ((2:ℝ)^d)^L.length / (2:ℝ)^(seekCycles d S L ∅).staleCharge ∅ ω else 0) ≤ 1 := by
  let T := seekCycles d S L ∅
  have hh := mean_freshCharge_le_one T
  have he : finiteMean (fun ω : SwitchIndex d → Bool =>
      if T.succeeds ω then (2:ℝ)^T.freshCharge ∅ ω else 0) =
      finiteMean (fun ω : SwitchIndex d → Bool =>
        if T.succeeds ω then ((2:ℝ)^d)^L.length / (2:ℝ)^T.staleCharge ∅ ω else 0) := by
    apply finiteMean_congr
    intro ω
    cases hs : T.succeeds ω
    · simp
    · simp only [↓reduceIte]
      have hc := fresh_add_stale T ∅ ω
      rw [seekCycles_raw_charge d S L ∅ ω hs] at hc
      have hp : ((2:ℝ)^d)^L.length = (2:ℝ)^T.freshCharge ∅ ω * (2:ℝ)^T.staleCharge ∅ ω := by
        rw [←pow_add,hc,←pow_mul,Nat.mul_comm]
      rw [hp,mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))]
  rw [← he]
  exact hh

end QueryTree

end CubeShuffle

end OAI
