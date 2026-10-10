import OAI.Combinatorics.BinaryEdit.FiniteTreeGeometry
import OAI.Combinatorics.BinaryEdit.FiniteVectorRestrictions
import OAI.Combinatorics.BinaryEdit.WordFinite

namespace OAI

/-! Instantiate the recursive word evaluator with the explicit finite state
group and subtree vectors. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- Total extension of a node prefix to a full leaf path. Its unused tail is
irrelevant to every vector at the depth of that prefix. -/
def extendPrefix {m k : ℕ} (i₀ : Fin m) (p : List (Fin m)) : Fin k → Fin m :=
  fun q => p.getD q.val i₀

theorem agrees_extendPrefix_iff {m k : ℕ} (i₀ : Fin m) (p : List (Fin m))
    (hp : p.length ≤ k) (l : Fin k → Fin m) :
    FiniteVectors.Agrees p.length (extendPrefix i₀ p) l ↔ p <+: List.ofFn l := by
  constructor
  · intro ha
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simpa using hp, ?_⟩
    intro j hj
    have h := ha ⟨j, lt_of_lt_of_le hj hp⟩ hj
    change l ⟨j, _⟩ = p.getD j i₀ at h
    rw [List.getD_eq_getElem p i₀ hj] at h
    simpa using h.symm
  · intro ha q hq
    have h := ha.getElem hq
    change l q = p.getD q.val i₀
    rw [List.getD_eq_getElem p i₀ hq]
    simpa using h.symm

theorem extendPrefix_leaf {m k : ℕ} (i₀ : Fin m) (p : List (Fin m))
    (hp : p.length = k) : extendPrefix i₀ p = leafEquiv m k ⟨p, hp⟩ := by
  funext q
  change p.getD q.val i₀ = p.get (q.cast hp.symm)
  exact List.getD_eq_get p i₀ (q.cast hp.symm)

theorem extendPrefix_append {m k : ℕ} (i₀ i : Fin m) (p : List (Fin m))
    (hp : p.length < k) :
    extendPrefix i₀ (p ++ [i]) = Function.update (extendPrefix i₀ p) ⟨p.length, hp⟩ i := by
  funext q
  by_cases hq : q.val < p.length
  · have hne : q ≠ ⟨p.length, hp⟩ := by intro he; subst q; simp at hq
    simp only [Function.update_of_ne hne, extendPrefix]
    exact List.getD_append p [i] i₀ q.val hq
  · have hq' : p.length ≤ q.val := Nat.le_of_not_gt hq
    by_cases he : q.val = p.length
    · have heq : q = ⟨p.length, hp⟩ := Fin.ext he
      subst q
      simp [extendPrefix, List.getD_eq_getElem?_getD]
    · have hne : q ≠ ⟨p.length, hp⟩ := by intro h; exact he (congrArg Fin.val h)
      simp only [Function.update_of_ne hne, extendPrefix]
      rw [List.getD_eq_default (p ++ [i]) i₀ (by simp; omega)]
      rw [List.getD_eq_default p i₀ hq']

/-- The actual leaf periods, in the list-path presentation used by the words. -/
def wordPeriods {m k : ℕ} (primes : Fin k → Fin m → ℕ) : Leaf m k → ℕ :=
  fun l => FiniteVectors.leafPeriod primes (leafEquiv m k l)

/-- Actual cheap subgroup vector at a list prefix. -/
def wordU {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (p : List (Fin m)) : State (wordPeriods primes) :=
  pullState (FiniteVectors.leafPeriod primes)
    (FiniteVectors.u primes p.length (extendPrefix i₀ p))

/-- Actual distinguished subgroup vector at a list prefix. -/
def wordW {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (p : List (Fin m)) : State (wordPeriods primes) :=
  pullState (FiniteVectors.leafPeriod primes)
    (FiniteVectors.w primes p.length (extendPrefix i₀ p))

/-- Prescribed period at a list prefix. -/
def wordPeriod {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (p : List (Fin m)) : ℕ :=
  FiniteVectors.prefixPeriod primes p.length (extendPrefix i₀ p)

/-- The concrete tree word at an arbitrary node. -/
def finiteWord {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    List (Symbol (wordPeriods primes)) :=
  nodeWord T (leafDecoder (wordPeriods primes) ⟨List.replicate k i₀, by simp⟩)
    (wordU primes i₀) h p x

@[simp] theorem finiteWord_length {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    (finiteWord primes i₀ T h p x).length = (m * T) ^ h := by
  simp [finiteWord]

@[simp] theorem ofFn_leafEquiv {m k : ℕ} (l : Leaf m k) :
    List.ofFn (leafEquiv m k l) = l.val := by
  rcases l with ⟨l, hl⟩
  subst k
  change List.ofFn l.get = l
  exact List.ofFn_get l

/-- Concrete vector restriction to a child in the list-path presentation. -/
theorem wordU_on_child {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (p : List (Fin m)) (hp : p.length < k)
    (l : Leaf m k) (hl : p ++ [i] <+: l.val) :
    wordU primes i₀ p l = wordW primes i₀ (p ++ [i]) l := by
  have hc : FiniteVectors.Agrees (p.length + 1)
      (Function.update (extendPrefix i₀ p) ⟨p.length, hp⟩ i) (leafEquiv m k l) := by
    have ha := (agrees_extendPrefix_iff i₀ (p ++ [i])
      (by simp; omega) (leafEquiv m k l)).2 (by simpa using hl)
    simpa [extendPrefix_append i₀ i p hp] using ha
  change FiniteVectors.u primes p.length (extendPrefix i₀ p) (leafEquiv m k l) =
    FiniteVectors.w primes (p ++ [i]).length (extendPrefix i₀ (p ++ [i])) (leafEquiv m k l)
  simpa [extendPrefix_append i₀ i p hp] using
    FiniteVectors.u_on_child primes p.length hp (extendPrefix i₀ p) (leafEquiv m k l) i hc

/-- Distinguished parent shift restricts to the current level product times
the distinguished child shift. -/
theorem wordW_on_child {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (p : List (Fin m)) (hp : p.length < k)
    (l : Leaf m k) (hl : p ++ [i] <+: l.val) :
    wordW primes i₀ p l =
      (FiniteVectors.levelProduct primes ⟨p.length, hp⟩ : ℤ) •
        wordW primes i₀ (p ++ [i]) l := by
  have h := congrFun (FiniteVectors.w_eq_level_nsmul_u primes p.length hp
    (extendPrefix i₀ p)) (leafEquiv m k l)
  change wordW primes i₀ p l =
    FiniteVectors.levelProduct primes ⟨p.length, hp⟩ • wordU primes i₀ p l at h
  rw [wordU_on_child primes i₀ i p hp l hl] at h
  simpa using h

@[simp] theorem wordW_leaf_self {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length = k) :
    wordW primes i₀ p ⟨p, hp⟩ = 1 := by
  change FiniteVectors.w primes p.length (extendPrefix i₀ p)
    (leafEquiv m k ⟨p, hp⟩) = 1
  rw [hp, extendPrefix_leaf i₀ p hp]
  simp [FiniteVectors.w_leaf]

@[simp] theorem wordPeriod_leaf {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length = k) :
    wordPeriod primes i₀ p = wordPeriods primes ⟨p, hp⟩ := by
  simp [wordPeriod, wordPeriods, hp, extendPrefix_leaf i₀ p hp,
    FiniteVectors.prefixPeriod, FiniteVectors.leafPeriod]

/-- The exact prescribed period annihilates the actual word's node vector. -/
theorem wordPeriod_nsmul_wordW {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) :
    wordPeriod primes i₀ p • wordW primes i₀ p = 0 := by
  funext l
  exact congrFun (FiniteVectors.prefixPeriod_nsmul_w primes p.length
    (extendPrefix i₀ p)) (leafEquiv m k l)

@[simp] theorem wordPeriod_root {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) :
    wordPeriod primes i₀ [] = 2 := by simp [wordPeriod]

@[simp] theorem wordU_off_subtree {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length ≤ k)
    (l : Leaf m k) (hl : ¬ p <+: l.val) : wordU primes i₀ p l = 0 := by
  have ha : ¬ FiniteVectors.Agrees p.length (extendPrefix i₀ p) (leafEquiv m k l) := by
    rw [agrees_extendPrefix_iff i₀ p hp, ofFn_leafEquiv]
    exact hl
  exact FiniteVectors.u_off_subtree primes p.length (extendPrefix i₀ p) (leafEquiv m k l) ha

@[simp] theorem wordW_off_subtree {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length ≤ k)
    (l : Leaf m k) (hl : ¬ p <+: l.val) : wordW primes i₀ p l = 0 := by
  have ha : ¬ FiniteVectors.Agrees p.length (extendPrefix i₀ p) (leafEquiv m k l) := by
    rw [agrees_extendPrefix_iff i₀ p hp, ofFn_leafEquiv]
    exact hl
  exact FiniteVectors.w_off_subtree primes p.length (extendPrefix i₀ p) (leafEquiv m k l) ha

/-- Base case of the separation proposition for the concrete word construction. -/
theorem finiteWord_leaf_deficit {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (T : ℕ) (p : List (Fin m)) (hp : p.length = k)
    (x : State (wordPeriods primes)) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    deficit 1 (finiteWord primes i₀ T 0 p x)
      (finiteWord primes i₀ T 0 p (x + t • wordW primes i₀ p)) = 1 := by
  apply leaf_deficit_of_not_dvd (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ p hp x (wordW primes i₀ p)
  · exact wordW_leaf_self primes i₀ p hp
  · simpa [wordPeriod_leaf primes i₀ p hp] using ht

/-- The actual relative child translation in any two rows of a node. -/
theorem finiteWord_child_relative {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (T h : ℕ) (p : List (Fin m))
    (hlen : p.length + (h + 1) = k) (x : State (wordPeriods primes))
    (t : ℤ) (a b : ℕ) :
    finiteWord primes i₀ T h (p ++ [i])
        (x + t • wordW primes i₀ p + b • wordU primes i₀ p) =
      finiteWord primes i₀ T h (p ++ [i])
        (x + a • wordU primes i₀ p +
          ((b : ℤ) - (a : ℤ) + t *
            (FiniteVectors.levelProduct primes ⟨p.length, by omega⟩ : ℤ)) •
              wordW primes i₀ (p ++ [i])) := by
  have hp : p.length < k := by omega
  apply child_relative_shift (wordPeriods primes) ⟨List.replicate k i₀, by simp⟩
    (wordU primes i₀) h (p ++ [i]) (by simp; omega)
  · intro l hl
    exact wordU_on_child primes i₀ i p hp l hl
  · intro l hl
    exact wordW_on_child primes i₀ i p hp l hl

/-- Positive prime entries make every cyclic leaf period positive. -/
theorem wordPeriods_pos {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (hpos : ∀ j i, 0 < primes j i) (l : Leaf m k) : 0 < wordPeriods primes l := by
  unfold wordPeriods FiniteVectors.leafPeriod
  exact Nat.mul_pos (by decide) (Finset.prod_pos fun j _ => hpos j _)

/-- The concrete parameter group is finite, not merely a formal product. -/
theorem finite_wordState {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (hpos : ∀ j i, 0 < primes j i) : Finite (State (wordPeriods primes)) := by
  let (l : Leaf m k) : NeZero (wordPeriods primes l) :=
    ⟨Nat.ne_of_gt (wordPeriods_pos primes hpos l)⟩
  infer_instance

/-- The actual tagged cyclic-state alphabet is finite. -/
theorem finite_wordSymbol {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (hpos : ∀ j i, 0 < primes j i) : Finite (Symbol (wordPeriods primes)) := by
  let (l : Leaf m k) : NeZero (wordPeriods primes l) :=
    ⟨Nat.ne_of_gt (wordPeriods_pos primes hpos l)⟩
  infer_instance

/-- Root words, retaining their exact common length in the type. -/
def rootWord {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (x : State (wordPeriods primes)) : Word (Symbol (wordPeriods primes)) ((m * T) ^ k) :=
  ⟨finiteWord primes i₀ T k [] x, finiteWord_length primes i₀ T k [] x⟩

end TreeEdit.BinaryLower.FiniteTree

end

end OAI
