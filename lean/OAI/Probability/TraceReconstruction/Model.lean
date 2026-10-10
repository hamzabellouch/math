import OAI.Probability.TraceReconstruction.FiniteLaw

namespace OAI

/-!
# Model

Independent deletion, complete trace observations, randomized estimators, ENNReal fixed-budget complexity, concatenation, and literal input words.
-/

open scoped ENNReal
noncomputable section

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Mask (n : ℕ) := Fin n → Bool
abbrev Trace := List Bool

/-- `true` retains the bit. The observer gets only the resulting list. -/
def traceOfMask {n : ℕ} (x : Word n) (a : Mask n) : Trace :=
  ((List.finRange n).filter fun i => a i).map x

/-- The deletion-mask probability, with deletion probability `q`. -/
def maskWeight {n : ℕ} (q : ℝ) (a : Mask n) : ℝ :=
  ∏ i, if a i then 1 - q else q

/-- Law of a single complete trace. -/
def traceMass {n : ℕ} (q : ℝ) (x : Word n) (w : Trace) : ℝ :=
  ∑ a : Mask n, if traceOfMask x a = w then maskWeight q a else 0

/-- All possible complete outputs from length-n inputs, with lengths included. -/
def traceSpace (n : ℕ) : Finset Trace :=
  Finset.univ.biUnion fun k : Fin (n + 1) =>
    Finset.univ.image fun x : Word k.val => List.ofFn x

/-- 1/2 sum of absolute differences, on the full finite output space. -/
def traceTV {n : ℕ} (q : ℝ) (x y : Word n) : ℝ :=
  (1 / 2 : ℝ) * ∑ w ∈ traceSpace n, |traceMass q x w - traceMass q y w|

/-- The estimator may depend arbitrarily on n, q and every complete sample.
    Its value is its conditional probability of reporting the given input. -/
def IsEstimator {n m : ℕ} (A : (Fin m → Trace) → Word n → ℝ) : Prop :=
  (∀ z x, 0 ≤ A z x) ∧ (∀ z, ∑ x : Word n, A z x = 1)

/-- Independent masks generate independent complete traces; no retained
    positions, boundaries or other latent variables are revealed to A. -/
def reconstructionSuccess {n m : ℕ} (q : ℝ)
    (A : (Fin m → Trace) → Word n → ℝ) (x : Word n) : ℝ :=
  ∑ a : Fin m → Mask n,
    (∏ j, maskWeight q (a j)) * A (fun j => traceOfMask x (a j)) x

def SufficientBudget (n : ℕ) (q s : ℝ) (m : ℕ) : Prop :=
  ∃ A : (Fin m → Trace) → Word n → ℝ,
    IsEstimator A ∧ ∀ x, s ≤ reconstructionSuccess q A x

/-- Natural fixed sample budget; infimum of the empty set is infinity. -/
noncomputable def sampleComplexity (n : ℕ) (q s : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ m : ℕ, SufficientBudget n q s m ∧ t = (m : ℝ≥0∞)}

/-- The real infimum is a minimum for n>0 (a nonempty finite set). -/
noncomputable def minTraceTV (n : ℕ) (q : ℝ) : ℝ :=
  sInf {t | ∃ x y : Word n, x ≠ y ∧ t = traceTV q x y}

end TraceReconstruction

noncomputable section

namespace TraceReconstruction




/-! ## Exact finite channel laws -/

theorem traceOfMask_length_le {n : ℕ} (x : Word n) (a : Mask n) :
    (traceOfMask x a).length ≤ n := by
  simpa [traceOfMask] using List.length_filter_le (fun i => a i) (List.finRange n)

theorem mem_traceSpace_of_length_le {n : ℕ} (w : Trace) (h : w.length ≤ n) :
    w ∈ traceSpace n := by
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨w.length, Nat.lt_succ_of_le h⟩, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem length_le_of_mem_traceSpace {n : ℕ} {w : Trace} (h : w ∈ traceSpace n) :
    w.length ≤ n := by
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hk
  simpa using Nat.le_of_lt_succ k.isLt

@[simp] theorem mem_traceSpace {n : ℕ} {w : Trace} :
    w ∈ traceSpace n ↔ w.length ≤ n :=
  ⟨length_le_of_mem_traceSpace, mem_traceSpace_of_length_le w⟩

theorem traceOfMask_mem {n : ℕ} (x : Word n) (a : Mask n) :
    traceOfMask x a ∈ traceSpace n :=
  mem_traceSpace_of_length_le _ (traceOfMask_length_le x a)

theorem maskWeight_nonneg {n : ℕ} {q : ℝ} (hq : q ∈ Set.Icc 0 1) (a : Mask n) :
    0 ≤ maskWeight q a := by
  apply Finset.prod_nonneg
  intro i _
  split <;> linarith [hq.1, hq.2]

@[simp] theorem sum_maskWeight {n : ℕ} (q : ℝ) :
    ∑ a : Mask n, maskWeight q a = 1 := by
  unfold maskWeight
  change (∑ a : Fin n → Bool, ∏ i, (fun (_ : Fin n) (b : Bool) =>
    if b then 1 - q else q) i (a i)) = 1
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then 1 - q else q)]
  simp

theorem traceMass_nonneg {n : ℕ} {q : ℝ} (hq : q ∈ Set.Icc 0 1)
    (x : Word n) (w : Trace) : 0 ≤ traceMass q x w := by
  apply Finset.sum_nonneg
  intro a _
  split
  · exact maskWeight_nonneg hq a
  · exact le_rfl

theorem traceMass_eq_zero_of_not_mem {n : ℕ} (q : ℝ) (x : Word n) (w : Trace)
    (hw : w ∉ traceSpace n) : traceMass q x w = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hne : traceOfMask x a ≠ w := by
    intro h
    exact hw (h ▸ traceOfMask_mem x a)
  simp [hne]

@[simp] theorem sum_traceMass {n : ℕ} (q : ℝ) (x : Word n) :
    ∑ w ∈ traceSpace n, traceMass q x w = 1 := by
  unfold traceMass
  rw [Finset.sum_comm]
  simp [traceOfMask_length_le]

theorem traceTV_nonneg {n : ℕ} (q : ℝ) (x y : Word n) : 0 ≤ traceTV q x y := by
  unfold traceTV
  positivity

@[simp] theorem traceTV_self {n : ℕ} (q : ℝ) (x : Word n) : traceTV q x x = 0 := by
  simp [traceTV]

theorem traceTV_comm {n : ℕ} (q : ℝ) (x y : Word n) : traceTV q x y = traceTV q y x := by
  simp only [traceTV, abs_sub_comm]

theorem traceTV_le_one {n : ℕ} {q : ℝ} (hq : q ∈ Set.Icc 0 1) (x y : Word n) :
    traceTV q x y ≤ 1 := by
  have h : ∑ w ∈ traceSpace n, |traceMass q x w - traceMass q y w| ≤
      ∑ w ∈ traceSpace n, (traceMass q x w + traceMass q y w) := by
    apply Finset.sum_le_sum
    intro w _
    exact abs_sub_le_iff.mpr
      ⟨by linarith [traceMass_nonneg hq y w], by linarith [traceMass_nonneg hq x w]⟩
  rw [Finset.sum_add_distrib, sum_traceMass, sum_traceMass] at h
  unfold traceTV
  linarith


end TraceReconstruction

namespace TraceReconstruction
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem ext {P Q : FiniteLaw α} (h : P.mass = Q.mass) : P = Q := by
  cases P with
  | mk pm pn pt => cases Q with
    | mk qm qn qt => cases h; rfl

noncomputable def pure (a : α) : FiniteLaw α := by
  classical
  exact ⟨(fun b => if a = b then 1 else 0),
    (fun b => by split_ifs <;> norm_num), by simp⟩

noncomputable def map (P : FiniteLaw α) (f : α → β) : FiniteLaw β :=
  P.bind (fun a => pure (f a))

theorem map_mass [DecidableEq β] (P : FiniteLaw α) (f : α → β) (b : β) :
    (P.map f).mass b = ∑ a, if f a = b then P.mass a else 0 := by
  classical
  unfold map bind pure
  simp only
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem expectation_map (P : FiniteLaw α) (f : α → β) (F : β → ℝ) :
    (∑ b, (P.map f).mass b * F b) = ∑ a, P.mass a * F (f a) := by
  classical
  simp_rw [map_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem tv_map_le (P Q : FiniteLaw α) (f : α → β) :
    tv (P.map f) (Q.map f) ≤ tv P Q := tv_bind_le P Q _

end FiniteLaw

abbrev BoundedTrace (n : ℕ) := ↥(traceSpace n)

def maskLaw {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) : FiniteLaw (Mask n) :=
  ⟨maskWeight q, maskWeight_nonneg hq, sum_maskWeight q⟩

def completeTraceLaw {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x : Word n) :
    FiniteLaw (BoundedTrace n) where
  mass w := traceMass q x w
  nonneg w := traceMass_nonneg hq x w
  total := by rw [Finset.sum_coe_sort]; exact sum_traceMass q x

theorem completeTraceLaw_tv {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x y : Word n) :
    (completeTraceLaw q hq x).tv (completeTraceLaw q hq y) = traceTV q x y := by
  change (1 / 2 : ℝ) * (∑ w : BoundedTrace n, |traceMass q x w - traceMass q y w|) = _
  rw [Finset.sum_coe_sort (traceSpace n) (fun w => |traceMass q x w - traceMass q y w|)]
  rfl

theorem completeTraceLaw_mask {n : ℕ} (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x : Word n) :
    completeTraceLaw q hq x =
      (maskLaw q hq).map (fun a : Mask n => ⟨traceOfMask x a, traceOfMask_mem x a⟩) := by
  apply FiniteLaw.ext
  funext w
  rw [FiniteLaw.map_mass]
  unfold completeTraceLaw traceMass maskLaw
  simp only
  apply Finset.sum_congr rfl
  intro a _
  rcases w with ⟨w, hw⟩
  simp only [Subtype.mk.injEq]

theorem trace_expectation {n : ℕ} (q : ℝ) (x : Word n) (F : Trace → ℝ) :
    (∑ w ∈ traceSpace n, traceMass q x w * F w) =
      ∑ a : Mask n, maskWeight q a * F (traceOfMask x a) := by
  classical
  unfold traceMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [traceOfMask_length_le]

/-- Concatenation of exact binary inputs, not an encoded surrogate. -/
def appendWord {n m : ℕ} (x : Word n) (y : Word m) : Word (n + m) := Fin.append x y

theorem trace_filterMap {n : ℕ} (x : Word n) (a : Mask n) :
    traceOfMask x a = (List.ofFn fun i => if a i then some (x i) else none).filterMap id := by
  have hlist (l : List (Fin n)) :
      (l.filter fun i => a i).map x = l.filterMap (fun i => if a i then some (x i) else none) := by
    induction l with
    | nil => rfl
    | cons i l ih => cases hai : a i <;> simp [hai, ih]
  unfold traceOfMask
  rw [hlist]
  have heq : (List.ofFn fun i => if a i then some (x i) else none) =
      (List.finRange n).map (fun i => if a i then some (x i) else none) := by
    rw [← List.ofFn_id, List.map_ofFn]
    rfl
  rw [heq, List.filterMap_map]
  rfl

theorem traceOfMask_append {n m : ℕ} (x : Word n) (y : Word m)
    (a : Mask n) (b : Mask m) :
    traceOfMask (appendWord x y) (Fin.append a b) = traceOfMask x a ++ traceOfMask y b := by
  rw [trace_filterMap, List.ofFn_add, List.filterMap_append, trace_filterMap, trace_filterMap]
  congr 2 <;> apply congrArg List.ofFn <;> funext i
  · change (if Fin.append a b (Fin.castAdd m i) then some (Fin.append x y (Fin.castAdd m i)) else none) = _
    simp
  · simp [appendWord]

theorem maskWeight_append {n m : ℕ} (q : ℝ) (a : Mask n) (b : Mask m) :
    maskWeight q (Fin.append a b) = maskWeight q a * maskWeight q b := by
  unfold maskWeight
  rw [Fin.prod_univ_add]
  simp

theorem concatenated_trace_expectation {n m : ℕ} (q : ℝ) (x : Word n) (y : Word m)
    (F : Trace → ℝ) :
    (∑ a : Mask (n + m), maskWeight q a * F (traceOfMask (appendWord x y) a)) =
      ∑ a : Mask n, ∑ b : Mask m,
        maskWeight q a * maskWeight q b * F (traceOfMask x a ++ traceOfMask y b) := by
  rw [← (Fin.appendEquiv n m).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change maskWeight q (Fin.append a b) * F (traceOfMask (appendWord x y) (Fin.append a b)) = _
  rw [maskWeight_append, traceOfMask_append]

end TraceReconstruction

namespace TraceReconstruction

/-- The four complete traces possible from the ordinary primitive `01`. -/
abbrev PrimitiveMark := Fin 4

def primitiveOutput : PrimitiveMark → List Bool := ![[], [false], [true], [false, true]]
def ordinaryPrimitiveMass (q : ℝ) : PrimitiveMark → ℝ :=
  ![q ^ 2, q * (1 - q), q * (1 - q), (1 - q) ^ 2]
def defectPrimitiveMass (q : ℝ) : PrimitiveMark → ℝ := ![q, 0, 1 - q, 0]
def primitiveErasure (q : ℝ) : ℝ := q ^ 2 / 2

def primitiveMarkMass (q : ℝ) (isDefect : Bool) (z : PrimitiveMark) : ℝ :=
  ((if isDefect then defectPrimitiveMass q z else ordinaryPrimitiveMass q z) -
    if z = 0 then primitiveErasure q else 0) / (1 - primitiveErasure q)

theorem primitive_retain_pos {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    0 < 1 - primitiveErasure q := by
  unfold primitiveErasure
  nlinarith [hq.1, hq.2]

theorem primitiveMarkMass_nonneg {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (b : Bool) (z : PrimitiveMark) : 0 ≤ primitiveMarkMass q b z := by
  apply div_nonneg _ (primitive_retain_pos hq).le
  cases b <;> fin_cases z <;>
    simp [ordinaryPrimitiveMass, defectPrimitiveMass, primitiveErasure] <;>
    nlinarith [hq.1, hq.2]

theorem primitiveMarkMass_sum {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (b : Bool) :
    ∑ z : PrimitiveMark, primitiveMarkMass q b z = 1 := by
  have hd := ne_of_gt (primitive_retain_pos hq)
  unfold primitiveMarkMass
  rw [← Finset.sum_div]
  apply (div_eq_one_iff_eq hd).mpr
  cases b <;> simp [ordinaryPrimitiveMass, defectPrimitiveMass, primitiveErasure, Fin.sum_univ_succ]
  all_goals ring

def primitiveMarkLaw (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (b : Bool) : FiniteLaw PrimitiveMark :=
  ⟨primitiveMarkMass q b, primitiveMarkMass_nonneg hq b, primitiveMarkMass_sum hq b⟩

/-- Emitting the conditional mark, or silently erasing the block, gives
exactly the ordinary primitive-output probabilities. Silent erasure and an
emitted empty mark are distinct latent events. -/
theorem primitiveMark_simulation {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (b : Bool) (z : PrimitiveMark) :
    (if z = 0 then primitiveErasure q else 0) +
      (1 - primitiveErasure q) * primitiveMarkMass q b z =
        if b then defectPrimitiveMass q z else ordinaryPrimitiveMass q z := by
  unfold primitiveMarkMass
  rw [mul_div_cancel₀ _ (ne_of_gt (primitive_retain_pos hq))]
  ring

def primitiveScore (q : ℝ) : PrimitiveMark → ℝ := ![2 / q - 2, -1, 1 / q - 1, -1]

theorem primitive_score_identity {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (z : PrimitiveMark) :
    primitiveMarkMass q true z = primitiveMarkMass q false z * (1 + primitiveScore q z) := by
  have hq0 := ne_of_gt hq.1
  have hd := ne_of_gt (primitive_retain_pos hq)
  fin_cases z <;>
    simp [primitiveMarkMass, ordinaryPrimitiveMass, defectPrimitiveMass, primitiveScore, primitiveErasure] <;>
    field_simp
  all_goals ring

theorem primitive_score_centered {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    ∑ z : PrimitiveMark, primitiveMarkMass q false z * primitiveScore q z = 0 := by
  have hi := primitiveMarkMass_sum hq true
  simp_rw [primitive_score_identity hq, mul_add, mul_one, Finset.sum_add_distrib,
    primitiveMarkMass_sum hq false] at hi
  linarith

theorem primitive_score_bound {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (z : PrimitiveMark) :
    |primitiveScore q z| ≤ 2 / q := by
  have hi : 1 ≤ 1 / q := (le_div_iff₀ hq.1).mpr (by linarith [hq.2])
  simp only [one_div] at hi
  have he : 2 / q = 2 * (1 / q) := by ring
  fin_cases z <;> simp [primitiveScore, abs_le, he] <;> (try constructor) <;> linarith

theorem primitive_score_variance_exact {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    (∑ z : PrimitiveMark, primitiveMarkMass q false z * primitiveScore q z ^ 2) =
      (1 / q - 2 * q + q ^ 2) / (1 - q ^ 2 / 2) := by
  have hq0 := ne_of_gt hq.1
  have hd := ne_of_gt (primitive_retain_pos hq)
  simp only [primitiveMarkMass, primitiveScore, ordinaryPrimitiveMass, primitiveErasure,
    Bool.false_eq_true, ↓reduceIte]
  simp [Fin.sum_univ_succ]
  field_simp
  ring

theorem primitive_score_variance_le {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    (∑ z : PrimitiveMark, primitiveMarkMass q false z * primitiveScore q z ^ 2) ≤ 2 / q := by
  rw [primitive_score_variance_exact hq]
  have hd : 0 < 1 - q ^ 2 / 2 := primitive_retain_pos hq
  apply (div_le_div_iff₀ hd hq.1).mpr
  rw [add_mul, sub_mul, one_div_mul_cancel (ne_of_gt hq.1)]
  have hpow : q ^ 3 ≤ q ^ 2 := by
    calc
      _ = q ^ 2 * q := by ring
      _ ≤ q ^ 2 * 1 := mul_le_mul_of_nonneg_left hq.2.le (sq_nonneg _)
      _ = _ := mul_one _
  nlinarith only [hpow, sq_nonneg q]

end TraceReconstruction

namespace TraceReconstruction
def ordinaryRun : ℕ → List Bool
  | 0 => []
  | m + 1 => false :: true :: ordinaryRun m

@[simp] theorem ordinaryRun_length (m : ℕ) : (ordinaryRun m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [ordinaryRun, List.length_cons, ih]; omega

theorem ordinaryRun_add (a b : ℕ) : ordinaryRun (a + b) = ordinaryRun a ++ ordinaryRun b := by
  induction a with
  | zero => simp [ordinaryRun]
  | succ a ih => simp [Nat.succ_add, ordinaryRun, ih]

/-- A period of m primitives with its unique `1` defect at zero-based slot d. -/
def initialPeriod (m d : ℕ) : List Bool :=
  ordinaryRun d ++ [true] ++ ordinaryRun (m - 1 - d)

theorem initialPeriod_length {m d : ℕ} (hd : d < m) :
    (initialPeriod m d).length = 2 * m - 1 := by
  simp only [initialPeriod, List.length_append, ordinaryRun_length, List.length_singleton]
  omega

/-- Distinct defect slots differ before either period ends, independently of future text. -/
theorem initialPeriod_tail_ne {m d e : ℕ} (hde : d < e) (he : e < m)
    (u v : List Bool) : initialPeriod m d ++ u ≠ initialPeriod m e ++ v := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (show d + 1 ≤ e by omega)
  subst e
  unfold initialPeriod
  rw [Nat.add_assoc d 1 a, ordinaryRun_add d (1 + a)]
  simp only [Nat.add_assoc] at *
  simp only [Nat.one_add, ordinaryRun, List.append_assoc, List.cons_append, List.nil_append]
  intro h
  have hh := List.append_cancel_left h
  have hf := congrArg List.head? hh
  simp only [List.head?_cons, Option.some.injEq] at hf
  cases hf

theorem initialPeriod_injective (m : ℕ) :
    Function.Injective (fun d : Fin m => initialPeriod m d) := by
  intro d e h
  by_contra hne
  have hv : d.val ≠ e.val := fun hv => hne (Fin.ext hv)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact initialPeriod_tail_ne hlt e.isLt [] [] (by simpa using h)
  · exact initialPeriod_tail_ne hgt d.isLt [] [] (by simpa using h.symm)

def periodString (m P : ℕ) (d : Fin P → Fin m) : List Bool :=
  (List.ofFn (fun i => initialPeriod m (d i))).flatten

theorem periodString_cons (m P : ℕ) (d : Fin (P + 1) → Fin m) :
    periodString m (P + 1) d = initialPeriod m (d 0) ++
      periodString m P (fun i => d i.succ) := by
  simp only [periodString, List.ofFn_succ, List.flatten_cons]

theorem periodString_length (m P : ℕ) (d : Fin P → Fin m) :
    (periodString m P d).length = P * (2 * m - 1) := by
  induction P with
  | zero => simp [periodString]
  | succ P ih =>
    rw [periodString_cons, List.length_append, initialPeriod_length (d 0).isLt, ih]
    rw [Nat.add_mul, one_mul, Nat.add_comm]

theorem periodString_injective (m P : ℕ) : Function.Injective (periodString m P) := by
  induction P with
  | zero => intro d e _; exact Subsingleton.elim _ _
  | succ P ih =>
    intro d e h
    rw [periodString_cons, periodString_cons] at h
    have hz : d 0 = e 0 := by
      by_contra hne
      have hv : (d 0).val ≠ (e 0).val := fun hv => hne (Fin.ext hv)
      rcases lt_or_gt_of_ne hv with hlt | hgt
      · exact initialPeriod_tail_ne hlt (e 0).isLt _ _ h
      · exact initialPeriod_tail_ne hgt (d 0).isLt _ _ h.symm
    rw [hz] at h
    have ht := ih (List.append_cancel_left h)
    funext i
    refine Fin.cases hz (fun j => congrFun ht j) i
end TraceReconstruction

namespace TraceReconstruction
/-- Uniformly sized binary atoms concatenated without boundary marks. -/
def atomString (P : ℕ) (w : Bool → List Bool) (θ : Fin P → Bool) : List Bool :=
  (List.ofFn (fun i => w (θ i))).flatten

theorem atomString_cons (P : ℕ) (w : Bool → List Bool) (θ : Fin (P + 1) → Bool) :
    atomString (P + 1) w θ = w (θ 0) ++ atomString P w (fun i => θ i.succ) := by
  simp only [atomString, List.ofFn_succ, List.flatten_cons]

theorem atomString_length (P S : ℕ) (w : Bool → List Bool) (hw : ∀ b, (w b).length = S)
    (θ : Fin P → Bool) : (atomString P w θ).length = P * S := by
  induction P with
  | zero => simp [atomString]
  | succ P ih => rw [atomString_cons, List.length_append, hw, ih, Nat.add_mul, one_mul, Nat.add_comm]

theorem atomString_injective (P S : ℕ) (w : Bool → List Bool)
    (hw : ∀ b, (w b).length = S) (hinj : Function.Injective w) :
    Function.Injective (atomString P w) := by
  induction P with
  | zero => intro θ φ _; exact Subsingleton.elim _ _
  | succ P ih =>
    intro θ φ h
    rw [atomString_cons, atomString_cons] at h
    have hh := congrArg (List.take S) h
    have hθ (u : List Bool) (b : Bool) : (w b ++ u).take S = w b := by
      rw [← hw b, List.take_left]
    rw [hθ, hθ] at hh
    have hz := hinj hh
    rw [hz] at h
    have ht := ih (List.append_cancel_left h)
    funext i
    exact Fin.cases hz (fun j => congrFun ht j) i

/-- Zero-based notation for the source complementary template; `true` is minus.
The motif itself is fixed independently of the hypothesis. -/
def templateType (P a L : ℕ) (sign : Fin L → Bool) (τ : Bool) (i : Fin P) : Bool :=
  if h : a ≤ i.val ∧ i.val < a + L then xor τ (sign ⟨i.val - a, by omega⟩) else false

theorem templateType_at (P a L : ℕ) (sign : Fin L → Bool) (τ : Bool)
    (hL : 0 < L) (ha : a < P) :
    templateType P a L sign τ ⟨a, ha⟩ = xor τ (sign ⟨0, hL⟩) := by
  simp [templateType, hL]

theorem templateType_injective (P a L : ℕ) (sign : Fin L → Bool)
    (hL : 0 < L) (ha : a < P) :
    Function.Injective (templateType P a L sign) := by
  intro τ υ h
  have he := congrFun h ⟨a, ha⟩
  rw [templateType_at P a L sign τ hL ha, templateType_at P a L sign υ hL ha] at he
  cases hs : sign ⟨0, hL⟩ <;> cases τ <;> cases υ <;> simp_all

def complementaryWords (P a L : ℕ) (sign : Fin L → Bool) (w : Bool → List Bool)
    (τ : Bool) : List Bool := atomString P w (templateType P a L sign τ)

theorem complementaryWords_length (P a L S : ℕ) (sign : Fin L → Bool)
    (w : Bool → List Bool) (hw : ∀ b, (w b).length = S) (τ : Bool) :
    (complementaryWords P a L sign w τ).length = P * S := atomString_length P S w hw _

theorem complementaryWords_injective (P a L S : ℕ) (sign : Fin L → Bool)
    (w : Bool → List Bool) (hw : ∀ b, (w b).length = S) (hinj : Function.Injective w)
    (hL : 0 < L) (ha : a < P) : Function.Injective (complementaryWords P a L sign w) :=
  (atomString_injective P S w hw hinj).comp (templateType_injective P a L sign hL ha)
end TraceReconstruction

end
end
end

end OAI
