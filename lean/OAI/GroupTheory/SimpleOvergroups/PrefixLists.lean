import Mathlib
import OAI.GroupTheory.FiniteType.ProductGroupHomology
import OAI.GroupTheory.SimpleOvergroups.PrefixArithmetic

namespace OAI


namespace BinaryPrefixOperators.Arithmetic
namespace Lists

abbrev Poly (K : Type*) := List (K × Pair)

variable {K : Type*} [CommRing K]

noncomputable def toArray : Poly K → (Pair →₀ K)
  | [] => 0
  | (a,p) :: ps => Finsupp.single p a + toArray ps

@[simp] theorem toArray_nil : toArray ([] : Poly K) = 0 := rfl
@[simp] theorem toArray_cons (a : K) (p : Pair) (ps : Poly K) :
    toArray ((a,p)::ps) = Finsupp.single p a + toArray ps := rfl
@[simp] theorem toArray_append (p q : Poly K) : toArray (p++q) = toArray p + toArray q := by
  induction p with
  | nil => simp
  | cons x p ih => rcases x with ⟨a,x⟩; simp [ih, add_assoc]

def coefficient (p : Poly K) (q : Pair) : K :=
  p.foldr (fun x a => (if x.2 = q then x.1 else 0) + a) 0

@[simp] theorem coefficient_nil (q : Pair) : coefficient ([] : Poly K) q = 0 := rfl
@[simp] theorem coefficient_cons (a : K) (p q : Pair) (ps : Poly K) :
    coefficient ((a,p)::ps) q = (if p=q then a else 0) + coefficient ps q := rfl

theorem coefficient_eq (p : Poly K) (q : Pair) : coefficient p q = toArray p q := by
  induction p with
  | nil => rfl
  | cons x p ih => rcases x with ⟨a,x⟩; simp [ih, Finsupp.single_apply]

theorem coefficient_eq_zero_of_not_mem (p : Poly K) (q : Pair)
    (h : ∀ a, (a,q) ∉ p) : coefficient p q = 0 := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    rcases x with ⟨a,x⟩
    have hne : x ≠ q := by intro he; exact h a (by simp [he])
    rw [coefficient_cons, ite_eq_right hne, zero_add]
    exact ih (by intro b hb; exact h b (by simp [hb]))

def isZero [DecidableEq K] (p : Poly K) : Bool :=
  p.all (fun q => decide (coefficient p q.2 = 0))

theorem isZero_iff [DecidableEq K] (p : Poly K) : isZero p = true ↔ toArray p = 0 := by
  rw [isZero, List.all_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    ext q
    rw [← coefficient_eq]
    by_cases hq : ∃ a, (a,q) ∈ p
    · obtain ⟨a,ha⟩ := hq; exact h (a,q) ha
    · exact coefficient_eq_zero_of_not_mem p q (by simpa using hq)
  · intro h q hq
    rw [coefficient_eq, h]
    rfl

def suffixes : ℕ → List Word
  | 0 => [[]]
  | n+1 => (suffixes n).map (0 :: ·) ++ (suffixes n).map (1 :: ·)

def expandTerm (n : ℕ) (a : K × Pair) : Poly K :=
  (suffixes n).map (fun t => (a.1, (a.2.1 ++ t, a.2.2 ++ t)))

@[simp] theorem expandTerm_zero {K : Type*} [CommRing K] (a : K × Pair) :
    expandTerm 0 a = [a] := by
  simp [expandTerm, suffixes]

theorem expandTerm_succ {K : Type*} [CommRing K] (n : ℕ) (a : K) (v w : Word) :
    expandTerm (n+1) (a,(v,w)) =
      expandTerm n (a,(v++[0],w++[0])) ++ expandTerm n (a,(v++[1],w++[1])) := by
  simp only [expandTerm, suffixes, List.map_append, List.map_map]
  simp [Function.comp_def, List.append_assoc]

theorem toArray_expandTerm (n : ℕ) (a : K) (p : Pair) :
    toArray (expandTerm n (a,p)) = a • subdivide K n p := by
  induction n generalizing p with
  | zero => simp [subdivide]
  | succ n ih =>
    rcases p with ⟨v,w⟩
    rw [expandTerm_succ, toArray_append, ih, ih, subdivide, smul_add]

def depth : Poly K → ℕ
  | [] => 0
  | (_,p)::ps => max p.2.length (depth ps)

def spread (m : ℕ) (p : Poly K) : Poly K :=
  p.flatMap (fun a => expandTerm (m-a.2.2.length) a)

theorem toArray_spread (m : ℕ) (p : Poly K) :
    toArray (spread m p) = uniform K m (toArray p) := by
  induction p with
  | nil => simp [spread]
  | cons a p ih =>
    rcases a with ⟨a,v,w⟩
    simp only [spread, List.flatMap_cons, toArray_append, toArray_cons, map_add,
      uniform_single, ← ih, toArray_expandTerm]

theorem depth_bound (p : Poly K) : ∀ q ∈ (toArray p).support, q.2.length ≤ depth p := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rcases a with ⟨a,v,w⟩
    intro q hq
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · have he := ((Finsupp.mem_support_single _ _ _).mp h).1
      simp only [he, depth]
      exact Nat.le_max_left _ _
    · exact (ih q h).trans (Nat.le_max_right _ _)

def zeroTest [DecidableEq K] (p : Poly K) : Bool := isZero (spread (depth p) p)

theorem zeroTest_iff [DecidableEq K] (p : Poly K) :
    zeroTest p = true ↔ evaluate K (toArray p) = 0 := by
  rw [zeroTest, isZero_iff, toArray_spread,
    ← evaluate_eq_zero_of_depth K _ (depth p) (uniform_depth K _ _ (depth_bound p)),
    evaluate_uniform]

end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
