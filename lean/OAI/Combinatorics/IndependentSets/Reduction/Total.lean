import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.ClausePolynomial
import OAI.Combinatorics.IndependentSets.Encoding.BitsValue

namespace OAI

namespace LargeIndependentSets

section
open IndependentSetsGames.Foundations
noncomputable section
namespace SemanticReduction

def total (H : PCP.RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : Graph := reduce H p u q hq (BinaryParser.decode b)

def totalPolynomial (p : SamplerParameters) (u q : ℕ) : Polynomial ℕ :=
  (outputPolynomial p u q).comp (Polynomial.X+Polynomial.C 1)

lemma total_output_bound (H : PCP.RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : (graphBits (total H p u q hq b)).length ≤ (totalPolynomial p u q).eval b.length := by
  apply (output_polynomial H p u q hq (BinaryParser.decode b)).trans
  have hh := Complexity.MachineComposition.natPolynomial_eval_mono
    (outputPolynomial p u q) (BinaryParser.decode_bits_bound b)
  simpa only [totalPolynomial,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_C] using hh

end SemanticReduction

theorem total_semantic_polynomial_output_reduction {δ : ℚ} (hδ : 0<δ) :
    ∃ reduce : List Bool → Graph, ∃ P : Polynomial ℕ,
      (∀ b, (graphBits (reduce b)).length ≤ P.eval b.length) ∧
      (∀ F : Formula, F.Satisfiable → (reduce (formulaBits F)).ThreeColorable) ∧
      (∀ F : Formula, ¬F.Satisfiable →
        ((reduce (formulaBits F)).independenceNumber : ℚ) < δ*(reduce (formulaBits F)).vertices) := by
  obtain ⟨H,p,u,q,hq,hyes,hno⟩ := semantic_reduction hδ
  refine ⟨SemanticReduction.total H p u q hq,SemanticReduction.totalPolynomial p u q,
    SemanticReduction.total_output_bound H p u q hq,?_,?_⟩
  · intro F hF
    simpa only [SemanticReduction.total,BinaryParser.decode_encoded] using hyes F hF
  · intro F hF
    simpa only [SemanticReduction.total,BinaryParser.decode_encoded] using hno F hF

end
end

namespace ShortestPaths
open scoped ENNReal

def pivot {X A : Type*} [Min A] [Add A] (w : X → X → A) (k : X) (x y : X) : A :=
  min (w x y) (w x k + w k y)

def closure {X A : Type*} [Min A] [Add A] (w : X → X → A) : List X → X → X → A
  | [] => w
  | k::ks => closure (pivot w k) ks

lemma pivot_le {X : Type*} (w : X → X → ℝ≥0∞) (k x y : X) : pivot w k x y ≤ w x y :=
  min_le_left _ _

lemma pivot_at {X : Type*} (w : X → X → ℝ≥0∞) (k x y : X) :
    pivot w k x y ≤ pivot w k x k + pivot w k k y := by
  simp only [pivot, min_eq_left (le_self_add), min_eq_left (le_add_self)]
  exact min_le_right _ _

lemma pivot_preserves {X : Type*} (w : X → X → ℝ≥0∞) (k z : X)
    (h : ∀ x y, w x y ≤ w x z + w z y) :
    ∀ x y, pivot w k x y ≤ pivot w k x z + pivot w k z y := by
  intro x y
  unfold pivot
  rw [min_add,add_min,add_min]
  apply le_min
  · apply le_min
    · exact (min_le_left _ _).trans (h x y)
    · exact (min_le_right _ _).trans (by
        simpa only [add_assoc,add_comm,add_left_comm] using add_le_add_right (h x k) (w k y))
  · apply le_min
    · exact (min_le_right _ _).trans (by
        simpa only [add_assoc,add_comm,add_left_comm] using add_le_add_left (h k y) (w x k))
    · exact (min_le_right _ _).trans (by
        have hh : w x k + w k y ≤ w x k + (w k z + w z k) + w k y :=
          add_le_add le_self_add le_rfl
        simpa only [add_assoc,add_comm,add_left_comm] using hh)

lemma closure_le {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) (x y : X) :
    closure w ks x y ≤ w x y := by
  induction ks generalizing w with
  | nil => exact le_rfl
  | cons k ks ih => exact (ih _).trans (pivot_le _ _ _ _)

lemma closure_preserves {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) (z : X)
    (h : ∀ x y, w x y ≤ w x z + w z y) :
    ∀ x y, closure w ks x y ≤ closure w ks x z + closure w ks z y := by
  induction ks generalizing w with
  | nil => exact h
  | cons k ks ih => exact ih _ (pivot_preserves w k z h)

lemma closure_at {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) {z : X} (hz : z ∈ ks) :
    ∀ x y, closure w ks x y ≤ closure w ks x z + closure w ks z y := by
  induction ks generalizing w with
  | nil => simp at hz
  | cons k ks ih =>
    rcases List.mem_cons.mp hz with he | hz
    · subst z
      exact closure_preserves _ ks k (pivot_at w k)
    · exact ih _ hz

lemma distance_le_closure {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) (x y : X) :
    pathDistance w x y ≤ closure w ks x y := by
  have h : ∀ (v : X → X → ℝ≥0∞), (∀ x y, pathDistance w x y ≤ v x y) →
      ∀ x y, pathDistance w x y ≤ closure v ks x y := by
    induction ks with
    | nil => intro v hv; exact hv
    | cons k ks ih =>
      intro v hv
      apply ih
      intro x y
      exact le_min (hv x y) ((pathDistance_triangle w x k y).trans (add_le_add (hv x k) (hv k y)))
  exact h w (pathDistance_le_link w) x y

theorem closure_eq_distance {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X)
    (hks : ∀ z, z ∈ ks) (x y : X) : closure w ks x y = pathDistance w x y := by
  apply le_antisymm ?_ (distance_le_closure w ks x y)
  apply le_iInf
  intro zs
  induction zs generalizing x with
  | nil => exact closure_le w ks x y
  | cons z zs ih =>
    exact (closure_at w ks (hks z) x y).trans (add_le_add (closure_le w ks x z) (ih z))

lemma closure_map {X A B : Type*} [Min A] [Add A] [Min B] [Add B]
    (f : A → B) (hfmin : ∀ a b, f (min a b) = min (f a) (f b))
    (hfadd : ∀ a b, f (a+b) = f a+f b) (w : X → X → A) (ks : List X) :
    (fun x y => f (closure w ks x y)) = closure (fun x y => f (w x y)) ks := by
  induction ks generalizing w with
  | nil => rfl
  | cons k ks ih =>
    simp only [closure]
    rw [ih]
    congr 1
    funext x y
    simp only [pivot,hfmin,hfadd]

abbrev Matrix (n : ℕ) := Vector (Vector ℕ∞ n) n

def Matrix.get {n : ℕ} (a : Matrix n) (i j : Fin n) : ℕ∞ := a[i.val][j.val]

def Matrix.pivot {n : ℕ} (a : Matrix n) (k : Fin n) : Matrix n :=
  letI : Min ℕ∞ := @LinearOrder.toMin ℕ∞ instLinearOrderENat
  Vector.ofFn (fun i => Vector.ofFn (fun j => ShortestPaths.pivot a.get k i j))

def Matrix.run {n : ℕ} (a : Matrix n) : List (Fin n) → Matrix n
  | [] => a
  | k::ks => (a.pivot k).run ks

lemma Matrix.run_get {n : ℕ} (a : Matrix n) (ks : List (Fin n)) :
    (a.run ks).get = closure a.get ks := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih =>
    rw [Matrix.run,ih]
    simp only [closure]
    congr 1
    funext i j
    simp [Matrix.pivot, Matrix.get]

def Matrix.allPairs {n : ℕ} (a : Matrix n) : Matrix n := a.run (List.finRange n)

theorem Matrix.allPairs_exact {n : ℕ} (a : Matrix n) (i j : Fin n) :
    ((a.allPairs.get i j : ℕ∞) : ℝ≥0∞) =
      pathDistance (fun x y => (a.get x y : ℝ≥0∞)) i j := by
  rw [Matrix.allPairs,Matrix.run_get]
  have hm := congrFun (congrFun (closure_map (fun z : ℕ∞ => (z:ℝ≥0∞))
    ENat.toENNReal_min ENat.toENNReal_add a.get (List.finRange n)) i) j
  rw [hm]
  exact closure_eq_distance _ _ (fun z => List.mem_finRange z) i j

end ShortestPaths
end LargeIndependentSets

end OAI
