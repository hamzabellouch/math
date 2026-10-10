import Mathlib
import OAI.Computability.MaxCut.Games.ProductTarget
import OAI.Computability.MaxCut.PCP.Product

namespace OAI

/-!
The independent graph product in the last step of the v2 reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

namespace MaxCutGames.Explicit

open MaxCutGames.Foundations.Games
open scoped BigOperators

namespace BipartiteGame

variable {L R E A : Type*}

/-- Independent tuples of edges and labels.  The two endpoint types keep the
two parts separate, even when the base sets happen to have the same type. -/
def product (G : BipartiteGame L R E A) (t : ℕ) :
    BipartiteGame (Fin t → L) (Fin t → R) (Fin t → E) (Fin t → A) where
  left e i := G.left (e i)
  right e i := G.right (e i)
  permutation e :=
    { toFun := fun a i => G.permutation (e i) (a i)
      invFun := fun a i => (G.permutation (e i)).symm (a i)
      left_inv := fun a => by funext i; exact (G.permutation (e i)).left_inv (a i)
      right_inv := fun a => by funext i; exact (G.permutation (e i)).right_inv (a i) }
  simple := by
    intro e f h
    funext i
    apply G.simple
    exact Prod.ext (congrFun (congrArg Prod.fst h) i)
      (congrFun (congrArg Prod.snd h) i)

@[simp] theorem product_left (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (i : Fin t) : (G.product t).left e i = G.left (e i) := rfl

@[simp] theorem product_right (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (i : Fin t) : (G.product t).right e i = G.right (e i) := rfl

@[simp] theorem product_permutation (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (a : Fin t → A) (i : Fin t) :
    (G.product t).permutation e a i = G.permutation (e i) (a i) := rfl

theorem product_isTranslation [Add A] (G : BipartiteGame L R E A)
    (hG : G.IsTranslation) (t : ℕ) : (G.product t).IsTranslation := by
  obtain ⟨offset, hoffset⟩ := hG
  refine ⟨fun e i => offset (e i), ?_⟩
  intro e a
  funext i
  exact hoffset (e i) (a i)

theorem product_edge_card [Fintype E] (t : ℕ) :
    Fintype.card (Fin t → E) = Fintype.card E ^ t := by simp

theorem product_left_card [Fintype L] (t : ℕ) :
    Fintype.card (Fin t → L) = Fintype.card L ^ t := by simp

theorem product_right_card [Fintype R] (t : ℕ) :
    Fintype.card (Fin t → R) = Fintype.card R ^ t := by simp

theorem product_edges_nonempty [Nonempty E] (t : ℕ) :
    Nonempty (Fin t → E) := inferInstance

noncomputable section

variable [Fintype L] [Fintype R] [Fintype E] [Fintype A] [Nonempty E]

/-- Each actual edge has equal weight. Simplicity makes the acceptance
predicate at its endpoint pair exactly its permutation constraint. -/
def toGame (G : BipartiteGame L R E A) : Game L R A A := by
  classical
  exact
    { questions := (FiniteDistribution.uniform E).pushforward
        (fun e => (G.left e, G.right e))
      accepts := fun x y a b => decide
        (∃ e, G.left e = x ∧ G.right e = y ∧ b = G.permutation e a) }

@[simp] theorem toGame_accepts_on_edge (G : BipartiteGame L R E A)
    (e : E) (a b : A) :
    G.toGame.accepts (G.left e) (G.right e) a b = true ↔
      b = G.permutation e a := by
  classical
  simp only [toGame, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hleft, hright, h⟩
    have hf : f = e := G.simple (Prod.ext hleft hright)
    simpa [hf] using h
  · intro h
    exact ⟨e, rfl, rfl, h⟩

/-- At most one accepting right answer exists for each local question pair
and left answer, including question pairs with zero edge weight. -/
theorem toGame_isProjection (G : BipartiteGame L R E A) :
    MaxCutGames.Repetition.IsProjection G.toGame := by
  classical
  intro x y a b b' hb hb'
  simp only [toGame, decide_eq_true_eq] at hb hb'
  obtain ⟨e, heL, heR, he⟩ := hb
  obtain ⟨f, hfL, hfR, hf⟩ := hb'
  have hef : e = f := G.simple (Prod.ext (heL.trans hfL.symm) (heR.trans hfR.symm))
  subst f
  exact he.trans hf.symm

/-- Acceptance probability directly on the uniform occurrence set. -/
def occurrenceSuccess (G : BipartiteGame L R E A)
    (strategy : Strategy L R A A) : ℝ := by
  classical
  exact (FiniteDistribution.uniform E).probability
    (fun e => decide (G.Satisfied strategy.1 strategy.2 e))

theorem toGame_success (G : BipartiteGame L R E A)
    (strategy : Strategy L R A A) :
    G.toGame.success strategy = G.occurrenceSuccess strategy := by
  classical
  unfold Game.success occurrenceSuccess
  change ((FiniteDistribution.uniform E).pushforward _).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  change G.toGame.accepts (G.left e) (G.right e)
      (strategy.1 (G.left e)) (strategy.2 (G.right e)) = true ↔
    decide (G.Satisfied strategy.1 strategy.2 e) = true
  constructor
  · intro h
    exact decide_eq_true ((G.toGame_accepts_on_edge e _ _).mp h)
  · intro h
    exact (G.toGame_accepts_on_edge e _ _).mpr (of_decide_eq_true h)

/-- The probabilistic game evaluates the same unweighted edge fraction as
the explicit graph's integer occurrence counter. -/
theorem toGame_success_eq_satisfiedCount [DecidableEq A]
    (G : BipartiteGame L R E A) (strategy : Strategy L R A A) :
    G.toGame.success strategy =
      (G.satisfiedCount strategy.1 strategy.2 : ℝ) / Fintype.card E := by
  classical
  rw [toGame_success, satisfiedCount_eq_sum_satisfied]
  unfold occurrenceSuccess FiniteDistribution.probability FiniteDistribution.uniform
  simp only [decide_eq_true_eq, Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : G.Satisfied strategy.1 strategy.2 e <;> simp [h]

/-- Independent uniform draws of base edges are exactly the uniform product
edge law, without reweighting or collapsing occurrences. -/
theorem product_uniform_edge_law (t : ℕ) :
    (FiniteDistribution.uniform E).iid t =
      FiniteDistribution.uniform (Fin t → E) :=
  FiniteDistribution.iid_uniform t

/-- The graph construction agrees with the ordinary independent repeated
game for arbitrary local tuple strategies. This is the soundness interface. -/
theorem product_success_eq_repetition (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy (Fin t → L) (Fin t → R) (Fin t → A) (Fin t → A)) :
    (G.product t).toGame.success strategy = (G.toGame.repetition t).success strategy := by
  classical
  let : DecidableEq (Fin t → A) := fun a b => Classical.propDecidable (a = b)
  rw [toGame_success]
  unfold occurrenceSuccess Game.success
  change (FiniteDistribution.uniform (Fin t → E)).probability _ =
    ((G.toGame.questions.iid t).transport (Game.tupleQuestionEquiv t)).probability _
  rw [FiniteDistribution.probability_transport]
  change _ = (((FiniteDistribution.uniform E).pushforward
    (fun e => (G.left e, G.right e))).iid t).probability _
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward,
    FiniteDistribution.iid_uniform]
  congr 1
  funext edges
  apply Bool.eq_iff_iff.mpr
  change _ ↔
    (G.toGame.repetition t).accepts (fun i => G.left (edges i))
      (fun i => G.right (edges i))
      (strategy.1 (fun i => G.left (edges i)))
      (strategy.2 (fun i => G.right (edges i))) = true
  rw [decide_eq_true_eq, Game.repetition_accepts_iff]
  constructor
  · intro h i
    apply (G.toGame_accepts_on_edge (edges i) _ _).mpr
    exact congrFun h i
  · intro h
    funext i
    exact (G.toGame_accepts_on_edge (edges i) _ _).mp (h i)

theorem product_coordinate_success (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy L R A A) :
    (G.product t).toGame.success (Game.repeatStrategy strategy t) =
      G.toGame.success strategy ^ t := by
  rw [product_success_eq_repetition, Game.success_repeatStrategy]

/-- Scalar union bound, proved for the actual base success probability. -/
theorem one_sub_mul_one_sub_le_pow {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (t : ℕ) :
    1 - (t : ℝ) * (1 - p) ≤ p ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmul := mul_le_mul_of_nonneg_right ih hp0
      have hnonneg : 0 ≤ (t : ℝ) * (1 - p) ^ 2 := by positivity
      rw [pow_succ]
      push_cast
      nlinarith

/-- The coordinatewise honest labeling loses at most `t` times the base
error. This does not restrict the strategies covered by the soundness bridge. -/
theorem product_coordinate_completeness (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy L R A A) {error : ℝ}
    (hcomplete : 1 - error ≤ G.toGame.success strategy) :
    1 - (t : ℝ) * error ≤
      (G.product t).toGame.success (Game.repeatStrategy strategy t) := by
  rw [product_coordinate_success]
  have hbound := one_sub_mul_one_sub_le_pow
    (G.toGame.success_nonnegative strategy) (G.toGame.success_le_one strategy) t
  have hmul := mul_le_mul_of_nonneg_left hcomplete (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  linarith

variable [Nonempty A]

/-- The finite maximum over arbitrary local strategies is exactly the
explicit graph value used by the subdivision identity. -/
theorem toGame_value [DecidableEq A] (G : BipartiteGame L R E A) :
    G.toGame.value = G.value := by
  apply le_antisymm
  · apply (G.toGame.value_le_iff _).2
    intro strategy
    rw [toGame_success_eq_satisfiedCount, value]
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (G.satisfiedCount_le_maxSatisfied strategy.1 strategy.2))
      (Nat.cast_nonneg _)
  · obtain ⟨a, b, hab⟩ := G.maxSatisfied_attained
    have hs := G.toGame.success_le_value (a, b)
    rw [toGame_success_eq_satisfiedCount, hab] at hs
    exact hs

theorem product_value_eq_repetition (G : BipartiteGame L R E A) (t : ℕ) :
    (G.product t).toGame.value = (G.toGame.repetition t).value := by
  apply le_antisymm
  · apply ((G.product t).toGame.value_le_iff _).2
    intro strategy
    rw [product_success_eq_repetition]
    exact (G.toGame.repetition t).success_le_value strategy
  · apply ((G.toGame.repetition t).value_le_iff _).2
    intro strategy
    rw [← product_success_eq_repetition]
    exact (G.product t).toGame.success_le_value strategy

theorem product_completeness (G : BipartiteGame L R E A) (t : ℕ) {error : ℝ}
    (hcomplete : 1 - error ≤ G.toGame.value) :
    1 - (t : ℝ) * error ≤ (G.product t).toGame.value := by
  obtain ⟨strategy, hstrategy⟩ := G.toGame.exists_optimal_strategy
  have hs := G.product_coordinate_completeness t strategy (hstrategy.symm ▸ hcomplete)
  exact hs.trans ((G.product t).toGame.success_le_value _)

end

/-- A change of alphabet coordinates keeps endpoints and edge identities. -/
def relabel {B : Type*} (G : BipartiteGame L R E A) (e : A ≃ B) :
    BipartiteGame L R E B where
  left := G.left
  right := G.right
  permutation f := e.symm.trans ((G.permutation f).trans e)
  simple := G.simple

theorem relabel_isTranslation {B : Type*} [Add A] [Add B]
    (G : BipartiteGame L R E A) (e : A ≃+ B) (hG : G.IsTranslation) :
    (G.relabel e.toEquiv).IsTranslation := by
  obtain ⟨offset, hoffset⟩ := hG
  refine ⟨fun f => e (offset f), ?_⟩
  intro f b
  change e (G.permutation f (e.symm b)) = b + e (offset f)
  rw [hoffset, map_add, e.apply_symm_apply]

noncomputable section

variable {B : Type*} [Fintype L] [Fintype R] [Fintype E]
  [Fintype A] [Fintype B] [Nonempty E]

/-- Alphabet coordinates are changed locally at each endpoint. -/
theorem relabel_success (G : BipartiteGame L R E A) (e : A ≃ B)
    (strategy : Strategy L R B B) :
    (G.relabel e).toGame.success strategy =
      G.toGame.success (fun x => e.symm (strategy.1 x), fun y => e.symm (strategy.2 y)) := by
  classical
  rw [toGame_success, toGame_success]
  unfold occurrenceSuccess
  congr 1
  funext f
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have h' := of_decide_eq_true h
    apply decide_eq_true
    apply e.injective
    simpa only [Satisfied, relabel, Equiv.trans_apply, Equiv.apply_symm_apply] using h'
  · intro h
    have h' := of_decide_eq_true h
    apply decide_eq_true
    simpa only [Satisfied, relabel, Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg e h'

theorem relabel_success_forward (G : BipartiteGame L R E A) (e : A ≃ B)
    (strategy : Strategy L R A A) :
    (G.relabel e).toGame.success
      (fun x => e (strategy.1 x), fun y => e (strategy.2 y)) =
      G.toGame.success strategy := by
  rw [relabel_success]
  congr 1
  apply Prod.ext <;> funext x <;> simp

theorem relabel_value [Nonempty A] [Nonempty B]
    (G : BipartiteGame L R E A) (e : A ≃ B) :
    (G.relabel e).toGame.value = G.toGame.value := by
  apply le_antisymm
  · apply ((G.relabel e).toGame.value_le_iff _).2
    intro strategy
    rw [relabel_success]
    exact G.toGame.success_le_value _
  · apply (G.toGame.value_le_iff _).2
    intro strategy
    rw [← G.relabel_success_forward e strategy]
    exact (G.relabel e).toGame.success_le_value _

end

/-- The explicit binary vector coordinates of the final alphabet. The
coordinate order is `(base bit, repetition coordinate)`. -/
def binaryProductEquiv (ell t : ℕ) :
    (Fin t → Fin ell → ZMod 2) ≃+ (Fin (ell * t) → ZMod 2) where
  toFun a j := a ((finProdFinEquiv.symm j : Fin ell × Fin t).2)
    ((finProdFinEquiv.symm j : Fin ell × Fin t).1)
  invFun a i j := a (finProdFinEquiv (j, i))
  left_inv a := by funext i j; simp
  right_inv a := by
    funext j
    change a (finProdFinEquiv (finProdFinEquiv.symm j : Fin ell × Fin t)) = a j
    rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl

def binaryProduct {ell : ℕ} (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) :
    BipartiteGame (Fin t → L) (Fin t → R) (Fin t → E) (Fin (ell * t) → ZMod 2) :=
  (G.product t).relabel (binaryProductEquiv ell t).toEquiv

theorem binaryProduct_isTranslation {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (hG : G.IsTranslation) (t : ℕ) :
    (G.binaryProduct t).IsTranslation :=
  relabel_isTranslation _ (binaryProductEquiv ell t) (G.product_isTranslation hG t)

theorem binaryProduct_dimension_positive {ell t : ℕ} (hell : 0 < ell) (ht : 0 < t) :
    0 < ell * t := Nat.mul_pos hell ht

theorem binaryProduct_alphabet_card (ell t : ℕ) :
    Fintype.card (Fin (ell * t) → ZMod 2) = 2 ^ (ell * t) := by simp

noncomputable section

variable [Fintype L] [Fintype R] [Fintype E] [Nonempty E]

theorem binaryProduct_value_eq_repetition {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) :
    (G.binaryProduct t).toGame.value = (G.toGame.repetition t).value := by
  rw [binaryProduct, relabel_value, product_value_eq_repetition]

theorem binaryProduct_completeness {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) {error : ℝ}
    (hcomplete : 1 - error ≤ G.toGame.value) :
    1 - (t : ℝ) * error ≤ (G.binaryProduct t).toGame.value := by
  rw [binaryProduct, relabel_value]
  exact G.product_completeness t hcomplete

end

end BipartiteGame

end MaxCutGames.Explicit

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace MaxCutGames.Explicit.ProductPaddedOutput

open MaxCutGames.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

def row (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ↪ Fin N)
    (edges : Fin M ≃ E) (i : Fin M) : Constraint N q where
  source := vertices (Sum.inl (G.left (edges i)))
  target := vertices (Sum.inr (G.right (edges i)))
  permutation := fullTable (G.permutation (edges i))

def render (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ↪ Fin N)
    (edges : Fin M ≃ E) (hM : 0 < M) : Instance q where
  vertices := N
  constraints := List.ofFn (row G vertices edges)
  nonempty := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hlen
    omega

@[simp] theorem render_length (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    (render G vertices edges hM).constraints.length = M := by simp [render]

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (i : Fin (render G vertices edges hM).constraints.length) :
    (render G vertices edges hM).constraints[i] =
      row G vertices edges ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (side : Fin N → Bool)
    (leftSide : ∀ x, side (vertices (Sum.inl x)) = false)
    (rightSide : ∀ y, side (vertices (Sum.inr y)) = true) :
    SimpleBipartite (render G vertices edges hM) where
  side := side
  sourceSide i := by simp only [render_get, row, leftSide]
  targetSide i := by simp only [render_get, row, rightSide]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges ⟨i.val, hi⟩).source,
          (row G vertices edges ⟨i.val, hi⟩).target) =
        ((row G vertices edges ⟨j.val, hj⟩).source,
          (row G vertices edges ⟨j.val, hj⟩).target) := by
      simpa only [render_get] using! hij
    have he : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective he))

variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in
theorem count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  change countSatisfied labeling (List.ofFn (row G vertices edges)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, fullTable]

noncomputable def extendLabelings [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) :
    Fin N → Fin q :=
  Function.extend vertices (Sum.elim left right) (fun _ => Classical.choice inferInstance)

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_left [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (x : L) :
    extendLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  exact vertices.injective.extend_apply _ _ _

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_right [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (y : R) :
    extendLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  exact vertices.injective.extend_apply _ _ _

theorem maxSatisfied [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges hM) = G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    erw [count]
    exact G.satisfiedCount_le_maxSatisfied _ _
  · obtain ⟨left, right, hmax⟩ := G.maxSatisfied_attained
    have hcount := count G vertices edges hM (extendLabelings vertices left right)
    simp only [extendLabelings_left, extendLabelings_right, hmax] at hcount
    rw [← hcount]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges hM) (extendLabelings vertices left right)

theorem value [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.value (render G vertices edges hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [maxSatisfied, render_length]
  have hc : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hc]

end Embedded

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

local instance : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩

abbrev Left := {v : Fin H.vertices // presentation.side v = false}
abbrev Right := {v : Fin H.vertices // presentation.side v = true}

def graph (t : ℕ) : BipartiteGame
    (Fin t → Left H presentation) (Fin t → Right H presentation)
    (Fin t → Fin H.constraints.length) (Fin (q ^ t)) :=
  (presentation.toBipartiteGame.product t).relabel finFunctionFinEquiv

/-- The two genuine product vertex sets embed into the common global radix
space. Opposite sides cannot collide because the repetition count is positive. -/
def vertices (t : ℕ) (ht : 0 < t) :
    ((Fin t → Left H presentation) ⊕ (Fin t → Right H presentation)) ↪
      Fin (H.vertices ^ t) where
  toFun := Sum.elim
    (fun x => finFunctionFinEquiv (fun i => (x i).val))
    (fun y => finFunctionFinEquiv (fun i => (y i).val))
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        funext i
        exact Subtype.ext (congrFun (finFunctionFinEquiv.injective h) i)
      | inr y =>
        have hfirst := congrFun (finFunctionFinEquiv.injective h) ⟨0, ht⟩
        have hs := congrArg presentation.side hfirst
        rw [(x ⟨0, ht⟩).property, (y ⟨0, ht⟩).property] at hs
        cases hs
    | inr x =>
      cases y with
      | inl y =>
        have hfirst := congrFun (finFunctionFinEquiv.injective h) ⟨0, ht⟩
        have hs := congrArg presentation.side hfirst
        rw [(x ⟨0, ht⟩).property, (y ⟨0, ht⟩).property] at hs
        cases hs
      | inr y =>
        apply congrArg Sum.inr
        funext i
        exact Subtype.ext (congrFun (finFunctionFinEquiv.injective h) i)

def side (t : ℕ) (ht : 0 < t) (v : Fin (H.vertices ^ t)) : Bool :=
  presentation.side (finFunctionFinEquiv.symm v ⟨0, ht⟩)

theorem side_left (t : ℕ) (ht : 0 < t) (x : Fin t → Left H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inl x)) = false := by
  simp only [side, vertices]
  change presentation.side
    (finFunctionFinEquiv.symm (finFunctionFinEquiv (fun i => (x i).val)) ⟨0, ht⟩) = false
  rw [Equiv.symm_apply_apply]
  exact (x ⟨0, ht⟩).property

theorem side_right (t : ℕ) (ht : 0 < t) (y : Fin t → Right H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inr y)) = true := by
  simp only [side, vertices]
  change presentation.side
    (finFunctionFinEquiv.symm (finFunctionFinEquiv (fun i => (y i).val)) ⟨0, ht⟩) = true
  rw [Equiv.symm_apply_apply]
  exact (y ⟨0, ht⟩).property

def outputRow (t : ℕ) (ht : 0 < t) (i : Fin (H.constraints.length ^ t)) :
    Constraint (H.vertices ^ t) (q ^ t) :=
  Embedded.row (graph H presentation t) (vertices H presentation t ht)
    finFunctionFinEquiv.symm i

def output (t : ℕ) (ht : 0 < t) : Instance (q ^ t) :=
  Embedded.render (graph H presentation t) (vertices H presentation t ht)
    finFunctionFinEquiv.symm (pow_pos H.constraintCount_positive t)

@[simp] theorem output_vertices (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).vertices = H.vertices ^ t := rfl

@[simp] theorem output_constraints (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).constraints = List.ofFn (outputRow H presentation t ht) := rfl

@[simp] theorem output_length (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).constraints.length = H.constraints.length ^ t := by simp

def simpleBipartite (t : ℕ) (ht : 0 < t) : SimpleBipartite (output H presentation t ht) :=
  Embedded.simpleBipartite _ _ _ _ (side H presentation t ht)
    (side_left H presentation t ht) (side_right H presentation t ht)

theorem outputRow_source (t : ℕ) (ht : 0 < t)
    (i : Fin (H.constraints.length ^ t)) :
    ((outputRow H presentation t ht i).source : ℕ) =
      ∑ j : Fin t, (H.constraints[finFunctionFinEquiv.symm i j].source : ℕ) *
        H.vertices ^ (j : ℕ) := rfl

theorem outputRow_target (t : ℕ) (ht : 0 < t)
    (i : Fin (H.constraints.length ^ t)) :
    ((outputRow H presentation t ht i).target : ℕ) =
      ∑ j : Fin t, (H.constraints[finFunctionFinEquiv.symm i j].target : ℕ) *
        H.vertices ^ (j : ℕ) := rfl

theorem outputRow_images (t : ℕ) (ht : 0 < t)
    (i : Fin (H.constraints.length ^ t)) (a : Fin (q ^ t)) :
    (outputRow H presentation t ht i).permutation.images[a] =
      finFunctionFinEquiv (fun j =>
        H.constraints[finFunctionFinEquiv.symm i j].permutation.images[
          finFunctionFinEquiv.symm a j]) := by
  simp [outputRow, Embedded.row, graph, BipartiteGame.relabel, BipartiteGame.product,
    SimpleBipartite.toBipartiteGame, permutationEquiv, fullTable]

theorem output_gameWords (t : ℕ) (ht : 0 < t) :
    Complexity.gameWords (output H presentation t ht) =
      [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++
        (List.ofFn (outputRow H presentation t ht)).flatMap Complexity.constraintWords := by
  simp only [Complexity.gameWords, output_vertices, output_constraints, List.length_ofFn]

noncomputable section

theorem output_value_eq_repetition [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) :
    Integration.InstanceValue.value (output H presentation t ht) =
      (presentation.toBipartiteGame.toGame.repetition t).value := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  let : Nonempty (Fin (q ^ t)) :=
    ⟨finFunctionFinEquiv (fun _ : Fin t => Classical.choice inferInstance)⟩
  rw [output, Embedded.value, ← BipartiteGame.toGame_value, graph,
    BipartiteGame.relabel_value, BipartiteGame.product_value_eq_repetition]

theorem output_completeness [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) {error : ℝ}
    (hcomplete : 1 - error ≤ Integration.InstanceValue.value H) :
    1 - (t : ℝ) * error ≤ Integration.InstanceValue.value (output H presentation t ht) := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition, ← BipartiteGame.product_value_eq_repetition]
  exact presentation.toBipartiteGame.product_completeness t
    (by simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hcomplete)

end

def finalCoordinates {ell : ℕ} (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) :
    Fin (q ^ t) ≃ (Fin (ell * t) → ZMod 2) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.piCongrRight (fun _ : Fin t => coordinates)).trans
      (BipartiteGame.binaryProductEquiv ell t).toEquiv)

theorem finalCoordinates_apply {ell : ℕ}
    (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) (a : Fin (q ^ t)) :
    finalCoordinates coordinates t a = BipartiteGame.binaryProductEquiv ell t
      (fun i => coordinates (finFunctionFinEquiv.symm a i)) := rfl

theorem output_translations {ell : ℕ}
    (coordinates : Fin q ≃ (Fin ell → ZMod 2))
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H)
    (t : ℕ) (ht : 0 < t) :
    Integration.TranslationTarget.IsTranslationInstance (finalCoordinates coordinates t)
      (output H presentation t ht) := by
  classical
  choose offset hoffset using fun e : Fin H.constraints.length =>
    hH H.constraints[e] (List.getElem_mem e.isLt)
  intro constraint hconstraint
  rw [output_constraints] at hconstraint
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hconstraint
  refine ⟨BipartiteGame.binaryProductEquiv ell t
    (fun j => offset (finFunctionFinEquiv.symm i j)), ?_⟩
  intro a
  rw [outputRow_images]
  simp only [finalCoordinates_apply, Equiv.symm_apply_apply]
  rw [← map_add]
  congr 1
  funext j
  exact hoffset _ _

end MaxCutGames.Explicit.ProductPaddedOutput

end OAI
