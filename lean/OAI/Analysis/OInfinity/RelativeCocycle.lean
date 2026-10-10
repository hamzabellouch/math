import OAI.Analysis.OInfinity.ProjectionCorner

namespace OAI

/-! # Actual binary row cocycles in a proper projection corner

The corner unitary is extended by the identity on the complementary
projection. The complement is retained explicitly; this is not yet an
ambient approximate intertwining statement for the canonical O∞ rows.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- A supported element, regarded as an element of the unital corner. -/
def projectionCornerElement (q : E) (hq : star q = q) (hqq : q * q = q)
    (x : E) (hx : q * x = x ∧ x * q = x) : ProjectionCorner q hq hqq := ⟨x, hx⟩

lemma projectionCornerElement_gram {I : Type*} [DecidableEq I]
    (q : E) (hq : star q = q) (hqq : q * q = q) (s : I → E)
    (hsp : ∀ i, q * s i = s i ∧ s i * q = s i)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0) (i j : I) :
    star (projectionCornerElement q hq hqq (s i) (hsp i)) *
      projectionCornerElement q hq hqq (s j) (hsp j) = if i = j then 1 else 0 := by
  apply Subtype.ext
  split_ifs with hij
  · change star (s i) * s j = q
    simpa only [hij, ite_true] using hs i j
  · change star (s i) * s j = 0
    simpa only [hij, ite_false] using hs i j

lemma projectionCornerElement_range_sum {I : Type*} [Fintype I]
    (q : E) (hq : star q = q) (hqq : q * q = q) (s : I → E)
    (hsp : ∀ i, q * s i = s i ∧ s i * q = s i)
    (hsum : (∑ i, s i * star (s i)) = q) :
    (∑ i, projectionCornerElement q hq hqq (s i) (hsp i) *
      star (projectionCornerElement q hq hqq (s i) (hsp i))) = 1 := by
  apply Subtype.ext
  change projectionCornerInclusion q hq hqq (∑ i,
    projectionCornerElement q hq hqq (s i) (hsp i) *
      star (projectionCornerElement q hq hqq (s i) (hsp i))) = q
  rw [map_sum]
  exact hsum

lemma projectionCornerInclusion_rowCocycle {I : Type*} [Fintype I]
    (q : E) (hq : star q = q) (hqq : q * q = q)
    (s t : I → ProjectionCorner q hq hqq) :
    projectionCornerInclusion q hq hqq (finiteRowCocycle s t) =
      finiteRowCocycle (fun i => (s i : E)) (fun i => (t i : E)) := by
  simp only [finiteRowCocycle, map_sum, map_mul, map_star]
  rfl

lemma projectionCornerInclusion_rowShift {I : Type*} [Fintype I]
    (q : E) (hq : star q = q) (hqq : q * q = q)
    (s : I → ProjectionCorner q hq hqq) (x : ProjectionCorner q hq hqq) :
    projectionCornerInclusion q hq hqq (finiteRowShift s x) =
      finiteRowShift (fun i => (s i : E)) (x : E) := by
  simp only [finiteRowShift, map_sum, map_mul, map_star]
  rfl

/-- The actual product cocycle, with the corner unit as its zeroth term. -/
def relativeRowProduct {I : Type*} [Fintype I] (q : E) (s t : I → E) : ℕ → E
  | 0 => q
  | n + 1 => finiteRowCocycle s t * finiteRowShift s (relativeRowProduct q s t n)

lemma projectionCorner_rowProduct (q : E) (hq : star q = q) (hqq : q * q = q)
    (s t : Fin 2 → ProjectionCorner q hq hqq)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (n : ℕ) :
    ((binaryRowCocycleUnitary s t hs ht hsum htsum n : ProjectionCorner q hq hqq) : E) =
      relativeRowProduct q (fun i => (s i : E)) (fun i => (t i : E)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change projectionCornerInclusion q hq hqq
        (finiteRowCocycle s t *
          (binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
            (by simpa using hs 1 1) (by simpa using hs 0 1)
            (binaryRowCocycleUnitary s t hs ht hsum htsum n) : ProjectionCorner q hq hqq)) = _
      rw [map_mul, binarySplitHom_coe s hs hsum,
        projectionCornerInclusion_rowCocycle, projectionCornerInclusion_rowShift, ih]
      rfl

lemma projectionCornerUnitary_complement (q : E) (hq : star q = q) (hqq : q * q = q)
    (u : unitary (ProjectionCorner q hq hqq)) :
    (projectionCornerUnitary q hq hqq u : E) * (1 - q) = 1 - q ∧
      (1 - q) * (projectionCornerUnitary q hq hqq u : E) = 1 - q := by
  have hl := (u : ProjectionCorner q hq hqq).property.1
  have hr := (u : ProjectionCorner q hq hqq).property.2
  change (((u : ProjectionCorner q hq hqq) : E) + (1 - q)) * (1 - q) = 1 - q ∧
    (1 - q) * (((u : ProjectionCorner q hq hqq) : E) + (1 - q)) = 1 - q
  constructor
  · simp only [add_mul, mul_sub, sub_mul, one_mul, mul_one, hqq, hr]
    abel
  · simp only [mul_add, mul_sub, sub_mul, one_mul, mul_one, hqq, hl]
    abel

/-- The uniform `192π` contraction survives proper-corner transport.
The constructed ambient unitary is exactly the product cocycle plus `1-q`
and fixes the complementary corner on both sides. -/
lemma exists_relative_binaryRowCocycle_path
    (q : E) (hq : star q = q) (hqq : q * q = q) (hqne : q ≠ 0)
    (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (hc : ∀ i j, Commute (s i) (t j)) (n : ℕ) :
    ∃ u : unitary E, (u : E) = relativeRowProduct q s t n + (1 - q) ∧
      (u : E) * (1 - q) = 1 - q ∧ (1 - q) * (u : E) = 1 - q ∧
      ∃ p : Path u 1, ∀ a b, ‖(p a : E) - p b‖ ≤ (192 * Real.pi) * |(a : ℝ) - b| := by
  have : NeZero q := ⟨hqne⟩
  have hsp (i : Fin 2) : q * s i = s i ∧ s i * q = s i :=
    ⟨finiteRow_left_support q s hq hqq hs hsum i,
      finiteRow_right_support q s hq hqq hs i⟩
  have htp (i : Fin 2) : q * t i = t i ∧ t i * q = t i :=
    ⟨finiteRow_left_support q t hq hqq ht htsum i,
      finiteRow_right_support q t hq hqq ht i⟩
  let S : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (s i) (hsp i)
  let T : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (t i) (htp i)
  have hS := projectionCornerElement_gram q hq hqq s hsp hs
  have hT := projectionCornerElement_gram q hq hqq t htp ht
  have hSsum := projectionCornerElement_range_sum q hq hqq s hsp hsum
  have hTsum := projectionCornerElement_range_sum q hq hqq t htp htsum
  have hST (i j : Fin 2) : Commute (S i) (T j) := by
    change S i * T j = T j * S i
    apply Subtype.ext
    exact (hc i j).eq
  obtain ⟨p, hp⟩ := exists_uniform_binaryRowCocycle_path S T hS hT hSsum hTsum hST n
  let v := binaryRowCocycleUnitary S T hS hT hSsum hTsum n
  let u := projectionCornerUnitary q hq hqq v
  obtain ⟨r, hr⟩ := projectionCornerPath_controlled q hq hqq p (192 * Real.pi) hp
  refine ⟨u, ?_, (projectionCornerUnitary_complement q hq hqq v).1,
    (projectionCornerUnitary_complement q hq hqq v).2, ?_⟩
  · change ((v : ProjectionCorner q hq hqq) : E) + (1 - q) = _
    rw [projectionCorner_rowProduct q hq hqq S T hS hT hSsum hTsum n]
    rfl
  · exact ⟨r.cast rfl (projectionCornerUnitary_one q hq hqq).symm, hr⟩

end WeakPureInfiniteness

end

end OAI
