import OAI.Algebra.DepthFive.RelaxedPaths
import OAI.Algebra.DepthFive.IndependentCoordinates

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings
open IndependentCoordinates

instance vertexNonempty (α : Type*) [Nonempty α] (τ σ : Kind) :
    Nonempty (Vertex α τ σ) := by
  obtain ⟨a⟩ := ‹Nonempty α›
  refine ⟨⟨⟨a,a,a,a⟩, ?_⟩⟩
  cases τ <;> cases σ <;> simp [Respects]

/-- Agreement between the two labels of a normal pairing at a vertex. -/
def vertexPairEq {α : Type*} [DecidableEq α] {τ σ : Kind}
    (x : Vertex α τ σ) : ℝ := if x.1.p = x.1.r then 1 else 0

theorem average_vertexPairEq (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
    (τ σ : Kind) :
    average (vertexPairEq (α := α) (τ := τ) (σ := σ)) =
      if τ = .normal ∧ σ = .normal then (Fintype.card α : ℝ)⁻¹ else 1 := by
  cases τ <;> cases σ
  · change average (fun x : Vertex α .normal .normal =>
      pairEq (normalVertexEquiv α x)) = (Fintype.card α : ℝ)⁻¹
    exact (average_equiv (normalVertexEquiv α) pairEq).trans (average_pair_eq (α := α))
  · have h : vertexPairEq (α := α) (τ := .normal) (σ := .diagonal) = fun _ => (1 : ℝ) := by
      funext x
      simp [vertexPairEq, x.property.2.1]
    simp [h, average_const]
  · have h : vertexPairEq (α := α) (τ := .diagonal) (σ := .normal) = fun _ => (1 : ℝ) := by
      funext x
      simp [vertexPairEq, x.property.1.1]
    simp [h, average_const]
  · have h : vertexPairEq (α := α) (τ := .diagonal) (σ := .diagonal) = fun _ => (1 : ℝ) := by
      funext x
      simp [vertexPairEq, x.property.1.1]
    simp [h, average_const]

/-- Number of endpoints at which both adjacent pairing types are normal. -/
def normalEndpointCount {L : ℕ} (τ : Fin (L + 1) → Kind)
    (s : Finset (Fin L)) : ℕ :=
  (s.filter (fun v => τ v.castSucc = .normal ∧ τ v.succ = .normal)).card

/-- Equality of both normal coordinates at all indicated internal endpoints. -/
def endpointCoincidence {α : Type*} [DecidableEq α] {L : ℕ}
    {τ : Fin (L + 1) → Kind} (s : Finset (Fin L)) (x : Assignments α τ) : ℝ :=
  ∏ v : s, vertexPairEq (x v)

theorem average_endpoint_group (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
    {L : ℕ} (τ : Fin (L + 1) → Kind) (s : Finset (Fin L)) :
    average (fun x : ∀ v : s, Vertex α (τ v.val.castSucc) (τ v.val.succ) =>
      ∏ v, vertexPairEq (x v)) =
      (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ s := by
  rw [average_prod]
  simp_rw [average_vertexPairEq]
  rw [Finset.prod_coe_sort s (fun v : Fin L =>
    if τ v.castSucc = .normal ∧ τ v.succ = .normal then
      (Fintype.card α : ℝ)⁻¹ else 1), ← Finset.prod_filter]
  simp [normalEndpointCount]

theorem average_endpoint_correction (α : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] {L : ℕ} (τ : Fin (L + 1) → Kind) (s : Finset (Fin L)) (c : ℝ) :
    average (fun x : ∀ v : s, Vertex α (τ v.val.castSucc) (τ v.val.succ) =>
      1 + c * ∏ v, vertexPairEq (x v)) =
      1 + c * (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ s := by
  rw [average_add, average_const, average_const_mul, average_endpoint_group]

/-- Exact average of normal-layer corrections for disjoint endpoint sets in
actual relaxed vertex assignments, including forced-equality interfaces. -/
theorem average_assignment_corrections (α : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] {L : ℕ} (τ : Fin (L + 1) → Kind)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Finset (Fin L)) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (c : ι → ℝ) :
    average (fun x : Assignments α τ => ∏ i, (1 + c i * endpointCoincidence (s i) x)) =
      ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ (s i)) := by
  change average (fun x : Assignments α τ =>
    ∏ i, (1 + c i * ∏ v : s i, vertexPairEq (x v))) = _
  have h := average_disjoint_finset_prod_dependent
    (β := fun v : Fin L => Vertex α (τ v.castSucc) (τ v.succ)) s hs
    (fun i (x : ∀ v : s i, Vertex α (τ v.val.castSucc) (τ v.val.succ)) =>
      1 + c i * ∏ v, vertexPairEq (x v))
  apply h.trans
  apply Finset.prod_congr rfl
  intro i _
  exact average_endpoint_correction α τ (s i) (c i)

/-- The weighted relaxed-assignment count: its unweighted count times the
product of the independent normal-layer correction averages. -/
theorem sum_assignment_corrections (α : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] {L : ℕ} (τ : Fin (L + 1) → Kind)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Finset (Fin L)) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (c : ι → ℝ) :
    (∑ x : Assignments α τ, ∏ i, (1 + c i * endpointCoincidence (s i) x)) =
      (Fintype.card α : ℝ) ^ (2 * L - adjacentSwitches τ) *
        ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ (s i)) := by
  have h := average_assignment_corrections α τ s hs c
  rw [average] at h
  have hc : (Fintype.card (Assignments α τ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum := (div_eq_iff hc).mp h
  rw [card_assignments, Nat.cast_pow] at hsum
  simpa only [mul_comm] using hsum

/-- The internal vertices adjacent to a specified layer. -/
def internalEndpointSet {L : ℕ} (t : Fin (L + 1)) : Finset (Fin L) :=
  Finset.univ.filter (fun v => v.castSucc = t ∨ v.succ = t)

/-- Distinct nonadjacent layers use disjoint internal vertex coordinates. -/
theorem internalEndpointSet_disjoint {L : ℕ} {i j : Fin (L + 1)}
    (hij : i ≠ j) (hforward : i.val + 1 ≠ j.val)
    (hbackward : j.val + 1 ≠ i.val) :
    Disjoint (internalEndpointSet i) (internalEndpointSet j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [internalEndpointSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hv hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  all_goals
    have hv' := congrArg Fin.val hv
    have hw' := congrArg Fin.val hw
    simp only [Fin.val_castSucc, Fin.val_succ] at hv' hw'
    omega

/-- An injective family of pairwise nonadjacent layers meets the exact
independence hypothesis of `sum_relaxedPaths_layer_corrections`. -/
theorem pairwise_internalEndpointSet_disjoint {L : ℕ} {ι : Type*}
    (t : ι → Fin (L + 1)) (ht : Function.Injective t)
    (hseparated : ∀ i j, i ≠ j → (t i).val + 1 ≠ (t j).val) :
    Pairwise (fun i j => Disjoint (internalEndpointSet (t i))
      (internalEndpointSet (t j))) := by
  intro i j hij
  exact internalEndpointSet_disjoint (fun h => hij (ht h))
    (hseparated i j hij) (hseparated j i hij.symm)

theorem layer_coordinate_eq_iff {α : Type*} {L : ℕ}
    (a : α) (x : Fin L → Labels α) (t : Fin (L + 1)) :
    (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ)).p =
      (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ)).r ↔
    ∀ v ∈ internalEndpointSet t, (x v).p = (x v).r := by
  simp only [zipLabels, Prod.mk.injEq]
  constructor
  · intro h v hv
    rcases (Finset.mem_filter.mp hv).2 with hv | hv
    · subst t
      simpa only [closePaths_internal] using h.2
    · subst t
      simpa only [Fin.castSucc_succ, closePaths_internal] using h.1
  · intro h
    constructor
    · have hleft : ∀ t : Fin (L + 1),
          (∀ v ∈ internalEndpointSet t, (x v).p = (x v).r) →
          (closePaths a x t.castSucc).p = (closePaths a x t.castSucc).r := by
        intro t
        refine Fin.cases ?_ (fun i => ?_) t
        · intro _
          rfl
        · intro hi
          simpa only [Fin.castSucc_succ, closePaths_internal] using
            hi i (by simp [internalEndpointSet])
      exact hleft t h
    · have hright : ∀ t : Fin (L + 1),
          (∀ v ∈ internalEndpointSet t, (x v).p = (x v).r) →
          (closePaths a x t.succ).p = (closePaths a x t.succ).r := by
        intro t
        refine Fin.lastCases ?_ (fun i => ?_) t
        · intro _
          simp [Fin.succ_last, closePaths_last, constantLabels]
        · intro hi
          simpa only [closePaths_internal] using
            hi i (by simp [internalEndpointSet])
      exact hright t h

/-- The product of endpoint indicators is exactly the full layer-coordinate
coincidence indicator, including either fixed external endpoint. -/
theorem endpointCoincidence_eq_layer_indicator {α : Type*} [DecidableEq α]
    {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind) (x : Assignments α τ)
    (t : Fin (L + 1)) :
    endpointCoincidence (internalEndpointSet t) x =
      if (zipLabels (closePaths a (fun v => (x v).val) t.castSucc)
          (closePaths a (fun v => (x v).val) t.succ)).p =
        (zipLabels (closePaths a (fun v => (x v).val) t.castSucc)
          (closePaths a (fun v => (x v).val) t.succ)).r then 1 else 0 := by
  simp only [endpointCoincidence, vertexPairEq, Fintype.prod_boole,
    layer_coordinate_eq_iff, Subtype.forall]

/-- Exact weighted count in terms of the actual layer coordinates of relaxed
endpoint-fixed path quadruples.  The sole combinatorial hypothesis is that the
selected layers have disjoint internal endpoint sets. -/
theorem sum_relaxedPaths_layer_corrections (α : Type*) [Fintype α]
    [DecidableEq α] [Nonempty α] {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → Fin (L + 1))
    (ht : Pairwise (fun i j => Disjoint (internalEndpointSet (t i))
      (internalEndpointSet (t j)))) (c : ι → ℝ) :
    (∑ x : RelaxedPaths α a τ, ∏ i,
      (1 + c i * if
        (zipLabels (closePaths a x.val (t i).castSucc)
          (closePaths a x.val (t i).succ)).p =
        (zipLabels (closePaths a x.val (t i).castSucc)
          (closePaths a x.val (t i).succ)).r then 1 else 0)) =
      (Fintype.card α : ℝ) ^ (2 * L - adjacentSwitches τ) *
        ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^
          normalEndpointCount τ (internalEndpointSet (t i))) := by
  calc
    _ = ∑ x : Assignments α τ, ∏ i,
        (1 + c i * endpointCoincidence (internalEndpointSet (t i)) x) := by
      apply Fintype.sum_equiv (relaxedPathsEquivAssignments α a τ)
      intro x
      apply Finset.prod_congr rfl
      intro i _
      rw [endpointCoincidence_eq_layer_indicator a τ]
      rfl
    _ = _ := sum_assignment_corrections α τ (fun i => internalEndpointSet (t i)) ht c

end Problem335.Pairings

end

end OAI
