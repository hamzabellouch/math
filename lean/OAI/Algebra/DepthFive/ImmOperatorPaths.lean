import OAI.Algebra.DepthFive.Basic
import OAI.Algebra.DepthFive.MatrixPaths
import OAI.Algebra.DepthFive.MixedOperator

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open MvPolynomial

/-- Enumerating labelled matrix paths never repeats an edge list. -/
private theorem immOperatorPaths_enumeration_nodup {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) : (matrixEntryPaths labels i j).Nodup := by
  induction labels generalizing i with
  | nil => by_cases hij : i = j <;> simp [matrixEntryPaths, hij]
  | cons t ts ih =>
    cases ts with
    | nil => simp [matrixEntryPaths]
    | cons u us =>
      rw [matrixEntryPaths, List.nodup_flatMap]
      constructor
      · intro k hk
        exact List.Nodup.map (fun p q h => (List.cons.inj h).2) (ih k)
      · apply (Finset.nodup_toList _).pairwise_of_forall_ne
        intro a ha b hb hab p hp hq
        obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hp
        obtain ⟨r, hr, heq⟩ := List.mem_map.mp hq
        simp only [List.cons.injEq, Prod.mk.injEq] at heq
        exact hab heq.1.2.2.symm

/-- The canonical labelled paths contributing to the endpoint IMM entry. -/
def immPaths (n : ℕ) (hn : 0 < n) : List (List (Fin n × Fin n × Fin n)) :=
  matrixEntryPaths (List.finRange n) ⟨0, hn⟩ ⟨0, hn⟩

/-- Every IMM path uses exactly one coordinate in each layer, in layer order. -/
theorem immPaths_labels (n : ℕ) (hn : 0 < n)
    (p : List (Fin n × Fin n × Fin n)) (hp : p ∈ immPaths n hn) :
    p.map Prod.fst = List.finRange n :=
  matrixEntryPaths_labels _ _ _ _ hp

/-- Distinct path indices select distinct edge lists. -/
theorem immPaths_get_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (immPaths n hn).get := by
  apply List.nodup_iff_injective_get.mp
  exact immOperatorPaths_enumeration_nodup _ _ _

/-- The number of endpoint paths is `n^(n-1)`. -/
theorem immPaths_length (n : ℕ) (hn : 0 < n) :
    (immPaths n hn).length = n ^ (n - 1) := by
  unfold immPaths
  rw [matrixEntryPaths_length _ (by simpa using (Nat.ne_of_gt hn))]
  simp

variable {K : Type*} [CommSemiring K]

/-- The endpoint IMM polynomial is the sum of its labelled path monomials. -/
theorem imm_eq_sum_path_products (n : ℕ) (hn : 0 < n) :
    imm K n = ((immPaths n hn).map fun p => (p.map (X (R := K))).prod).sum := by
  have h := matrixEntryPaths_sum_prod (immLayer K n) (List.finRange n)
    (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  simp only [imm, dite_eq_left hn, List.ofFn_eq_map]
  exact h.symm

/-- The full IMM polynomial operator is a sum of products of its edge operators. -/
theorem mixedOperator_imm_eq_sum_paths (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool) :
    mixedOperator (K := K) isV (imm K n) =
      ((immPaths n hn).map fun p =>
        (p.map (variableOperator (K := K) isV)).prod).sum := by
  rw [imm_eq_sum_path_products n hn, map_list_sum]
  simp only [List.map_map, Function.comp_def, map_list_prod, mixedOperator_X]

/-- Each individual IMM path contains no repeated variable. -/
theorem immPaths_nodup (n : ℕ) (hn : 0 < n)
    (p : List (Fin n × Fin n × Fin n)) (hp : p ∈ immPaths n hn) : p.Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [immPaths_labels n hn p hp]
  exact List.nodup_finRange n

/-- The operator expansion indexed by the finite type of paths. -/
theorem mixedOperator_imm_eq_sum_paths_fin (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool) :
    mixedOperator (K := K) isV (imm K n) =
      ∑ p : Fin (immPaths n hn).length,
        (((immPaths n hn).get p).map (variableOperator (K := K) isV)).prod := by
  rw [mixedOperator_imm_eq_sum_paths n hn isV]
  symm
  simpa only [List.get_eq_getElem] using
    (Fin.sum_univ_fun_getElem (immPaths n hn)
      (fun p => (p.map (variableOperator (K := K) isV)).prod))

/-- Applying the IMM operator is the sum of its individual path actions. -/
theorem mixedOperator_imm_apply_eq_sum_paths (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (f : MvPolynomial (Fin n × Fin n × Fin n) K) :
    mixedOperator isV (imm K n) f =
      ∑ p : Fin (immPaths n hn).length,
        ((((immPaths n hn).get p).map (variableOperator isV)).prod) f := by
  rw [mixedOperator_imm_eq_sum_paths_fin n hn isV, LinearMap.sum_apply]

/-- Coefficients of the IMM operator are finite sums of path coefficients. -/
theorem coeff_mixedOperator_imm_eq_sum_paths (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (f : MvPolynomial (Fin n × Fin n × Fin n) K)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) :
    (mixedOperator isV (imm K n) f).coeff d =
      ∑ p : Fin (immPaths n hn).length,
        (((((immPaths n hn).get p).map (variableOperator isV)).prod) f).coeff d := by
  rw [mixedOperator_imm_apply_eq_sum_paths n hn isV f, coeff_sum]

/-- Extend internal vertex choices by the two fixed endpoint vertices. -/
def immInternalPathVertices (d : ℕ) (p : Fin d → Fin (d + 1)) :
    Fin (d + 2) → Fin (d + 1) :=
  Fin.cons (α := fun _ => Fin (d + 1)) 0 (Fin.snoc p 0)

/-- The edge list associated to the tuple of internal vertices. -/
def immInternalPathEdges (d : ℕ) (p : Fin d → Fin (d + 1)) :
    List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) :=
  List.ofFn fun t : Fin (d + 1) =>
    (t, Fin.cons (α := fun _ => Fin (d + 1)) 0 p t,
      Fin.snoc (α := fun _ => Fin (d + 1)) p 0 t)

@[simp] theorem immInternalPathVertices_start (d : ℕ) (p : Fin d → Fin (d + 1)) :
    immInternalPathVertices d p 0 = 0 := by
  simp [immInternalPathVertices]

@[simp] theorem immInternalPathVertices_end (d : ℕ) (p : Fin d → Fin (d + 1)) :
    immInternalPathVertices d p (Fin.last (d + 1)) = 0 := by
  simp [immInternalPathVertices]

@[simp] theorem immInternalPathVertices_castSucc (d : ℕ)
    (p : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    immInternalPathVertices d p t.castSucc =
      Fin.cons (α := fun _ => Fin (d + 1)) 0 p t := by
  simp [immInternalPathVertices, Fin.cons_snoc_eq_snoc_cons]

@[simp] theorem immInternalPathVertices_succ (d : ℕ)
    (p : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    immInternalPathVertices d p t.succ =
      Fin.snoc (α := fun _ => Fin (d + 1)) p 0 t := by
  simp [immInternalPathVertices]

/-- Extending by endpoints does not identify different internal paths. -/
theorem immInternalPathVertices_injective (d : ℕ) :
    Function.Injective (immInternalPathVertices d) := by
  intro p q h
  funext t
  have hh := congrFun h t.castSucc.succ
  simpa [immInternalPathVertices] using hh

/-- The edge list has every layer as its first coordinate, exactly once. -/
theorem immInternalPathEdges_labels (d : ℕ) (p : Fin d → Fin (d + 1)) :
    (immInternalPathEdges d p).map Prod.fst = List.finRange (d + 1) := by
  rw [immInternalPathEdges, List.map_ofFn]
  exact List.ofFn_id _

/-- Internal-vertex edge lists have no repeated variable. -/
theorem immInternalPathEdges_nodup (d : ℕ) (p : Fin d → Fin (d + 1)) :
    (immInternalPathEdges d p).Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [immInternalPathEdges_labels]
  exact List.nodup_finRange _

/-- The IMM expansion using the canonical tuple of internal vertices. -/
theorem imm_succ_eq_sum_internal_paths (d : ℕ) :
    imm K (d + 1) = ∑ p : Fin d → Fin (d + 1),
      ((immInternalPathEdges d p).map (X (R := K))).prod := by
  simp only [imm, Nat.succ_pos, dite_eq_left]
  rw [matrix_ofFn_prod_eq_sum_paths]
  simp [immInternalPathEdges, List.map_ofFn, Function.comp_def, immLayer]

/-- The actual IMM operator as a sum over internal vertex tuples. -/
theorem mixedOperator_imm_succ_eq_sum_internal_paths (d : ℕ)
    (isV : (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) → Bool) :
    mixedOperator (K := K) isV (imm K (d + 1)) =
      ∑ p : Fin d → Fin (d + 1),
        ((immInternalPathEdges d p).map (variableOperator (K := K) isV)).prod := by
  rw [imm_succ_eq_sum_internal_paths d, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [map_list_prod, List.map_map, Function.comp_def, mixedOperator_X]

end Problem335

end

end OAI
