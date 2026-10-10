import OAI.Algebra.DepthFive.MatrixPaths

namespace OAI

noncomputable section

namespace Problem335

variable {σ ι : Type*}

/-- Record the edges of a path from its internal vertices and fixed endpoints. -/
def internalPathEdges {d : ℕ} (labels : Fin (d + 1) → σ) (i j : ι)
    (p : Fin d → ι) : List (σ × ι × ι) :=
  List.ofFn fun t : Fin (d + 1) =>
    (labels t, Fin.cons (α := fun _ => ι) i p t, Fin.snoc (α := fun _ => ι) p j t)

theorem internalPathEdges_mem [Fintype ι] [DecidableEq ι]
    (d : ℕ) (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    internalPathEdges labels i j p ∈ matrixEntryPaths (List.ofFn labels) i j := by
  induction d generalizing i with
  | zero => simp [internalPathEdges, List.ofFn_succ, matrixEntryPaths, Fin.snoc_zero]
  | succ d ih =>
      rw [← Fin.cons_self_tail p]
      unfold internalPathEdges
      rw [List.ofFn_succ, List.ofFn_succ]
      conv_rhs => rw [List.ofFn_succ]
      rw [matrixEntryPaths]
      apply List.mem_flatMap.mpr
      refine ⟨p 0, by simp, ?_⟩
      apply List.mem_map.mpr
      refine ⟨internalPathEdges (Fin.tail labels) (p 0) j (Fin.tail p), ?_, ?_⟩
      · simpa only [List.ofFn_succ, Fin.tail] using
          ih (Fin.tail labels) (p 0) (Fin.tail p)
      · simp only [internalPathEdges, ← Fin.cons_snoc_eq_snoc_cons,
          Fin.cons_zero, Fin.cons_succ, Fin.tail]

theorem internalPathEdges_injective {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) :
    Function.Injective (internalPathEdges labels i j) := by
  intro p q h
  have hf := List.ofFn_injective h
  funext t
  have ht := congrArg (fun f => (f t.castSucc).2.2) hf
  simpa only [Fin.snoc_castSucc] using ht

/-- Locate the explicitly described path in the exact list enumeration. -/
def internalPathIndex [Fintype ι] [DecidableEq ι] {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    Fin (matrixEntryPaths (List.ofFn labels) i j).length :=
  Classical.choose (List.mem_iff_get.mp (internalPathEdges_mem d labels i j p))

@[simp] theorem get_internalPathIndex [Fintype ι] [DecidableEq ι] {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    (matrixEntryPaths (List.ofFn labels) i j).get (internalPathIndex labels i j p) =
      internalPathEdges labels i j p :=
  Classical.choose_spec (List.mem_iff_get.mp (internalPathEdges_mem d labels i j p))

theorem internalPathIndex_injective [Fintype ι] [DecidableEq ι] {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) :
    Function.Injective (internalPathIndex labels i j) := by
  intro p q h
  apply internalPathEdges_injective labels i j
  rw [← get_internalPathIndex labels i j p, ← get_internalPathIndex labels i j q, h]

/-- The canonical matrix-path list and the tuple of internal vertices enumerate
exactly the same paths. The edge list is preserved, not merely its cardinality. -/
def internalPathEquiv [Fintype ι] [DecidableEq ι] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) :
    (Fin d → ι) ≃ Fin (matrixEntryPaths (List.ofFn labels) i j).length :=
  Equiv.ofBijective (internalPathIndex labels i j)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨internalPathIndex_injective labels i j, by
      simp only [Fintype.card_fun, Fintype.card_fin]
      rw [matrixEntryPaths_length _ (by simp) i j]
      simp⟩)

@[simp] theorem get_internalPathEquiv [Fintype ι] [DecidableEq ι] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    (matrixEntryPaths (List.ofFn labels) i j).get (internalPathEquiv d labels i j p) =
      internalPathEdges labels i j p := get_internalPathIndex labels i j p

/-- Vertex paths with both external endpoints fixed. -/
def EndpointPath (d : ℕ) (i j : ι) :=
  {v : Fin (d + 2) → ι // v 0 = i ∧ v (Fin.last (d + 1)) = j}

/-- Adjoining the two endpoints identifies arbitrary internal-vertex tuples with
endpoint-fixed vertex paths. -/
def endpointPathEquiv (d : ℕ) (i j : ι) : (Fin d → ι) ≃ EndpointPath d i j where
  toFun p := ⟨Fin.cons i (Fin.snoc p j), by simp⟩
  invFun v := Fin.init (Fin.tail v.1)
  left_inv p := by simp
  right_inv := by
    rintro ⟨v, hi, hj⟩
    apply Subtype.ext
    change Fin.cons i (Fin.snoc (Fin.init (Fin.tail v)) j) = v
    have hj' : (Fin.tail v) (Fin.last d) = j := by simpa [Fin.tail] using hj
    rw [← hj', Fin.snoc_init_self, ← hi, Fin.cons_self_tail]

/-- Representation bridge from endpoint-fixed vertices to canonical list-based paths. -/
def endpointPathIndexEquiv [Fintype ι] [DecidableEq ι] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) :
    EndpointPath d i j ≃ Fin (matrixEntryPaths (List.ofFn labels) i j).length :=
  (endpointPathEquiv d i j).symm.trans (internalPathEquiv d labels i j)

/-- The representation equivalence preserves the exact ordered edge list. -/
@[simp] theorem get_endpointPathIndexEquiv [Fintype ι] [DecidableEq ι] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) (v : EndpointPath d i j) :
    (matrixEntryPaths (List.ofFn labels) i j).get
      (endpointPathIndexEquiv d labels i j v) =
      List.ofFn (fun t : Fin (d + 1) => (labels t, v.1 t.castSucc, v.1 t.succ)) := by
  obtain ⟨p, rfl⟩ := (endpointPathEquiv d i j).surjective v
  simp only [endpointPathIndexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    get_internalPathEquiv]
  unfold internalPathEdges
  apply congrArg List.ofFn
  funext t
  change (labels t, Fin.cons (α := fun _ => ι) i p t,
      Fin.snoc (α := fun _ => ι) p j t) =
    (labels t, Fin.cons (α := fun _ => ι) i (Fin.snoc (α := fun _ => ι) p j) t.castSucc,
      Fin.cons (α := fun _ => ι) i (Fin.snoc (α := fun _ => ι) p j) t.succ)
  rw [Fin.cons_succ, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc]

instance endpointPathFintype [Fintype ι] (d : ℕ) (i j : ι) :
    Fintype (EndpointPath d i j) :=
  Fintype.ofEquiv (Fin d → ι) (endpointPathEquiv d i j)

@[simp] theorem card_endpointPath [Fintype ι] (d : ℕ) (i j : ι) :
    Fintype.card (EndpointPath d i j) = Fintype.card ι ^ d := by
  simpa using Fintype.card_congr (endpointPathEquiv d i j).symm

open scoped BigOperators

/-- Reindex any path statistic from enumerated paths to internal vertices. -/
theorem sum_matrixEntryPaths_eq_sum_internal [Fintype ι] [DecidableEq ι]
    {R : Type*} [AddCommMonoid R] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) (f : List (σ × ι × ι) → R) :
    (∑ p : Fin (matrixEntryPaths (List.ofFn labels) i j).length,
      f ((matrixEntryPaths (List.ofFn labels) i j).get p)) =
      ∑ p : Fin d → ι, f (internalPathEdges labels i j p) := by
  simpa only [get_internalPathEquiv] using
    (Equiv.sum_comp (internalPathEquiv d labels i j)
      (fun p => f ((matrixEntryPaths (List.ofFn labels) i j).get p))).symm

/-- Reindex any path statistic to the endpoint-fixed vertex representation.
This can be applied once per path in the four-path trace expansion. -/
theorem sum_matrixEntryPaths_eq_sum_vertices [Fintype ι] [DecidableEq ι]
    {R : Type*} [AddCommMonoid R] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) (f : List (σ × ι × ι) → R) :
    (∑ p : Fin (matrixEntryPaths (List.ofFn labels) i j).length,
      f ((matrixEntryPaths (List.ofFn labels) i j).get p)) =
      ∑ v : EndpointPath d i j,
        f (List.ofFn (fun t : Fin (d + 1) => (labels t, v.1 t.castSucc, v.1 t.succ))) := by
  simpa only [get_endpointPathIndexEquiv] using
    (Equiv.sum_comp (endpointPathIndexEquiv d labels i j)
      (fun p => f ((matrixEntryPaths (List.ofFn labels) i j).get p))).symm

/-- Additive edge statistics, including signed exponent shifts, are preserved. -/
theorem sum_get_endpointPathIndexEquiv [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommMonoid A] (d : ℕ) (labels : Fin (d + 1) → σ)
    (i j : ι) (v : EndpointPath d i j) (f : σ × ι × ι → A) :
    (((matrixEntryPaths (List.ofFn labels) i j).get
      (endpointPathIndexEquiv d labels i j v)).map f).sum =
      ∑ t : Fin (d + 1), f (labels t, v.1 t.castSucc, v.1 t.succ) := by
  rw [get_endpointPathIndexEquiv]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- Multiplicative edge statistics, including path amplitudes, are preserved. -/
theorem prod_get_endpointPathIndexEquiv [Fintype ι] [DecidableEq ι]
    {A : Type*} [CommMonoid A] (d : ℕ) (labels : Fin (d + 1) → σ)
    (i j : ι) (v : EndpointPath d i j) (f : σ × ι × ι → A) :
    (((matrixEntryPaths (List.ofFn labels) i j).get
      (endpointPathIndexEquiv d labels i j v)).map f).prod =
      ∏ t : Fin (d + 1), f (labels t, v.1 t.castSucc, v.1 t.succ) := by
  rw [get_endpointPathIndexEquiv]
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def]

end Problem335

end

end OAI
