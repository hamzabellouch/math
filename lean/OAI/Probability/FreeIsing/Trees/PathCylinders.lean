import OAI.Probability.FreeIsing.Spins.Kernel
import OAI.Probability.FreeIsing.Trees.ConnectedHull

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

theorem prefix_length_eq {d : ℕ} (v : TreeVertex d) {n : ℕ}
    (hn : n ≤ v.1.length) : (takeVertex v n).1.length = n := by
  simp [takeVertex, Nat.min_eq_left hn]

theorem mem_vertices {d : ℕ} {v u : TreeVertex d} :
    u ∈ vertices v ↔ ∃ n ≤ v.1.length, takeVertex v n = u := by
  classical
  simp only [vertices, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨n, by omega, heq⟩
  · rintro ⟨n, hn, heq⟩
    exact ⟨n, by omega, heq⟩

theorem prefix_mem_vertices {d : ℕ} (v : TreeVertex d) {n : ℕ}
    (hn : n ≤ v.1.length) : takeVertex v n ∈ vertices v :=
  mem_vertices.mpr ⟨n, hn, rfl⟩

theorem connected_vertices {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset (vertices v) := by
  have hmem : ∀ n ≤ v.1.length, takeVertex v n ∈ vertices v :=
    fun _ hn => prefix_mem_vertices v hn
  refine ⟨⟨root d, by simpa using hmem 0 (Nat.zero_le _)⟩, ?_⟩
  intro u hu w hw
  obtain ⟨i, hi, rfl⟩ := mem_vertices.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_vertices.mp hw
  exact (prefix_paths (vertices v) v hmem hi).2.trans
    (prefix_paths (vertices v) v hmem hj).1

def path {d : ℕ} (v : TreeVertex d) (i : Fin (v.1.length+1)) : TreeVertex d :=
  takeVertex v i

theorem path_injective {d : ℕ} (v : TreeVertex d) : Function.Injective (path v) := by
  intro i j h
  apply Fin.ext
  have hl := congrArg (fun x : TreeVertex d => x.1.length) h
  simpa only [path, prefix_length_eq v (Nat.le_of_lt_succ i.isLt),
    prefix_length_eq v (Nat.le_of_lt_succ j.isLt)] using hl

def pathEdge {d : ℕ} (v : TreeVertex d) (i : Fin v.1.length) :
    TreeVertex d × TreeVertex d := (path v i.castSucc, path v i.succ)

theorem pathEdge_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (pathEdge v) := by
  intro i j h
  have hi := path_injective v (congrArg Prod.fst h)
  exact Fin.ext (congrArg (fun x : Fin (v.1.length+1) => x.val) hi)

theorem vertices_eq_image_path {d : ℕ} (v : TreeVertex d) :
    vertices v = Finset.univ.image (path v) := by
  classical
  ext u
  simp only [mem_vertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨⟨n, by omega⟩, heq⟩
  · rintro ⟨i, heq⟩
    exact ⟨i, by omega, heq⟩

theorem inducedEdges_vertices {d : ℕ} (v : TreeVertex d) :
    inducedEdges (vertices v) = Finset.univ.image (pathEdge v) := by
  classical
  ext e
  rcases e with ⟨u,w⟩
  constructor
  · intro he
    obtain ⟨hmem, hadj, hlt⟩ := Finset.mem_filter.mp he
    obtain ⟨hu,hw⟩ := Finset.mem_product.mp hmem
    obtain ⟨i,hi,rfl⟩ := mem_vertices.mp hu
    obtain ⟨j,hj,rfl⟩ := mem_vertices.mp hw
    have hij : j = i+1 := by
      rcases hadj with ⟨c,hc⟩ | ⟨c,hc⟩
      · have hl := congrArg List.length hc
        simpa only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] using hl
      · have hl := congrArg List.length hc
        simp only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] at hl
        simp only [prefix_length_eq v hi, prefix_length_eq v hj] at hlt
        omega
    subst j
    exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨i,-,hei⟩ := Finset.mem_image.mp he
    rw [←hei]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, ?_, ?_⟩
    · exact prefix_mem_vertices v (Nat.le_of_lt i.isLt)
    · exact prefix_mem_vertices v (Nat.succ_le_of_lt i.isLt)
    · exact prefix_adj v i.isLt
    · change (takeVertex v i.val).1.length < (takeVertex v (i.val+1)).1.length
      rw [prefix_length_eq v (Nat.le_of_lt i.isLt),
        prefix_length_eq v (Nat.succ_le_of_lt i.isLt)]
      omega

theorem freeCylinderWeight_vertices {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta (vertices v) eta = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta (path v i.castSucc)) (eta (path v i.succ))) := by
  classical
  rw [freeCylinderWeight_eq_transitionKernel, inducedEdges_vertices,
    Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => pathEdge_injective v h

def pathAssignment {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) (u : TreeVertex d) : IsingSpin :=
  if h : u.1.length ≤ v.1.length then eta ⟨u.1.length, by omega⟩ else .neg

@[simp] theorem pathAssignment_path {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) (i : Fin (v.1.length+1)) :
    pathAssignment v eta (path v i) = eta i := by
  unfold pathAssignment path
  have hi := Nat.le_of_lt_succ i.isLt
  simp only [prefix_length_eq v hi, dite_eq_left hi]

theorem path_cylinder_eq {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) :
    {x : TreeVertex d → IsingSpin | ∀ u ∈ vertices v, x u = pathAssignment v eta u} =
      {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} := by
  classical
  ext x
  constructor
  · intro h i
    have hi : path v i ∈ vertices v :=
      prefix_mem_vertices v (Nat.le_of_lt_succ i.isLt)
    simpa only [pathAssignment_path] using h (path v i) hi
  · intro h u hu
    rw [vertices_eq_image_path] at hu
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hu
    simpa only [pathAssignment_path] using h i

theorem freeLaw_path_cylinder {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) (eta : Fin (v.1.length+1) → IsingSpin) :
    mu {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta i.castSucc) (eta i.succ)) := by
  have h := hmu (vertices v) (connected_vertices v) (pathAssignment v eta)
  rw [path_cylinder_eq, freeCylinderWeight_vertices] at h
  simpa only [pathAssignment_path] using h

end ConnectedHull
namespace ConnectedHull

@[simp] theorem path_zero {d : ℕ} (v : TreeVertex d) :
    path v 0 = root d := prefix_zero v

@[simp] theorem path_last {d : ℕ} (v : TreeVertex d) :
    path v (Fin.last v.1.length) = v := prefix_length v

theorem chain_product_nonneg {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (n : ℕ) (eta : Fin (n+1) → IsingSpin) :
    0 ≤ (1/2 : ℝ) * ∏ i : Fin n,
      transitionKernel theta (eta i.castSucc) (eta i.succ) := by
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _ => transitionKernel_nonneg hlo hhi _ _)

end ConnectedHull
namespace AlternatingPath

def word {α : Type*} (a b : α) : ℕ → List α
  | 0 => []
  | n+1 => a :: word b a n

@[simp] theorem word_length {α : Type*} (a b : α) (n : ℕ) :
    (word a b n).length = n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [word, List.length_cons, ih]

theorem word_isChain {α : Type*} (a b : α) (hab : a ≠ b) (n : ℕ) :
    List.IsChain (fun x y : α => x ≠ y) (word a b n) := by
  induction n generalizing a b with
  | zero => exact List.IsChain.nil
  | succ n ih =>
    cases n with
    | zero => exact List.IsChain.singleton a
    | succ n =>
      exact List.IsChain.cons_cons hab (ih b a hab.symm)

def vertex {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : TreeVertex d :=
  let a : Fin d := ⟨0, by omega⟩
  let b : Fin d := ⟨1, by omega⟩
  ⟨word a b n, word_isChain a b (by intro h; have := congrArg Fin.val h; simp at this) n⟩

@[simp] theorem vertex_length {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    (vertex hd n).1.length = n := word_length _ _ n

end AlternatingPath

theorem exists_treeVertex_length {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ v : TreeVertex d, v.1.length = n :=
  ⟨AlternatingPath.vertex hd n, AlternatingPath.vertex_length hd n⟩

end Problem367

end

end OAI
