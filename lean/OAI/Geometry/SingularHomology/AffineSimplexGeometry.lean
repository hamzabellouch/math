import OAI.Geometry.SingularHomology.SimplexCoordinates
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

noncomputable section

namespace Problem340.AffineSimplex

variable {E : Type*} {n : ℕ}

def face (i : Fin (n + 1)) (v : Fin (n + 1) → E) : Fin n → E :=
  v ∘ i.succAbove

def cone (a : E) (v : Fin n → E) : Fin (n + 1) → E := Fin.cons a v

@[simp] lemma cone_zero (a : E) (v : Fin n → E) : cone a v 0 = a := by
  simp [cone]

@[simp] lemma cone_succ (a : E) (v : Fin n → E) (i : Fin n) :
    cone a v i.succ = v i := by
  simp [cone]

@[simp] lemma face_zero_cone (a : E) (v : Fin n → E) :
    face 0 (cone a v) = v := by
  funext i
  simp [face, cone]

@[simp] lemma face_succ_cone (a : E) (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    face i.succ (cone a v) = cone a (face i v) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [face, cone]
  | succ j => simp [face, cone]

lemma range_cone (a : E) (v : Fin n → E) :
    Set.range (cone a v) = insert a (Set.range v) := by
  simp [cone, Fin.range_cons]

section Realization

variable [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def realize (v : ι → E) (p : Convexity.StdSimplex ℝ ι) : E :=
  ∑ i, p i • v i

@[simp] lemma realize_vertex (v : ι → E) [DecidableEq ι] (i : ι) :
    realize v (Convexity.StdSimplex.single i) = v i := by
  simp [realize, Finsupp.single_apply]

lemma realize_cone (a : E) (v : Fin n → E) (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    realize (cone a v) p = p 0 • a + ∑ i : Fin n, p i.succ • v i := by
  simp [realize, Fin.sum_univ_succ]

lemma realize_comp_map (f : ι → κ) (v : κ → E) (p : Convexity.StdSimplex ℝ ι) :
    realize v (Convexity.StdSimplex.map f p) = realize (v ∘ f) p := by
  classical
  unfold realize
  simp only [RealSimplex.map_apply, Finset.sum_smul]
  calc
    (∑ y : κ, ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x • v y) =
        ∑ y : κ, ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x • v (f x) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x : ι, p x • (v ∘ f) x := by
      exact Finset.sum_fiberwise Finset.univ f (fun x => p x • v (f x))

lemma realize_face (v : Fin (n + 1) → E) (i : Fin (n + 1))
    (p : Convexity.StdSimplex ℝ (Fin n)) :
    realize v (Convexity.StdSimplex.map i.succAbove p) = realize (face i v) p :=
  realize_comp_map i.succAbove v p

lemma realize_mem {s : Set E} (hs : Convex ℝ s) (v : ι → E)
    (hv : ∀ i, v i ∈ s) (p : Convexity.StdSimplex ℝ ι) : realize v p ∈ s := by
  exact hs.sum_mem (fun i _ => p.weights_nonneg i) p.total_of_fintype
    (fun i _ => hv i)

lemma realize_mem_convexHull (v : ι → E) (p : Convexity.StdSimplex ℝ ι) :
    realize v p ∈ convexHull ℝ (Set.range v) :=
  realize_mem (convex_convexHull ℝ _) v
    (fun i => subset_convexHull ℝ _ (Set.mem_range_self i)) p

lemma realize_cone_mem_convexHull (v : Fin n → E) (a : E)
    (ha : a ∈ convexHull ℝ (Set.range v)) (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    realize (cone a v) p ∈ convexHull ℝ (Set.range v) := by
  apply realize_mem (convex_convexHull ℝ _)
  intro i
  cases i using Fin.cases with
  | zero => simpa using ha
  | succ i => simpa using subset_convexHull ℝ (Set.range v) (Set.mem_range_self i)

def barycenter [Nonempty ι] (v : ι → E) : E := realize v Convexity.StdSimplex.barycenter

lemma barycenter_mem_convexHull [Nonempty ι] (v : ι → E) :
    barycenter v ∈ convexHull ℝ (Set.range v) :=
  realize_mem_convexHull v _

lemma barycenter_eq_sum [Nonempty ι] (v : ι → E) :
    barycenter v = (Fintype.card ι : ℝ)⁻¹ • ∑ i, v i := by
  simp [barycenter, realize, Finset.smul_sum]

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

lemma continuous_realize (v : ι → E) : Continuous (realize v) := by
  unfold realize
  exact continuous_finsetSum _ (fun i _ =>
    (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const)

def realizeMap (v : ι → E) : C(Convexity.StdSimplex ℝ ι, E) :=
  ⟨realize v, continuous_realize v⟩

@[simp] lemma realizeMap_apply (v : ι → E) (p : Convexity.StdSimplex ℝ ι) :
    realizeMap v p = realize v p := rfl

lemma realizeMap_comp_map (f : ι → κ) (v : κ → E) :
    (realizeMap v).comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ =
      realizeMap (v ∘ f) := by
  ext p
  exact realize_comp_map f v p

def realizeIn (s : Set E) (hs : Convex ℝ s) (v : ι → E) (hv : ∀ i, v i ∈ s) :
    C(Convexity.StdSimplex ℝ ι, s) :=
  ⟨fun p => ⟨realize v p, realize_mem hs v hv p⟩,
    (continuous_realize v).subtype_mk _⟩

@[simp] lemma realizeIn_coe (s : Set E) (hs : Convex ℝ s)
    (v : ι → E) (hv : ∀ i, v i ∈ s) (p : Convexity.StdSimplex ℝ ι) :
    (realizeIn s hs v hv p : E) = realize v p := rfl

end Topology

end Realization

section SimplexTarget

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

def simplexRealizeMap (v : ι → Convexity.StdSimplex ℝ κ) :
    C(Convexity.StdSimplex ℝ ι, Convexity.StdSimplex ℝ κ) :=
  (⟨RealSimplex.coordinateHomeomorph.symm,
    RealSimplex.coordinateHomeomorph.symm.continuous⟩ :
      C(RealSimplex.coordinateSet κ, Convexity.StdSimplex ℝ κ)).comp
    (realizeIn (RealSimplex.coordinateSet κ) RealSimplex.convex_coordinateSet
      (fun i => (v i : κ → ℝ)) (fun i => RealSimplex.mem_coordinateSet (v i)))

@[simp] lemma simplexRealizeMap_coe (v : ι → Convexity.StdSimplex ℝ κ) (p : Convexity.StdSimplex ℝ ι) :
    (simplexRealizeMap v p : κ → ℝ) = realize (fun i => (v i : κ → ℝ)) p :=
  RealSimplex.coordinateHomeomorph_symm_apply _

lemma simplexRealizeMap_apply (v : ι → Convexity.StdSimplex ℝ κ) (p : Convexity.StdSimplex ℝ ι) (j : κ) :
    simplexRealizeMap v p j = ∑ i, p i * v i j := by
  rw [simplexRealizeMap_coe]
  simp [realize, Finset.sum_apply]

@[simp] lemma simplexRealizeMap_vertex (v : ι → Convexity.StdSimplex ℝ κ)
    [DecidableEq ι] (i : ι) : simplexRealizeMap v (Convexity.StdSimplex.single i) = v i := by
  apply RealSimplex.coordinates_injective
  exact (simplexRealizeMap_coe v _).trans (realize_vertex (fun j => (v j : κ → ℝ)) i)

lemma simplexRealizeMap_comp_map (f : ι → κ) (v : κ → Convexity.StdSimplex ℝ τ) :
    (simplexRealizeMap v).comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ =
      simplexRealizeMap (v ∘ f) := by
  ext p : 1
  apply RealSimplex.coordinates_injective
  change (simplexRealizeMap v (Convexity.StdSimplex.map f p) : τ → ℝ) =
    (simplexRealizeMap (v ∘ f) p : τ → ℝ)
  simp only [simplexRealizeMap_coe]
  exact realize_comp_map f (fun i => (v i : τ → ℝ)) p

lemma map_simplexRealizeMap (f : κ → τ) (v : ι → Convexity.StdSimplex ℝ κ)
    (p : Convexity.StdSimplex ℝ ι) :
    Convexity.StdSimplex.map f (simplexRealizeMap v p) =
      simplexRealizeMap (fun i => Convexity.StdSimplex.map f (v i)) p := by
  classical
  apply RealSimplex.coordinates_injective
  funext index
  change Convexity.StdSimplex.map f (simplexRealizeMap v p) index =
    simplexRealizeMap (fun i => Convexity.StdSimplex.map f (v i)) p index
  simp_rw [RealSimplex.map_apply, simplexRealizeMap_apply, RealSimplex.map_apply,
    Finset.mul_sum]
  exact Finset.sum_comm

lemma realize_simplexRealizeMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : κ → E) (w : ι → Convexity.StdSimplex ℝ κ) (p : Convexity.StdSimplex ℝ ι) :
    realize v (simplexRealizeMap w p) = realize (fun i => realize v (w i)) p := by
  unfold realize
  simp_rw [simplexRealizeMap_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

lemma simplexRealizeMap_assoc (v : κ → Convexity.StdSimplex ℝ τ)
    (w : ι → Convexity.StdSimplex ℝ κ) (p : Convexity.StdSimplex ℝ ι) :
    simplexRealizeMap v (simplexRealizeMap w p) =
      simplexRealizeMap (fun i => simplexRealizeMap v (w i)) p := by
  apply RealSimplex.coordinates_injective
  change (simplexRealizeMap v (simplexRealizeMap w p) : τ → ℝ) =
    (simplexRealizeMap (fun i => simplexRealizeMap v (w i)) p : τ → ℝ)
  simp only [simplexRealizeMap_coe]
  exact realize_simplexRealizeMap (fun j => (v j : τ → ℝ)) w p

def simplexBarycenter [Nonempty ι] (v : ι → Convexity.StdSimplex ℝ κ) : Convexity.StdSimplex ℝ κ :=
  simplexRealizeMap v Convexity.StdSimplex.barycenter

@[simp] lemma simplexBarycenter_coe [Nonempty ι] (v : ι → Convexity.StdSimplex ℝ κ) :
    (simplexBarycenter v : κ → ℝ) = barycenter (fun i => (v i : κ → ℝ)) :=
  simplexRealizeMap_coe v _

lemma simplexRealizeMap_barycenter [Nonempty ι]
    (v : κ → Convexity.StdSimplex ℝ τ) (w : ι → Convexity.StdSimplex ℝ κ) :
    simplexRealizeMap v (simplexBarycenter w) =
      simplexBarycenter (fun i => simplexRealizeMap v (w i)) :=
  simplexRealizeMap_assoc v w Convexity.StdSimplex.barycenter

lemma map_simplexBarycenter [Nonempty ι] (f : κ → τ) (v : ι → Convexity.StdSimplex ℝ κ) :
    Convexity.StdSimplex.map f (simplexBarycenter v) =
      simplexBarycenter (fun i => Convexity.StdSimplex.map f (v i)) :=
  map_simplexRealizeMap f v Convexity.StdSimplex.barycenter

lemma simplexBarycenter_mem_convexHull [Nonempty ι] (v : ι → Convexity.StdSimplex ℝ κ) :
    (simplexBarycenter v : κ → ℝ) ∈ convexHull ℝ (Set.range fun i => (v i : κ → ℝ)) := by
  rw [simplexBarycenter_coe]
  exact barycenter_mem_convexHull _

end SimplexTarget

end Problem340.AffineSimplex

end

end OAI
