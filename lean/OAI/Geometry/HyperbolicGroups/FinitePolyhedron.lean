import Mathlib

namespace OAI

section


/-! Literal barycentric realizations of finite abstract complexes. No abstract
CW or homotopy replacement is used in the definitions. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V]

def simplex (s : Finset V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧ ∀ i, i ∉ s → x i = 0}

def carrierSet (K : AbstractSimplicialComplex V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
    ∃ s ∈ K.faces, ∀ i, i ∉ s → x i = 0}

abbrev Carrier (K : AbstractSimplicialComplex V) := carrierSet K

lemma simplex_convex (s : Finset V) : Convex ℝ (simplex s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ←Finset.mul_sum, hx.2.1, hy.2.1, mul_one, hab]
  · intro i hi
    simp [hx.2.2 i hi, hy.2.2 i hi]

lemma simplex_closed (s : Finset V) : IsClosed (simplex s) := by
  change IsClosed ({point : V → ℝ | ∀ index, 0 ≤ point index} ∩
    ({point : V → ℝ | (∑ index, point index) = 1} ∩
      {point : V → ℝ | ∀ index, index ∉ s → point index = 0}))
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun index =>
      isClosed_le continuous_const (continuous_apply index)
  · apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun index => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply index) continuous_const

lemma simplex_compact (s : Finset V) : IsCompact (simplex s) := by
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : V → ℝ) 1)).of_isClosed_subset
    (simplex_closed s) ?_
  intro point hpoint
  refine ⟨hpoint.1, fun index => ?_⟩
  calc
    point index ≤ ∑ other, point other :=
      Finset.single_le_sum (fun other _ => hpoint.1 other) (Finset.mem_univ index)
    _ = 1 := hpoint.2.1

lemma carrierSet_eq_union (K : AbstractSimplicialComplex V) :
    carrierSet K = ⋃ s ∈ K.faces, simplex s := by
  ext x
  simp only [carrierSet, Set.mem_ofPred_eq, Set.mem_iUnion, simplex]
  exact ⟨fun ⟨h0,h1,s,hs,hx⟩ => ⟨s,hs,h0,h1,hx⟩,
    fun ⟨s,hs,h0,h1,hx⟩ => ⟨h0,h1,s,hs,hx⟩⟩

lemma carrierSet_compact (K : AbstractSimplicialComplex V) : IsCompact (carrierSet K) := by
  rw [carrierSet_eq_union]
  exact Set.toFinite K.faces |>.isCompact_biUnion (fun s _ => simplex_compact s)

instance (K : AbstractSimplicialComplex V) : CompactSpace (Carrier K) :=
  isCompact_iff_compactSpace.mp (carrierSet_compact K)

def vertex (K : AbstractSimplicialComplex V) (v : V) : Carrier K := by
  classical
  exact ⟨Pi.single v 1, by
    refine ⟨?_, ?_, {v}, K.singleton_mem v, ?_⟩
    · intro i
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      simp [hi]⟩

lemma vertex_mem_simplex (K : AbstractSimplicialComplex V) {s : Finset V} {v : V} (hv : v ∈ s) :
    (vertex K v).val ∈ simplex s := by
  refine ⟨(vertex K v).property.1, (vertex K v).property.2.1, ?_⟩
  intro i hi
  have hne : i ≠ v := by rintro rfl; exact hi hv
  simp [vertex, hne]

lemma simplex_subset_carrier (K : AbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K.faces) :
    simplex s ⊆ carrierSet K :=
  fun _ hx => ⟨hx.1,hx.2.1,s,hs,hx.2.2⟩

lemma joined_of_simplex (K : AbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K.faces)
    (x y : Carrier K) (hx : x.val ∈ simplex s) (hy : y.val ∈ simplex s) : Joined x y := by
  exact (((simplex_convex s).isPathConnected ⟨x.val,hx⟩).joinedIn x.val hx y.val hy).mono
    (simplex_subset_carrier K hs) |>.joined_subtype

lemma vertex_joined_of_edge [DecidableEq V] (K : AbstractSimplicialComplex V) {a b : V}
    (hab : {a,b} ∈ K.faces) : Joined (vertex K a) (vertex K b) :=
  joined_of_simplex K hab _ _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp))

lemma exists_joined_vertex (K : AbstractSimplicialComplex V) (x : Carrier K) :
    ∃ v : V, Joined x (vertex K v) := by
  obtain ⟨s,hs,hx⟩ := x.property.2.2
  obtain ⟨v,hv⟩ := (K.isRelLowerSet_faces hs).1
  exact ⟨v,joined_of_simplex K hs x _ ⟨x.property.1,x.property.2.1,hx⟩ (vertex_mem_simplex K hv)⟩

lemma pathConnected_of_vertex_connected (K : AbstractSimplicialComplex V) (v : V)
    (h : ∀ w, Joined (vertex K v) (vertex K w)) : PathConnectedSpace (Carrier K) := by
  refine ⟨⟨vertex K v⟩, fun x y => ?_⟩
  obtain ⟨a,ha⟩ := exists_joined_vertex K x
  obtain ⟨b,hb⟩ := exists_joined_vertex K y
  exact ha.trans ((h a).symm.trans ((h b).trans hb.symm))

end HyperbolicObstruction.FinitePolyhedron
end
end

section

end

end OAI
