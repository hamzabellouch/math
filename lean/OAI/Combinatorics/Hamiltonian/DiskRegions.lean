import OAI.Combinatorics.Hamiltonian.Quotients

namespace OAI

/-! Connected face regions and the exact disk Euler formula. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def regionEdges (A : Finset V) : Finset E :=
  Finset.univ.filter fun e => N.tail e ∈ A ∨ N.head e ∈ A

omit [Fintype V] in
@[simp] lemma mem_regionEdges (A : Finset V) (e : E) :
    e ∈ N.regionEdges A ↔ N.tail e ∈ A ∨ N.head e ∈ A := by
  simp [regionEdges]

def regionVertices (A : Finset V) : Finset F :=
  Finset.univ.filter fun z => ∃ e ∈ N.regionEdges A, D.Incident e z

omit [Fintype V] in
@[simp] lemma mem_regionVertices (A : Finset V) (z : F) :
    z ∈ N.regionVertices D A ↔ ∃ e ∈ N.regionEdges A, D.Incident e z := by
  simp [regionVertices]

def region (A : Finset V) : Network (N.regionVertices D A) (N.regionEdges A) where
  tail e := ⟨D.tail e.val, (N.mem_regionVertices D A _).mpr ⟨e.val,e.property,Or.inl rfl⟩⟩
  head e := ⟨D.head e.val, (N.mem_regionVertices D A _).mpr ⟨e.val,e.property,Or.inr rfl⟩⟩

omit [Fintype V] in
lemma region_map (A : Finset V) :
    (N.region D A).mapVertices Subtype.val = D.restrict (Subtype.val : N.regionEdges A → E) := rfl

omit [Fintype V] in
lemma region_boundary (A : Finset V) (x : N.regionEdges A → ℝ) :
    push (Subtype.val : N.regionVertices D A → F) ((N.region D A).boundary x) =
      D.boundary (push Subtype.val x) := by
  rw [← boundary_mapVertices, N.region_map, boundary_restrict]

omit [Fintype V] in
lemma push_subtype_apply (A : Finset V) (f : A → ℝ) (v : A) :
    push (Subtype.val : A → V) f v.val = f v := by
  have h := congrFun (pull_push_injective (E := V) Subtype.val_injective f) v
  exact h

omit [Fintype V] in
lemma push_subtype_outside (A : Finset V) (f : A → ℝ) {v : V} (hv : v ∉ A) :
    push (Subtype.val : A → V) f v = 0 :=
  push_eq_zero_outside f (by simpa using hv)

omit [Fintype V] in
lemma extend_gradient_outside (A : Finset V) (f : A → ℝ) {e : E}
    (he : e ∉ N.regionEdges A) : N.gradient (push (Subtype.val : A → V) f) e = 0 := by
  have hh : N.head e ∉ A := fun h => he ((N.mem_regionEdges A e).mpr (Or.inr h))
  have ht : N.tail e ∉ A := fun h => he ((N.mem_regionEdges A e).mpr (Or.inl h))
  simp only [gradient_apply, push_subtype_outside A f hh, push_subtype_outside A f ht, sub_self]

omit [Fintype V] in
lemma extend_restrict_gradient (A : Finset V) (f : A → ℝ) :
    push (Subtype.val : N.regionEdges A → E)
      (pull Subtype.val (N.gradient (push (Subtype.val : A → V) f))) =
        N.gradient (push (Subtype.val : A → V) f) := by
  ext e
  by_cases he : e ∈ N.regionEdges A
  · exact push_subtype_apply (N.regionEdges A) _ ⟨e,he⟩
  · rw [push_subtype_outside (N.regionEdges A) _ he]
    exact (N.extend_gradient_outside A f he).symm

omit [Fintype V] in

lemma region_connected (A : Finset V) (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    (N.region D A).graph.Connected := by
  let R := N.region D A
  have in_face {v : V} (hv : v ∈ A) {z : F} (hz : z ∈ Set.range (face v).corner) :
      z ∈ N.regionVertices D A := by
    obtain ⟨e,he,hz⟩ := ((face v).corner_iff_incident D z).mp hz
    have hv' := (N.mem_star e v).mp he
    have heA : e ∈ N.regionEdges A := by
      apply (N.mem_regionEdges A e).mpr
      exact hv'.elim (fun he => Or.inl (he ▸ hv)) (fun he => Or.inr (he ▸ hv))
    exact (N.mem_regionVertices D A z).mpr ⟨e,heA,hz⟩
  let a (v : {v // v ∈ A}) : N.regionVertices D A :=
    ⟨(face v.val).corner 0,in_face v.property ⟨0,rfl⟩⟩
  have local_path {v : V} (hv : v ∈ A) {z w : N.regionVertices D A}
      (hz : z.val ∈ Set.range (face v).corner) (hw : w.val ∈ Set.range (face v).corner) :
      R.graph.Reachable z w := by
    obtain ⟨i,hi⟩ := hz
    obtain ⟨j,hj⟩ := hw
    by_cases hij : i = j
    · have he : z = w := Subtype.ext (hi.symm.trans (hij ▸ hj))
      rw [he]
    · have hadj := (face v).clique D hij
      rw [hi,hj] at hadj
      obtain ⟨hne,e,he⟩ := hadj
      have heface : e ∈ N.star v := by
        have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
        rcases hfin i j hij with h | h
        · have ep : s(D.tail e,D.head e) = s(D.tail ((face v).edge i),D.head ((face v).edge i)) := by
            rw [(face v).edge_ends, ← h, hi, hj]
            exact Sym2.eq_iff.mpr he
          have ee := sD.pair_injective ep
          rw [ee]
          have hm : (face v).edge i ∈ Finset.univ.image (face v).edge :=
            Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
          rwa [(face v).edge_range] at hm
        · have ep : s(D.tail e,D.head e) = s(D.tail ((face v).edge j),D.head ((face v).edge j)) := by
            rw [(face v).edge_ends, ← h, hi, hj]
            exact Sym2.eq_iff.mpr he.symm
          rw [sD.pair_injective ep]
          have hm : (face v).edge j ∈ Finset.univ.image (face v).edge :=
            Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
          rwa [(face v).edge_range] at hm
      have heA : e ∈ N.regionEdges A := by
        rcases (N.mem_star e v).mp heface with h | h
        · exact (N.mem_regionEdges A e).mpr (Or.inl (h ▸ hv))
        · exact (N.mem_regionEdges A e).mpr (Or.inr (h ▸ hv))
      apply SimpleGraph.Adj.reachable
      refine ⟨fun h => hne (congrArg Subtype.val h),⟨e,heA⟩,?_⟩
      exact he.elim (fun h => Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩)
        (fun h => Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩)
  have step {v w : {v // v ∈ A}} (hvw : (N.graph.induce {v | v ∈ A}).Adj v w) :
      R.graph.Reachable (a v) (a w) := by
    obtain ⟨_,e,he⟩ := hvw
    have hv : N.Incident e v.val := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    have hw : N.Incident e w.val := he.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
    have hf (u : V) (hu : N.Incident e u) : D.tail e ∈ Set.range (face u).corner :=
      ((face u).corner_iff_incident D _).mpr ⟨e,(N.mem_star e u).mpr hu,Or.inl rfl⟩
    let z : N.regionVertices D A := ⟨D.tail e,in_face v.property (hf _ hv)⟩
    exact (local_path v.property ⟨0,rfl⟩ (hf _ hv)).trans
      (local_path w.property (z := z) (hf _ hw) ⟨0,rfl⟩)
  have all_faces {v w : {v // v ∈ A}} : R.graph.Reachable (a v) (a w) := by
    obtain ⟨p⟩ := hA v w
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih => exact (step h).trans ih
  obtain ⟨v₀⟩ := hA.nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨a v₀,?_⟩
  intro z
  obtain ⟨e,he,hz⟩ := (N.mem_regionVertices D A z.val).mp z.property
  rcases (N.mem_regionEdges A e).mp he with ht | hh
  · have hf := ((face (N.tail e)).corner_iff_incident D z.val).mpr
      ⟨e,(N.mem_star _ _).mpr (Or.inl rfl),hz⟩
    exact (all_faces (w := ⟨N.tail e,ht⟩)).trans (local_path ht ⟨0,rfl⟩ hf)
  · have hf := ((face (N.head e)).corner_iff_incident D z.val).mpr
      ⟨e,(N.mem_star _ _).mpr (Or.inr rfl),hz⟩
    exact (all_faces (w := ⟨N.head e,hh⟩)).trans (local_path hh ⟨0,rfl⟩ hf)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def regionCycleMap (A : Finset V) : (A → ℝ) →ₗ[ℝ] (N.regionEdges A → ℝ) :=
  (pull (Subtype.val : N.regionEdges A → E)).comp
    (N.gradient.comp (push (Subtype.val : A → V)))

omit [Fintype V] in
lemma regionCycleMap_injective (hN : N.graph.Connected) (A : Finset V)
    (hout : ∃ v, v ∉ A) : Function.Injective (N.regionCycleMap A) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  have hz : N.regionCycleMap A f = 0 := hf
  have hg : N.gradient (push (Subtype.val : A → V) f) = 0 := by
    rw [← N.extend_restrict_gradient A f]
    change push (Subtype.val : N.regionEdges A → E) (N.regionCycleMap A f) = 0
    rw [hz,map_zero]
  obtain ⟨r,hr⟩ := hout
  ext v
  have he := N.gradient_zero_reachable hg (hN r v.val)
  rw [push_subtype_outside A f hr, push_subtype_apply A f v] at he
  exact he.symm

omit [Fintype V] in
lemma region_cycles_eq_range (h : N.Duality D) (A : Finset V)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected) :
    (N.region D A).boundary.ker = (N.regionCycleMap A).range := by
  ext x
  constructor
  · intro hx
    have hx' : (N.region D A).boundary x = 0 := hx
    let y : E → ℝ := push (Subtype.val : N.regionEdges A → E) x
    have hy : D.boundary y = 0 := by
      rw [← N.region_boundary D A x, hx',map_zero]
    obtain ⟨f,hf⟩ : ∃ f, N.gradient f = y := by
      have hm : y ∈ D.boundary.ker := hy
      rw [h.dual_cycles_eq_cuts] at hm
      exact hm
    obtain ⟨r⟩ := hAc.nonempty
    have fstep {v w : {v // v ∉ A}}
        (hvw : (N.graph.induce {v | v ∉ A}).Adj v w) : f v.val = f w.val := by
      obtain ⟨_,e,he⟩ := hvw
      have heA : e ∉ N.regionEdges A := by
        rw [N.mem_regionEdges]
        exact he.elim (fun he => by rw [he.1,he.2]; exact not_or.mpr ⟨v.property,w.property⟩)
          (fun he => by rw [he.1,he.2]; exact not_or.mpr ⟨w.property,v.property⟩)
      have hy0 : y e = 0 := push_eq_zero_outside x (by simpa using heA)
      have heq := congrFun hf e
      rw [hy0,gradient_apply,sub_eq_zero] at heq
      exact he.elim (fun he => by rw [he.1,he.2] at heq; exact heq.symm)
        (fun he => by rwa [he.1,he.2] at heq)
    have fconstant (v : {v // v ∉ A}) : f v.val = f r.val := by
      obtain ⟨p⟩ := hAc v r
      induction p with
      | nil => rfl
      | cons h p ih => exact (fstep h).trans ih
    let u : A → ℝ := fun v => f v.val - f r.val
    have hext : push (Subtype.val : A → V) u = f - (fun _ => f r.val) := by
      ext v
      by_cases hv : v ∈ A
      · exact push_subtype_apply A u ⟨v,hv⟩
      · rw [push_subtype_outside A u hv]
        exact (sub_eq_zero.mpr (fconstant ⟨v,hv⟩)).symm
    refine ⟨u,?_⟩
    change pull (Subtype.val : N.regionEdges A → E) (N.gradient (push Subtype.val u)) = x
    rw [hext,map_sub,N.gradient_const,sub_zero,hf]
    exact pull_push_injective Subtype.val_injective x
  · rintro ⟨f,rfl⟩
    have hz : push (Subtype.val : N.regionVertices D A → F)
        ((N.region D A).boundary (N.regionCycleMap A f)) = 0 := by
      rw [N.region_boundary]
      change D.boundary (push (Subtype.val : N.regionEdges A → E)
        (pull Subtype.val (N.gradient (push (Subtype.val : A → V) f)))) = 0
      rw [N.extend_restrict_gradient]
      exact h.dual_conserved_gradient N D _
    have hh := congrArg (pull (Subtype.val : N.regionVertices D A → F)) hz
    rw [pull_push_injective Subtype.val_injective,map_zero] at hh
    exact hh

omit [Fintype V] in
lemma region_dim_cycles (h : N.Duality D) (A : Finset V)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected) :
    Module.finrank ℝ (N.region D A).boundary.ker = A.card := by
  rw [N.region_cycles_eq_range D h A hAc,
    LinearMap.finrank_range_of_inj (N.regionCycleMap_injective h.connected A ?_),
    Module.finrank_pi,Fintype.card_coe]
  obtain ⟨v⟩ := hAc.nonempty
  exact ⟨v.val,v.property⟩

omit [Fintype V] in

theorem region_euler (h : N.Duality D) (A : Finset V)
    (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    A.card + (N.regionVertices D A).card = (N.regionEdges A).card + 1 := by
  have hh := (N.region D A).dim_cycles (N.region_connected D A hA sD face)
  rwa [N.region_dim_cycles D h A hAc,Fintype.card_coe,Fintype.card_coe] at hh

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma sum_stars (hN : N.Simple) (A : Finset V) :
    ∑ v ∈ A, (N.star v).card =
      ∑ e, ((if N.tail e ∈ A then 1 else 0) + (if N.head e ∈ A then 1 else 0)) := by
  calc
    ∑ v ∈ A, (N.star v).card =
      ∑ v ∈ A, ∑ e, ((if N.tail e = v then 1 else 0) + (if N.head e = v then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [star,Finset.card_filter]
        simp only [Incident]
        apply Finset.sum_congr rfl
        intro e _
        have hne := hN.loopless e
        by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simp [Finset.sum_add_distrib]

lemma cubic_region_count (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (A : Finset V) :
    3 * A.card + (N.cut A).card = 2 * (N.regionEdges A).card := by
  have hsum := N.sum_stars hN A
  have hv : (∑ v ∈ A, (N.star v).card) = 3 * A.card := by
    have hc' : ∀ v, N.graph.degree v = 3 := hc
    simp only [N.card_star hN,hc']
    simp [Nat.mul_comm]
  rw [hv] at hsum
  rw [hsum]
  simp only [cut,regionEdges,Finset.card_filter,
    ← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;> simp [ht,hh]

lemma disk_euler_count (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (A : Finset V)
    (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    (A.card : ℤ) = 2 * (N.regionVertices D A).card - (N.cut A).card - 2 := by
  have he := N.region_euler D h A hA hAc sD face
  have hc := N.cubic_region_count hN hc A
  omega

end
end Barnette.Network

end OAI
