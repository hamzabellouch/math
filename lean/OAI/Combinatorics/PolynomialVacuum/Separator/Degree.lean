import OAI.Combinatorics.PolynomialVacuum.Cylinder.ThreeSeams

namespace OAI

namespace PolynomialVacuumCylinder
open Classical

 
noncomputable def centralCut (n : ℕ) : Finset (Edge (2*n)) :=
  (Finset.range n).image (fun k : ℕ => ((((k+1 : ℕ) : ZMod (2*n)),0),0))

theorem central_step (M : ℕ) (k : ℕ) (E : Finset (Edge M))
    (h : ((((k+1 : ℕ) : ZMod M),0), (0 : Fin 3))∉E) :
    DualAdjacent E ((k : ZMod M),0) (((k+1 : ℕ) : ZMod M),0) := by
  refine ⟨((((k+1 : ℕ) : ZMod M),0),0),h,Or.inr ?_⟩
  simp [leftFace,rightFace,reverseGerm,neighbor]

theorem central_path (M k : ℕ) (E : Finset (Edge M))
    (h : ∀ j<k,((((j+1 : ℕ) : ZMod M),0), (0 : Fin 3))∉E) :
    Relation.ReflTransGen (DualAdjacent E) (0,0) ((k : ZMod M),0) := by
  induction k with
  | zero => simpa using (Relation.ReflTransGen.refl : Relation.ReflTransGen (DualAdjacent E) (0,0) (0,0))
  | succ k ih =>
    exact Relation.ReflTransGen.tail (ih (fun j hj => h j (by omega)))
      (central_step M k E (h k (by omega)))

theorem separator_meets_cut (n : ℕ) (P : Polygon (2*n))
    (hP : Separates P (0,0) ((n : ZMod (2*n)),0)) :
    ∃ e∈P.val,e∈centralCut n := by
  by_contra hn
  apply hP
  apply central_path
  intro j hj he
  apply hn
  exact ⟨((((j+1 : ℕ) : ZMod (2*n)),0),0),he,
    Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,by simp⟩⟩

theorem polygon_edge_vertex {M : ℕ} (P : Polygon M) (e : Edge M) (he : e∈P.val) :
    Vertex.up e.1.1 e.1.2∈P.vertices := by
  apply Finset.mem_biUnion.mpr
  exact ⟨e,he,by simp [edgeVertices]⟩

theorem separated_system_card_le (n : ℕ) (S : System n) : S.val.card≤n := by
  let pick : {P // P∈S.val} → Edge (2*n) := fun P => (separator_meets_cut n P.val (S.property.1 P.val P.property)).choose
  have hmem : ∀ P, pick P∈P.val.val ∧ pick P∈centralCut n :=
    fun P => (separator_meets_cut n P.val (S.property.1 P.val P.property)).choose_spec
  have hi : Function.Injective pick := by
    intro P Q h
    apply Subtype.ext
    by_contra hn
    have hd := S.property.2 P.property Q.property hn
    have hp := polygon_edge_vertex P.val (pick P) (hmem P).1
    have hq := polygon_edge_vertex Q.val (pick Q) (hmem Q).1
    rw [h] at hp
    exact (Finset.disjoint_left.mp hd) hp hq
  have hcard := Finset.card_le_card_of_injOn pick (s := (Finset.univ : Finset {P // P∈S.val}))
    (t := centralCut n) (by intro P _; exact (hmem P).2) (fun _ _ _ _ h => hi h)
  have hcut : (centralCut n).card≤n := (Finset.card_image_le).trans (by simp)
  simpa using hcard.trans hcut

end PolynomialVacuumCylinder

end OAI
