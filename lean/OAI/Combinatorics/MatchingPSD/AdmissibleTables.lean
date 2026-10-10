import OAI.Combinatorics.MatchingPSD.GlobalGeometry

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ColorTransport
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
noncomputable def colorEquiv (f : A → C) (g : B → C) (h : histogram f = histogram g) : A ≃ B :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fun c => Fintype.equivOfCardEq (congrFun h c))).trans
      (Equiv.sigmaFiberEquiv g))

omit [Fintype C] in
lemma colorEquiv_spec (f : A → C) (g : B → C) (h : histogram f = histogram g) (a : A) :
    g (colorEquiv f g h a) = f a := by
  exact (Fintype.equivOfCardEq (congrFun h (f a)) ⟨a,rfl⟩).property
end ColorTransport

def typePair : Fin 6 → Fin 3 × Fin 3 := ![(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
abbrev TypedEdges (E : Fin 6 → ℕ) := (t : Fin 6) × Fin (E t)
def edgeColor (E : Fin 6 → ℕ) : TypedEdges E × Bool → Fin 3 :=
  fun v => if v.2 then (typePair v.1.1).2 else (typePair v.1.1).1

def endpointSizes (E : Fin 6 → ℕ) : Fin 3 → ℕ :=
  ![2*E 0+E 1+E 2, E 1+2*E 3+E 4, E 2+E 4+2*E 5]

lemma edgeColor_histogram (E : Fin 6 → ℕ) : histogram (edgeColor E) = endpointSizes E := by
  funext c
  apply Nat.cast_injective (R := ℝ)
  rw [histogram_cast_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_bool]
  fin_cases c <;> simp [edgeColor, endpointSizes, typePair, Fin.sum_univ_succ] <;> ring

lemma edgeColor_cross (E : Fin 6 → ℕ) (i : Fin 3) :
    crossCoordinate (edgeColor E) i (standardPairing (H := TypedEdges E)) =
      (![E 1,E 2,E 4] i : ℝ) := by
  simp only [crossCoordinate, tableCoordinate, Fintype.sum_prod_type,
    Fintype.sum_sigma, Fintype.sum_bool]
  fin_cases i <;> simp [crossPair, standardPairing, edgeColor, typePair, Fin.sum_univ_succ]

lemma exists_pairing_of_endpoints {V : Type u_4} [Fintype V]
    (z : V → Fin 3) (E : Fin 6 → ℕ) (hz : histogram z = endpointSizes E) :
    ∃ M : Pairing V, ∀ i : Fin 3, crossCoordinate z i M = (![E 1,E 2,E 4] i : ℝ) := by
  let e := colorEquiv (edgeColor E) z ((edgeColor_histogram E).trans hz.symm)
  have he : z ∘ e = edgeColor E := funext (colorEquiv_spec _ _ _)
  refine ⟨Pairing.transport e standardPairing, ?_⟩
  intro i
  rw [crossCoordinate, tableCoordinate_transport, he]
  exact edgeColor_cross E i

abbrev TripleVertices (s : ℕ) := (Fin (2*s+1) ⊕ Fin (2*s+1)) ⊕ (Fin s × Bool)
def tripleColor {s : ℕ} : TripleVertices s → Fin 3 :=
  Sum.elim (Sum.elim (fun _ => 0) (fun _ => 1)) (fun _ => 2)

lemma tripleColor_histogram (s : ℕ) :
    histogram (@tripleColor s) = ![2*s+1,2*s+1,2*s] := by
  funext c
  apply Nat.cast_injective (R := ℝ)
  rw [histogram_cast_sum]
  fin_cases c <;> simp [tripleColor, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_mul]; ring

lemma triple_card (s : ℕ) : Fintype.card (TripleVertices s) = 2*(3*s+1) := by
  simp only [TripleVertices, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool]
  omega

noncomputable def tripleEquiv (s : ℕ) : TripleVertices s ≃ Vertices (3*s+1) :=
  Fintype.equivOfCardEq (by
    change Fintype.card (TripleVertices s) = Fintype.card (Fin (3*s+1) × Bool)
    rw [triple_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)

lemma triple_histogram_pos {s : ℕ} (hs : 0 < s) (i : Fin 3) :
    0 < histogram (@tripleColor s) i := by
  rw [tripleColor_histogram]
  fin_cases i <;> simp; omega

end MatchingSmoothing

end OAI
