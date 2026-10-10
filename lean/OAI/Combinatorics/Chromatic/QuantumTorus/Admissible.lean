import Mathlib
import OAI.Combinatorics.Chromatic.Model

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

@[simp] theorem edge_comm (a b : Fin n) : G.Edge a b ↔ G.Edge b a := by
  simp only [Edge, or_comm]

@[simp] theorem edge_irrefl (a : Fin n) : ¬ G.Edge a a := by
  simp [Edge]

def Admissible (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → σ i < σ j → G.Edge (σ i) (σ j)

instance (σ : Equiv.Perm (Fin n)) : Decidable (G.Admissible σ) :=
  inferInstanceAs (Decidable (∀ i j : Fin n,
    i.val + 1 = j.val → σ i < σ j → G.Edge (σ i) (σ j)))

def reversePerm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans σ

@[simp] theorem reversePerm_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reversePerm σ i = σ i.rev := rfl

@[simp] theorem reversePerm_reverse (σ : Equiv.Perm (Fin n)) :
    reversePerm (reversePerm σ) = σ := by
  ext i
  simp

lemma rev_adjacent {i j : Fin n} (h : i.val + 1 = j.val) :
    j.rev.val + 1 = i.rev.val := by
  simp only [Fin.rev]
  omega

theorem nondescent_iff_reverse_admissible (σ : Equiv.Perm (Fin n)) :
    G.Nondescent σ ↔ G.Admissible (reversePerm σ) := by
  constructor
  · intro h i j hij hlt
    exact (G.edge_comm _ _).mp (h j.rev i.rev (rev_adjacent hij) hlt)
  · intro h i j hij hlt
    have he := h j.rev i.rev (rev_adjacent hij)
    simpa using he (by simpa using hlt)

def reversalEquiv : {σ : Equiv.Perm (Fin n) // G.Nondescent σ} ≃
    {w : Equiv.Perm (Fin n) // G.Admissible w} where
  toFun σ := ⟨reversePerm σ.val, (G.nondescent_iff_reverse_admissible _).mp σ.property⟩
  invFun w := ⟨reversePerm w.val,
    (G.nondescent_iff_reverse_admissible _).mpr (by simpa using w.property)⟩
  left_inv σ := Subtype.ext (reversePerm_reverse _)
  right_inv w := Subtype.ext (reversePerm_reverse _)

def edges : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ab => ab.1 < ab.2 ∧ G.Edge ab.1 ab.2)

def edgeCount : ℕ := G.edges.card

def invertedEdges (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  G.edges.filter (fun ab => σ.symm ab.2 < σ.symm ab.1)

@[simp] lemma mem_edges (ab : Fin n × Fin n) :
    ab ∈ G.edges ↔ ab.1 < ab.2 ∧ G.Edge ab.1 ab.2 := by simp [edges]

@[simp] lemma mem_invertedEdges (σ : Equiv.Perm (Fin n)) (ab : Fin n × Fin n) :
    ab ∈ G.invertedEdges σ ↔
      ab.1 < ab.2 ∧ G.Edge ab.1 ab.2 ∧ σ.symm ab.2 < σ.symm ab.1 := by
  simp [invertedEdges, and_assoc]

theorem graphInversions_eq_card_invertedEdges (σ : Equiv.Perm (Fin n)) :
    G.graphInversions σ = (G.invertedEdges σ).card := by
  unfold graphInversions
  apply Finset.card_bij (fun ij _ => (σ ij.2, σ ij.1))
  · rintro ⟨i,j⟩ hij
    obtain ⟨hij,hlt,he⟩ := (Finset.mem_filter.mp hij).2
    simp only [mem_invertedEdges, Equiv.symm_apply_apply]
    exact ⟨hlt, (G.edge_comm _ _).mp he, hij⟩
  · rintro ⟨i,j⟩ _ ⟨k,l⟩ _ heq
    have hj := σ.injective (congrArg Prod.fst heq)
    have hi := σ.injective (congrArg Prod.snd heq)
    exact Prod.ext hi hj
  · rintro ⟨a,b⟩ hab
    obtain ⟨hab,he,hpos⟩ := (G.mem_invertedEdges σ _).mp hab
    refine ⟨(σ.symm b, σ.symm a), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply]
      exact ⟨hpos, hab, (G.edge_comm _ _).mp he⟩
    · simp

@[simp] theorem inverse_reverse_apply (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    (reversePerm σ).symm a = (σ.symm a).rev := rfl

lemma invertedEdges_reverse (σ : Equiv.Perm (Fin n)) :
    G.invertedEdges (reversePerm σ) =
      G.edges.filter (fun ab => ¬ σ.symm ab.2 < σ.symm ab.1) := by
  ext ab
  simp only [mem_invertedEdges, Finset.mem_filter, mem_edges,
    inverse_reverse_apply, Fin.rev_lt_rev, not_lt]
  constructor
  · rintro ⟨hab,he,hpos⟩
    exact ⟨⟨hab,he⟩,hpos.le⟩
  · rintro ⟨⟨hab,he⟩,hpos⟩
    refine ⟨hab,he,lt_of_le_of_ne hpos ?_⟩
    exact fun hh => hab.ne (σ.symm.injective hh)

theorem graphInversions_add_reverse (σ : Equiv.Perm (Fin n)) :
    G.graphInversions σ + G.graphInversions (reversePerm σ) = G.edgeCount := by
  rw [G.graphInversions_eq_card_invertedEdges,
    G.graphInversions_eq_card_invertedEdges, invertedEdges_reverse]
  exact Finset.card_filter_add_card_filter_not (s := G.edges) (fun ab => σ.symm ab.2 < σ.symm ab.1)

theorem graphInversions_le_edges (σ : Equiv.Perm (Fin n)) :
    G.graphInversions σ ≤ G.edgeCount := by
  have h := G.graphInversions_add_reverse σ
  omega

theorem graphInversions_reverse (σ : Equiv.Perm (Fin n)) :
    G.graphInversions (reversePerm σ) = G.edgeCount - G.graphInversions σ := by
  have h := G.graphInversions_add_reverse σ
  omega

def coloringInversions {r : ℕ} (f : Fin n → Fin r) : ℕ :=
  (G.edges.filter (fun ab => f ab.2 < f ab.1)).card

noncomputable def inversionChromatic (r : ℕ) : MvPolynomial (Fin r) (Polynomial ℕ) :=
  ∑ f ∈ Finset.univ.filter (G.Proper (r := r)),
    MvPolynomial.C (Polynomial.X ^ G.coloringInversions f) *
      ∏ i : Fin n, MvPolynomial.X (f i)

lemma coloringAscents_eq_card {r : ℕ} (f : Fin n → Fin r) :
    G.coloringAscents f = (G.edges.filter (fun ab => f ab.1 < f ab.2)).card := by
  unfold coloringAscents
  congr 1
  ext ab
  simp [edges, and_assoc]

theorem coloringInversions_add_ascents {r : ℕ} (f : Fin n → Fin r)
    (hf : G.Proper f) :
    G.coloringInversions f + G.coloringAscents f = G.edgeCount := by
  rw [coloringInversions, coloringAscents_eq_card]
  have hfilter : G.edges.filter (fun ab => f ab.1 < f ab.2) =
      G.edges.filter (fun ab => ¬ f ab.2 < f ab.1) := by
    apply Finset.filter_congr
    intro ab hab
    have hne := hf ab.1 ab.2 ((G.mem_edges ab).mp hab).2
    exact ⟨fun h => not_lt.mpr h.le, fun h => lt_of_le_of_ne (not_lt.mp h) hne⟩
  rw [hfilter]
  exact Finset.card_filter_add_card_filter_not (s := G.edges) _

end ElementaryPositivity.NaturalUnitIntervalGraph

namespace ElementaryPositivity.CoefficientReflection

noncomputable def reflectPolynomial (M : ℕ) : Polynomial ℕ →+ Polynomial ℕ where
  toFun := Polynomial.reflect M
  map_zero' := Polynomial.reflect_zero
  map_add' p q := Polynomial.reflect_add p q M

noncomputable def reflect {α : Type*} (M : ℕ) :
    MvPolynomial α (Polynomial ℕ) →+ MvPolynomial α (Polynomial ℕ) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom (reflectPolynomial M)).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

@[simp] theorem coeff_reflect {α : Type*} (M : ℕ)
    (P : MvPolynomial α (Polynomial ℕ)) (m : α →₀ ℕ) :
    (reflect M P).coeff m =
      Polynomial.reflect M (P.coeff m) := rfl

theorem reflect_C_X_pow_mul_map {α : Type*} (M k : ℕ) (hk : k ≤ M)
    (P : MvPolynomial α ℕ) :
    reflect M (MvPolynomial.C (Polynomial.X ^ k) *
      MvPolynomial.map Polynomial.C P) =
    MvPolynomial.C (Polynomial.X ^ (M-k)) * MvPolynomial.map Polynomial.C P := by
  ext m
  simp only [coeff_reflect, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rw [mul_comm, Polynomial.reflect_C_mul, Polynomial.reflect_monomial,
    Polynomial.revAt_le hk, mul_comm]

lemma map_esymmPart {α : Type*} [Fintype α] {n : ℕ} (lam : Nat.Partition n) :
    MvPolynomial.map (Polynomial.C : ℕ →+* Polynomial ℕ)
      (MvPolynomial.esymmPart α ℕ lam) = MvPolynomial.esymmPart α (Polynomial ℕ) lam := by
  simp only [MvPolynomial.esymmPart, map_multiset_prod, Multiset.map_map,
    Function.comp_def, MvPolynomial.map_esymm]

theorem reflect_C_X_pow_mul_esymmPart {α : Type*} [Fintype α]
    {n : ℕ} (lam : Nat.Partition n) (M k : ℕ) (hk : k ≤ M) :
    reflect M (MvPolynomial.C (Polynomial.X ^ k) *
      MvPolynomial.esymmPart α (Polynomial ℕ) lam) =
    MvPolynomial.C (Polynomial.X ^ (M-k)) *
      MvPolynomial.esymmPart α (Polynomial ℕ) lam := by
  rw [← map_esymmPart lam]
  exact reflect_C_X_pow_mul_map M k hk _

end ElementaryPositivity.CoefficientReflection

namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

theorem reflect_inversionChromatic (r : ℕ) :
    CoefficientReflection.reflect G.edgeCount (G.inversionChromatic r) = G.chromatic r := by
  unfold inversionChromatic chromatic
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  have hproper : G.Proper f := (Finset.mem_filter.mp hf).2
  have hc := G.coloringInversions_add_ascents f hproper
  have hk : G.coloringInversions f ≤ G.edgeCount := by omega
  have he : G.edgeCount - G.coloringInversions f = G.coloringAscents f := by omega
  have hm : (∏ i : Fin n, MvPolynomial.X (R := Polynomial ℕ) (f i)) =
      MvPolynomial.map Polynomial.C (∏ i : Fin n, MvPolynomial.X (R := ℕ) (f i)) := by
    simp
  rw [hm, CoefficientReflection.reflect_C_X_pow_mul_map _ _ hk, he]

end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
