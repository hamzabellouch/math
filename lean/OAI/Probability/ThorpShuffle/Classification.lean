import OAI.Probability.ThorpShuffle.Irreducibility

namespace OAI

universe uG uI uV uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def rowCellsEquiv (D : YoungDiagram) : Cells D ≃ (i : Fin (D.colLen 0)) × Fin (D.rowLen i) where
  toFun x := ⟨⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp (D.up_left_mem le_rfl (Nat.zero_le _) x.property)⟩,
    ⟨x.val.2, YoungDiagram.mem_iff_lt_rowLen.mp x.property⟩⟩
  invFun x := ⟨(x.1, x.2), YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  left_inv x := rfl
  right_inv x := by cases x; rfl

lemma card_cells_eq_sum (D : YoungDiagram) : Fintype.card (Cells D) = D.rowLens.sum := by
  rw [Fintype.card_congr (rowCellsEquiv D), Fintype.card_sigma]
  simp only [Fintype.card_fin, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]

def ofPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma rowLens_ofPartition {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  exact p.parts_pos ((Multiset.mem_sort _).mp hx)

lemma card_ofPartition {n : ℕ} (p : Nat.Partition n) : Fintype.card (Cells (ofPartition p)) = n := by
  rw [card_cells_eq_sum, rowLens_ofPartition]
  simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum

lemma ofPartition_injective {n : ℕ} : Function.Injective (ofPartition (n := n)) := by
  intro p q hpq
  apply Nat.Partition.ext
  have hh := congrArg YoungDiagram.rowLens hpq
  rw [rowLens_ofPartition, rowLens_ofPartition] at hh
  simpa only [Multiset.sort_eq] using congrArg (fun x : List ℕ => (x : Multiset ℕ)) hh

def toPartition (D : YoungDiagram) (n : ℕ) (hn : Fintype.card (Cells D) = n) : Nat.Partition n where
  parts := D.rowLens
  parts_pos := fun hx => D.pos_of_mem_rowLens _ hx
  parts_sum := by simpa only [Multiset.sum_coe, ← card_cells_eq_sum] using hn

lemma of_toPartition (D : YoungDiagram) (n : ℕ) (hn : Fintype.card (Cells D) = n) :
    ofPartition (toPartition D n hn) = D := by
  have hs : (D.rowLens : Multiset ℕ).sort (· ≥ ·) = D.rowLens := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ D.rowLens_sorted.pairwise
  unfold ofPartition toPartition
  simp only [hs]
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self

end Thorp.Young

namespace Thorp.Fourier
open scoped Classical

variable {G : Type uG} [Group G] [Fintype G]

def charPair (f h : G → ℂ) : ℂ := (Nat.card G : ℂ)⁻¹ * ∑ g, f g * h g⁻¹

lemma charPair_sum {I : Type uI} (s : Finset I) (a : I → ℂ) (f : I → G → ℂ) (h : G → ℂ) :
    charPair (∑ i ∈ s, a i • f i) h = ∑ i ∈ s, a i * charPair (f i) h := by
  simp only [charPair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc (a i)]
  rw [← Finset.mul_sum]
  ring

lemma charPair_zero (h : G → ℂ) : charPair (0 : G → ℂ) h = 0 := by simp [charPair]

lemma irreducible_char_independent {I : Type uI} {V : I → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
    (hne : ∀ i j, Nonempty (Representation.Equiv (ρ i) (ρ j)) → i = j) :
    LinearIndependent ℂ (fun i => (ρ i).character) := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have ho (i j : I) : charPair (ρ i).character (ρ j).character = if i = j then 1 else 0 := by
    rw [charPair, Representation.char_orthonormal]
    congr 1
    apply propext
    constructor
    · exact fun h => (hne j i h).symm
    · intro h; subst j; exact ⟨Representation.Equiv.refl _⟩
  rw [linearIndependent_iff']
  intro s a ha i hi
  have hh := congrArg (fun f => charPair f (ρ i).character) ha
  rw [charPair_sum, charPair_zero] at hh
  simp only [ho] at hh
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_left hi] using hh

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

abbrev Shape (α : Type uα) [Fintype α] := Nat.Partition (Fintype.card α)

def canonicalTableau (p : Shape α) : α ≃ Thorp.Young.Cells (Thorp.Young.ofPartition p) := by
  have card_cells_eq_sum (D : YoungDiagram) : Fintype.card (Thorp.Young.Cells D) = D.rowLens.sum := by
    rw [Fintype.card_congr (Thorp.Young.rowCellsEquiv D), Fintype.card_sigma]
    simp only [Fintype.card_fin, YoungDiagram.rowLens]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]
  have rowLens_ofPartition {n : ℕ} (p : Nat.Partition n) :
      (Thorp.Young.ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
    apply YoungDiagram.rowLens_ofRowLens_eq_self
    intro x hx
    exact p.parts_pos ((Multiset.mem_sort _).mp hx)
  have card_ofPartition {n : ℕ} (p : Nat.Partition n) : Fintype.card (Thorp.Young.Cells (Thorp.Young.ofPartition p)) = n := by
    rw [card_cells_eq_sum, rowLens_ofPartition]
    simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum
  exact Fintype.equivOfCardEq (card_ofPartition p).symm

abbrev Space (p : Shape α) := (module (Thorp.Young.ofPartition p) (canonicalTableau p)).toSubmodule

def family (p : Shape α) : Representation ℂ (Equiv.Perm α) (Space p) :=
  (module (Thorp.Young.ofPartition p) (canonicalTableau p)).toRepresentation

instance family_irreducible (p : Shape α) : Representation.IsIrreducible (family p) :=
  irreducible (Thorp.Young.ofPartition p) (canonicalTableau p)

lemma family_inequiv (p q : Shape α) (he : Nonempty (Representation.Equiv (family p) (family q))) : p = q := by
  obtain ⟨e⟩ := he
  apply Thorp.Young.ofPartition_injective
  exact shape_eq_of_equiv _ _ _ _ e

lemma characters_independent : LinearIndependent ℂ (fun p : Shape α => (family p).character) :=
  Thorp.Fourier.irreducible_char_independent family family_inequiv

def classLift (f : Equiv.Perm α → ℂ) (p : Shape α) : ℂ :=
  if h : ∃ g : Equiv.Perm α, g.partition = p then f h.choose else 0

lemma classLift_apply (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) (g : Equiv.Perm α) :
    classLift f g.partition = f g := by
  unfold classLift
  have hh : ∃ a : Equiv.Perm α, a.partition = g.partition := ⟨g, rfl⟩
  rw [dite_eq_left hh]
  exact hf _ g (Equiv.Perm.partition_eq_of_isConj.mpr hh.choose_spec)

lemma character_isClass (p : Shape α) (g h : Equiv.Perm α) (hgh : IsConj g h) :
    (family p).character g = (family p).character h := by
  obtain ⟨x, hx⟩ := isConj_iff.mp hgh
  rw [← hx]
  exact (Representation.char_conj (family p) g x).symm

lemma liftedCharacters_independent :
    LinearIndependent ℂ (fun p : Shape α => classLift (family p).character) := by
  let E : (Shape α → ℂ) →ₗ[ℂ] (Equiv.Perm α → ℂ) := {
    toFun := fun f g => f g.partition
    map_add' := by intro f h; rfl
    map_smul' := by intro a f; rfl }
  apply LinearIndependent.of_comp E
  convert characters_independent (α := α) using 1
  funext p g
  exact classLift_apply _ (character_isClass p) g

def characterBasis : Module.Basis (Shape α) ℂ (Shape α → ℂ) :=
  basisOfPiSpaceOfLinearIndependent liftedCharacters_independent

lemma characterBasis_apply (p : Shape α) : characterBasis p = classLift (family p).character := by
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent liftedCharacters_independent) p

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

lemma class_expansion (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) :
    (∑ p : Shape α, (characterBasis.repr (classLift f)) p • (family p).character) = f := by
  funext g
  have he := congrFun (characterBasis.sum_repr (classLift f)) g.partition
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, characterBasis_apply,
    classLift_apply _ (character_isClass _), classLift_apply _ hf] at he
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

lemma char_orthogonal (p q : Shape α) :
    Thorp.Fourier.charPair (family p).character (family q).character = if p = q then 1 else 0 := by
  let : Invertible (Nat.card (Equiv.Perm α) : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [Thorp.Fourier.charPair, Representation.char_orthonormal]
  congr 1
  apply propext
  exact ⟨fun h => (family_inequiv q p h).symm,
    fun h => by subst q; exact ⟨Representation.Equiv.refl _⟩⟩

lemma class_coeff (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) (q : Shape α) :
    characterBasis.repr (classLift f) q = Thorp.Fourier.charPair f (family q).character := by
  have he := congrArg (fun x => Thorp.Fourier.charPair x (family q).character) (class_expansion f hf)
  rw [Thorp.Fourier.charPair_sum] at he
  simp only [char_orthogonal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at he
  exact he

def degree (p : Shape α) : ℕ := Module.finrank ℂ (Space p)

theorem regular_char (g : Equiv.Perm α) :
    ∑ p : Shape α, (degree p : ℂ) * (family p).character g =
      if g = 1 then (Nat.card (Equiv.Perm α) : ℂ) else 0 := by
  let δ : Equiv.Perm α → ℂ := fun h => if h = 1 then Nat.card (Equiv.Perm α) else 0
  have hδ : ∀ a b, IsConj a b → δ a = δ b := by
    intro a b hab
    have hh : a = 1 ↔ b = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hab
      rw [← hc]
      constructor
      · intro ha; simp [ha]
      · intro hb
        have hh := congrArg (fun z => c⁻¹ * z * c) hb
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, one_mul, mul_one] using hh
    simp only [δ, hh]
  have hc (p : Shape α) : Thorp.Fourier.charPair δ (family p).character = degree p := by
    rw [Thorp.Fourier.charPair]
    simp only [δ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, inv_one,
      Representation.char_one]
    rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne _), one_mul]
    rfl
  have he := congrFun (class_expansion δ hδ) g
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, class_coeff δ hδ, hc] using he

theorem degree_sq_sum : ∑ p : Shape α, (degree p : ℂ) ^ 2 = Nat.card (Equiv.Perm α) := by
  have hh := regular_char (α := α) 1
  simpa only [Representation.char_one, degree, pow_two, ↓reduceIte] using hh

end Thorp.Specht

end

end OAI
