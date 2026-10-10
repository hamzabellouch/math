import Mathlib

namespace OAI

/-! Universal tensor squares of irreducible complex symmetric-group representations. -/

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

abbrev WordSpace (n d : ℕ) := (Fin n → Fin d) → ℂ

def wordRep (n d : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) (WordSpace n d) where
  toFun g :=
    { toFun := fun f a => f (a ∘ g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f a; rfl
  map_mul' g h := by ext f a; rfl

def cyclic {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G => ρ g v)
  apply_mem_toSubmodule g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      simpa only [map_smul] using Submodule.smul_mem _ a ih

abbrev Tableau (n : ℕ) (μ : YoungDiagram) := Fin n ≃ μ.cells

def canonicalTableau {n : ℕ} (μ : YoungDiagram) (hn : μ.card = n) : Tableau n μ :=
  (Fintype.equivFinOfCardEq (by simpa using hn)).symm

def rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) : Fin n → Fin (μ.colLen 0) :=
  fun i => ⟨(t i).val.1, YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (Nat.zero_le _) (t i).property)⟩

def columnGroup {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, (t (g i)).val.2 = (t i).val.2}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro g h hg hh i
    exact (hg (h i)).trans (hh i)
  inv_mem' := by
    intro g hg i
    have h := hg (g⁻¹ i)
    simpa using h.symm

def polytabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    WordSpace n (μ.colLen 0) := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t,
    (((Equiv.Perm.sign (g : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
      wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)

def spechtSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :=
  cyclic (wordRep n (μ.colLen 0)) (polytabloid t)

abbrev Specht {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :=
  (spechtSub t).toSubmodule

def spechtRep {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation ℂ (Equiv.Perm (Fin n)) (Specht t) :=
  (spechtSub t).toRepresentation

def kronecker {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) : ℕ :=
  Module.finrank ℂ (Representation.IntertwiningMap (spechtRep t)
    ((spechtRep a).tprod (spechtRep b)))

end Saxl

namespace UniversalTensorSquares

universe u

theorem universal_tensor_square
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  sorry

end UniversalTensorSquares

end

end OAI
