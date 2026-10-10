import Mathlib

namespace OAI

noncomputable section

universe uG uV uE uX uH uI uβ uα

open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

abbrev Position (d : ℕ) := Fin d → Bool

namespace Block

variable {I : Type uI} {β : Type uβ} {α : Type uα}

def perm (p : I → Equiv.Perm β) : Equiv.Perm (I × β) where
  toFun x := (x.1, p x.1 x.2)
  invFun x := (x.1, (p x.1)⁻¹ x.2)
  left_inv x := by simp
  right_inv x := by simp

def hom : (I → Equiv.Perm β) →* Equiv.Perm (I × β) where
  toFun := perm
  map_one' := by ext ⟨i,b⟩ <;> rfl
  map_mul' p q := by ext ⟨i,b⟩ <;> rfl

def embedding (e : α ≃ I × β) : (I → Equiv.Perm β) →* Equiv.Perm α :=
  (e.symm.permCongrHom).toMonoidHom.comp hom

end Block

namespace Fourier

variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def integrated (ρ : Representation ℂ G V) (f : G → ℂ) : Module.End ℂ V :=
  ∑ g, f g • ρ g

end Fourier

namespace Young

abbrev Cells (D : YoungDiagram) := {p : ℕ × ℕ // p ∈ D.cells}

def rowCellsEquiv (D : YoungDiagram) : Cells D ≃ (i : Fin (D.colLen 0)) × Fin (D.rowLen i) where
  toFun x := ⟨⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp (D.up_left_mem le_rfl (Nat.zero_le _) x.property)⟩,
    ⟨x.val.2, YoungDiagram.mem_iff_lt_rowLen.mp x.property⟩⟩
  invFun x := ⟨(x.1, x.2), YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  left_inv x := rfl
  right_inv x := by cases x; rfl

def ofPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

def longest (D : YoungDiagram) : ℕ := max (D.rowLen 0) (D.colLen 0)

end Young

namespace Specht

variable {G : Type uG} [Group G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def cyclic (ρ : Representation ℂ G E) (e : E) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g e)
  apply_mem_toSubmodule g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      exact Submodule.subset_span ⟨g * h, by simp⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).add_mem ihx ihy
    | smul a x hx ih =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).smul_mem a ih

namespace PermutationSpace

variable {X : Type uX} [Fintype X] [MulAction G X]

def rep : Representation ℂ G (EuclideanSpace ℂ X) where
  toFun g := {
    toFun v := WithLp.toLp 2 (fun x => v (g⁻¹ • x))
    map_add' := by intro v w; rfl
    map_smul' := by intro a v; rfl }
  map_one' := by ext v x; simp
  map_mul' := by
    intro g h
    ext v x
    change v ((g * h)⁻¹ • x) = v (h⁻¹ • g⁻¹ • x)
    simp [mul_smul]

variable {H : Type uH} [Group H] [Fintype H]

def alternator (ι : H →* G) (χ : H →* ℂ) : Module.End ℂ (EuclideanSpace ℂ X) :=
  ∑ h, χ h • rep (ι h)

end PermutationSpace

variable {α : Type uα} [Fintype α]

def Tabloid (r : α → ℕ) := {f : α → ℕ // ∃ g : Equiv.Perm α, f = r ∘ g}

instance tabloidFinite (r : α → ℕ) : Finite (Tabloid r) := by
  apply Finite.of_surjective (fun g : Equiv.Perm α => (⟨r ∘ g, g, rfl⟩ : Tabloid r))
  rintro ⟨f, g, rfl⟩
  exact ⟨g, rfl⟩

instance tabloidFintype (r : α → ℕ) : Fintype (Tabloid r) := Fintype.ofFinite _

instance tabloidAction (r : α → ℕ) : MulAction (Equiv.Perm α) (Tabloid r) where
  smul g f := ⟨f.val ∘ ⇑(g⁻¹ : Equiv.Perm α), by
    obtain ⟨h, hh⟩ := f.property
    refine ⟨h * g⁻¹, ?_⟩
    funext x
    simp only [Function.comp_apply, hh, Equiv.Perm.mul_apply]⟩
  one_smul f := by apply Subtype.ext; funext x; rfl
  mul_smul g h f := by
    apply Subtype.ext
    funext x
    change f.val ((g * h)⁻¹ x) = f.val (h⁻¹ (g⁻¹ x))
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

def baseTabloid (r : α → ℕ) : Tabloid r := ⟨r, 1, by funext x; rfl⟩

def fiberGroup (c : α → ℕ) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, c (g x) = c x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have hh := hg (g⁻¹ x)
    change c (g (g.symm x)) = c (g.symm x) at hh
    rw [g.apply_symm_apply] at hh
    exact hh.symm

def complexSign : Equiv.Perm α →* ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤˣ) : ℤ)
  map_one' := by simp
  map_mul' := by intro g h; simp

variable (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D)

def tableauRow (x : α) : ℕ := (t x).val.1

def tableauCol (x : α) : ℕ := (t x).val.2

def tabloidRep : Representation ℂ (Equiv.Perm α) (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.rep

def columnAlternator : Module.End ℂ (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)

def polytabloid : EuclideanSpace ℂ (Tabloid (tableauRow D t)) :=
  columnAlternator D t (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ))

def module : Subrepresentation (tabloidRep D t) := cyclic (tabloidRep D t) (polytabloid D t)

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

def degree (p : Shape α) : ℕ := Module.finrank ℂ (Space p)

open Thorp.Young

abbrev NShape (n : ℕ) := Shape (Fin n)

def defect {n : ℕ} (p : NShape n) : ℕ := n - longest (ofPartition p)

end Specht

namespace Current

def reciprocalFirst (n : ℕ) : ℝ :=
  ∑ p : Specht.NShape n, (Specht.degree p : ℝ)⁻¹

def exceptionalFirst (n : ℕ) : ℝ :=
  ∑ p : Specht.NShape n, if 0 < Specht.defect p then (Specht.degree p : ℝ)⁻¹ else 0

def C1 : ℝ := sSup (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val))

theorem first_reciprocal_main :
    (BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0)) ∧
    (∀ (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (_ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (_ : ∀ g, 0 ≤ ν g) (_ : ∑ g, ν g = 1)
    (_ : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))),
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ)) := by
  sorry

end Current

end Thorp

end

end OAI
