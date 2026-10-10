import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceNormalizedSpectrum
import Mathlib.Data.List.FinRange

namespace OAI

/-! Literal coefficient rounding and zero deletion preserve the original
square-lattice geometry and the simple unordered edge enumeration. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum
open MediatorIteration MediatorListProgram SourceBondLists

private theorem rounded_injective (d : SquareLatticeHeisenberg) (M : ℕ) :
    Function.Injective (fun e : Fin d.edges => ((d.left e).val, (d.right e).val,
      SourceCoefficientRounding.coefficient M (d.coefficient e))) := by
  intro e f h
  by_contra hne
  apply (d.edge_simple e f hne).1
  exact ⟨Fin.ext (congrArg Prod.fst h),
    Fin.ext (congrArg (fun b : Bond => b.2.1) h)⟩

theorem retained_nodup (d : SquareLatticeHeisenberg) (M : ℕ) : (retained d M).Nodup :=
  (List.nodup_ofFn_ofInjective (rounded_injective d M)).filter _

/-- Every retained bond has the same two endpoints as a definite original
source bond; only its coefficient has been rounded. -/
theorem family_original_edge (d : SquareLatticeHeisenberg) (M : ℕ)
    (e : Fin (retained d M).length) :
    ∃ i : Fin d.edges, (family d M).left e = d.left i ∧
      (family d M).right e = d.right i ∧
      (retained d M).get e = ((d.left i).val, (d.right i).val,
        SourceCoefficientRounding.coefficient M (d.coefficient i)) := by
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp (List.get_mem (retained d M) e)).1
  refine ⟨i, ?_, ?_, hi.symm⟩
  · exact Fin.ext (congrArg Prod.fst hi.symm)
  · exact Fin.ext (congrArg (fun b : Bond => b.2.1) hi.symm)

theorem family_adjacent (d : SquareLatticeHeisenberg) (M : ℕ)
    (e : Fin (retained d M).length) :
    Int.natAbs ((d.coordinate ((family d M).left e)).1 -
        (d.coordinate ((family d M).right e)).1) +
      Int.natAbs ((d.coordinate ((family d M).left e)).2 -
        (d.coordinate ((family d M).right e)).2) = 1 := by
  obtain ⟨i, hi, hj, _⟩ := family_original_edge d M e
  rw [hi, hj]
  exact d.adjacent i

theorem family_edge_simple (d : SquareLatticeHeisenberg) (M : ℕ)
    (e f : Fin (retained d M).length) (hef : e ≠ f) :
    ¬((family d M).left e = (family d M).left f ∧
      (family d M).right e = (family d M).right f) ∧
    ¬((family d M).left e = (family d M).right f ∧
      (family d M).right e = (family d M).left f) := by
  obtain ⟨i, hei, hei', hgeti⟩ := family_original_edge d M e
  obtain ⟨j, hfj, hfj', hgetj⟩ := family_original_edge d M f
  have hij : i ≠ j := by
    intro h
    subst j
    exact hef ((retained_nodup d M).injective_get (hgeti.trans hgetj.symm))
  have hs := d.edge_simple i j hij
  constructor
  · rintro ⟨hl, hr⟩
    exact hs.1 ⟨hei.symm.trans (hl.trans hfj), hei'.symm.trans (hr.trans hfj')⟩
  · rintro ⟨hl, hr⟩
    exact hs.2 ⟨hei.symm.trans (hl.trans hfj'), hei'.symm.trans (hr.trans hfj)⟩

/-- The normalized graph in the same geometric source type. Its thresholds
are inherited only to satisfy the record; all coefficient and matrix
normalization theorems continue to use the literal `family` definition. -/
def lattice (d : SquareLatticeHeisenberg) (M : ℕ) : SquareLatticeHeisenberg where
  vertices := d.vertices
  vertices_pos := d.vertices_pos
  coordinate := d.coordinate
  coordinate_injective := d.coordinate_injective
  edges := (retained d M).length
  left := (family d M).left
  right := (family d M).right
  adjacent := family_adjacent d M
  edge_simple := family_edge_simple d M
  coefficient := (family d M).weight
  lower := d.lower
  upper := d.upper
  gap_pos := d.gap_pos

@[simp] theorem lattice_bonds (d : SquareLatticeHeisenberg) (M : ℕ) :
    (lattice d M).bonds = family d M := rfl

@[simp] theorem lattice_coordinate (d : SquareLatticeHeisenberg) (M : ℕ) :
    (lattice d M).coordinate = d.coordinate := rfl

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
