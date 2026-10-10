import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingSignedCollision
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingLogTime

namespace OAI

/-!
# Freeness of the shearing horosphere

A lattice with no nonzero vector on a coordinate hyperplane has no
nonidentity stabilizer fixing a coordinate column. Root-horospherical
matrices fix such a column. Full diagonal invariance gives the required
lattice property almost everywhere, removing any small-size restriction
from the compact shearing contradiction.
-/

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma vecMul_fixed_column {n : ℕ} (h : G n) (i : Fin n)
    (hcol : ∀ r, h.val r i = (1 : Matrix (Fin n) (Fin n) ℝ) r i)
    (v : Fin n → ℝ) : (v ᵥ* h.val) i = v i := by
  calc
    (v ᵥ* h.val) i = (v ᵥ* (1 : Matrix (Fin n) (Fin n) ℝ)) i := by
      change (∑ k, v k * h.val k i) = ∑ k, v k * (1 : Matrix (Fin n) (Fin n) ℝ) k i
      apply Finset.sum_congr rfl
      intro k _
      rw [hcol k]
    _ = v i := congrFun (Matrix.vecMul_one v) i

theorem stabilizer_eq_one_of_fixed_column {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ i, v i ≠ 0)
    (h : G n) (i : Fin n)
    (hcol : ∀ r, h.val r i = (1 : Matrix (Fin n) (Fin n) ℝ) r i)
    (hfix : rightAction x h = x) : h = 1 := by
  have hvec (v : Fin n → ℝ) (hv : v ∈ pointLattice x) : v ᵥ* h.val = v := by
    let w := v ᵥ* h.val - v
    have hw : w ∈ pointLattice x := by
      apply Submodule.sub_mem _ _ hv
      have hmem := vecMul_mem_pointLattice_rightAction x h v hv
      simpa only [hfix] using hmem
    have hwi : w i = 0 := by
      change (v ᵥ* h.val) i - v i = 0
      rw [vecMul_fixed_column h i hcol, sub_self]
    have hwzero : w = 0 := by
      by_contra hn
      exact hx w hw hn i hwi
    exact sub_eq_zero.mp hwzero
  induction x using Quotient.inductionOn with
  | h g =>
    have hmul : g * h = g := by
      apply Subtype.ext
      ext r s
      have hmem : g.val r ∈ pointLattice (Quotient.mk'' g) := by
        rw [pointLattice_mk]
        exact Submodule.subset_span (mem_range_self r)
      exact congrFun (hvec (g.val r) hmem) s
    exact mul_left_cancel (hmul.trans (mul_one g).symm)

theorem rootHorosphere_stabilizer_eq_one {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : X n) (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0)
    (h : G n) (hshape : RootHorosphereShape i j h) (hfix : rightAction x h = x) : h = 1 := by
  apply stabilizer_eq_one_of_fixed_column x hx h i _ hfix
  intro r
  by_cases hr : r = i
  · exact hshape r i (Or.inr hr)
  · exact hshape r i (Or.inl ⟨hr, hij⟩)

theorem ae_rootHorosphere_stabilizer_trivial
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ h : G (d + 1), RootHorosphereShape i j h → rightAction x h = x → h = 1 := by
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx
  exact fun h hshape hfix => rootHorosphere_stabilizer_eq_one hij x hx h hshape hfix

end DukePrimeDegree

end

end OAI
