import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogDistance
import OAI.NumberTheory.PrimePackets.IdealNorms

namespace OAI

/-! # Time-independent covers of compact neutral displacements

Compact sets of displacements commuting with the diagonal flow admit a
fixed finite orbit cover, valid for every time and every base point.
Thus their geometric covering cost does not grow with orbit length.
-/

noncomputable section
open Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem quotientLogDistance_commuting_displacements {n : ℕ}
    (x : X n) (g h a : G n) (hg : Commute g a) (hh : Commute h a) :
    quotientLogDistance (rightAction (rightAction x g) a)
      (rightAction (rightAction x h) a) ≤ matrixLogLength (g⁻¹*h) := by
  apply quotientLogDistance_le_length _ _ (g⁻¹*h)
  simp only [rightAction_mul]
  congr 1
  calc
    (g*a)*(g⁻¹*h) = (a*g)*(g⁻¹*h) := by rw [hg.eq]
    _ = a*h := by group
    _ = h*a := hh.eq.symm

theorem compact_neutral_orbit_cover {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (K : Set (G n)) (hK : IsCompact K)
    (hcomm : ∀ g ∈ K, ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset K, ∀ g ∈ K, ∃ h ∈ s, ∀ (x : X n) (t : ℝ),
      quotientLogDistance
        (rightAction (rightAction x g) (diagonalOneParameter ell hell t))
        (rightAction (rightAction x h.val) (diagonalOneParameter ell hell t)) < ε := by
  let U (h : K) : Set (G n) := {g | matrixLogLength (g⁻¹*h.val) < ε}
  have hU (h : K) : IsOpen (U h) :=
    isOpen_lt ((continuous_matrixLogLength n).comp (continuous_inv.mul continuous_const))
      continuous_const
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (fun g hg =>
    mem_iUnion.mpr ⟨⟨g,hg⟩,by simpa only [U,mem_ofPred_eq,inv_mul_cancel,
      matrixLogLength_one] using hε⟩)
  refine ⟨s,?_⟩
  intro g hg
  obtain ⟨h,hh,hgh⟩ := mem_iUnion₂.mp (hs hg)
  refine ⟨h,hh,fun x t => ?_⟩
  exact (quotientLogDistance_commuting_displacements x g h.val
    (diagonalOneParameter ell hell t) (hcomm g hg t) (hcomm h.val h.prop t)).trans_lt hgh

end DukePrimeDegree

end

end OAI
