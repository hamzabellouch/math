import OAI.Analysis.LipschitzHilbert.Trees.SourceSpatialSubdivision

namespace OAI

/-! Exact finite splitting of a selected tree into spatial pieces with
the center bounds required by the ordinary tree theorem. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {ι : Type*}

def spatialTreePiece (S : Finset ι) (x y : ι → ℝ) (a b L W : ℝ) (p : ℤ×ℤ) : Finset ι :=
  S.filter (fun q => spatialPacketCell x y a b L W q=p)

theorem spatialTreePiece_centers (S : Finset ι) (x y : ι → ℝ) (a b L W : ℝ)
    (hL : 0<L) (hW : 0<W) (p : ℤ×ℤ) (q : ι)
    (hq : q∈spatialTreePiece S x y a b L W p) :
    |x q-spatialCellCenter a L p.1|≤L/2 ∧ |y q-spatialCellCenter b W p.2|≤W/2 := by
  have he := (Finset.mem_filter.mp hq).2
  rw [←he]
  exact ⟨spatialCell_center_bound a L (x q) hL,spatialCell_center_bound b W (y q) hW⟩

theorem sum_spatialTreePieces {E : Type*} [AddCommMonoid E]
    (S : Finset ι) (x y : ι → ℝ) (a b L W : ℝ) (hL : 0<L) (hW : 0<W) (K : ℕ)
    (hx : ∀ q∈S, |x q-a|≤(K:ℝ)*L) (hy : ∀ q∈S, |y q-b|≤(K:ℝ)*W)
    (f : ι → E) :
    (∑ p∈(Finset.Icc (-(K:ℤ)) K) ×ˢ (Finset.Icc (-(K:ℤ)) K),
      ∑ q∈spatialTreePiece S x y a b L W p, f q)=∑ q∈S, f q := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun q hq => spatialPacketCell_mem x y a b L W hL hW K q (hx q hq) (hy q hq)) f

theorem spatialTreePieces_area (L W : ℝ) (K : ℕ) :
    (∑ _p∈(Finset.Icc (-(K:ℤ)) K) ×ˢ (Finset.Icc (-(K:ℤ)) K), L*W)=
      (((2*K+1)^2:ℕ):ℝ)*(L*W) := by
  rw [Finset.sum_const,spatialCell_count,nsmul_eq_mul]

end LipschitzHilbert

end

end OAI
