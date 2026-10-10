import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanMetadata

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

structure IntegerReferenceData
    (x y : SourceAssignment C.sources (SelectedTemplate k L l)) (P Q : ℤ) : Prop where
  left_mass : (assignmentPrior C.sources (SelectedTemplate k L l)).mass x ≠ 0
  right_mass : (assignmentPrior C.sources (SelectedTemplate k L l)).mass y ≠ 0
  plus_pos : 0 < P
  minus_pos : 0 < Q
  plus_cell : |Real.log (P:ℝ)-(C.giantCenter:ℝ)| ≤ 1
  minus_cell : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)| ≤ 1

theorem prime_draw_cells (r : PrimeDraw C.giant) (hr : 0 < primeWeight C.giant r) :
    0 < primeP C.giant r ∧ 0 < primeQ C.giant r ∧
    |Real.log ((primeP C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 ∧
    |Real.log ((primeQ C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 := by
  have hp := primeDraw_positive C.giant r
  have hcell := prime_reference_cells C r hr
  refine ⟨hp.1,hp.2,?_,?_⟩
  · simpa only [primeP,Int.cast_natCast] using hcell.1.le
  · simpa only [primeQ,Int.cast_natCast] using hcell.2.le

theorem mixed_draw_cells (r : MixedDraw C.giantCenter C.giant)
    (hr : 0 < mixedWeight C.giantCenter C.giant r) :
    0 < mixedP C.giantCenter C.giant r ∧ 0 < mixedQ C.giantCenter C.giant r ∧
    |Real.log ((mixedP C.giantCenter C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 ∧
    |Real.log ((mixedQ C.giantCenter C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 := by
  have hp := mixedDraw_positive C.giantCenter C.giant r
  have hcell := mixed_reference_cells C r hr
  refine ⟨hp.1,hp.2,?_,?_⟩
  · simpa only [mixedP,Int.cast_natCast] using hcell.1.le
  · simpa only [mixedQ,Int.cast_natCast] using hcell.2.le

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference

end

end OAI
