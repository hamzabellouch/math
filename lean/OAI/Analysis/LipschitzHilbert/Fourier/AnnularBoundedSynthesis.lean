import OAI.Analysis.LipschitzHilbert.Estimates.BoundedProjectedOutput
import OAI.Analysis.LipschitzHilbert.Packets.AnnularEnlargedFrame

namespace OAI

/-! Uniform synthesis of actual annular projections of a bounded function
once those individual projections have finite square energy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def annularBoundedComponent (N : ℕ) (F : (ℝ×ℝ) → ℂ) (i : Fin (2*N+1)) : (ℝ×ℝ) → ℂ :=
  verticalConvolution (verticalProfileKernel reassemblyDifferenceSchwartz (reassemblyScale N i) 0) F

theorem finiteFunctionSum_memLp {n : ℕ} (f : Fin n → (ℝ×ℝ) → ℂ)
    (h : ∀ i, MemLp (f i) 2 planeMeasure) :
    MemLp (fun z => ∑ i, f i z) 2 planeMeasure := by
  simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun i _ => h i)

theorem finiteFunctionSum_toLp {n : ℕ} (f : Fin n → (ℝ×ℝ) → ℂ)
    (h : ∀ i, MemLp (f i) 2 planeMeasure) :
    (finiteFunctionSum_memLp f h).toLp (fun z => ∑ i, f i z)=∑ i, (h i).toLp (f i) := by
  apply Lp.ext
  have hco := ae_all_iff.mpr (fun i => (h i).coeFn_toLp)
  filter_upwards [(finiteFunctionSum_memLp f h).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => (h i).toLp (f i)),hco] with z hz hs hi
  rw [hz,hs]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

theorem annularBounded_synthesis (N : ℕ) (F : (ℝ×ℝ) → ℂ) (hFm : Measurable F)
    (B : ℝ) (hFb : ∀ z, ‖F z‖≤B)
    (hG : ∀ i, MemLp (annularBoundedComponent N F i) 2 planeMeasure) :
    ‖(finiteFunctionSum_memLp (annularBoundedComponent N F) hG).toLp
      (fun z => ∑ i, annularBoundedComponent N F i z)‖≤
      Real.sqrt 12*Real.sqrt (∑ i, ‖(hG i).toLp (annularBoundedComponent N F i)‖^2) := by
  let g := fun i => (hG i).toLp (annularBoundedComponent N F i)
  have hid (i : Fin (2*N+1)) : verticalL2Projection reassemblyEnlarged (reassemblyScale N i) (g i)=g i :=
    verticalL2Projection_on_projected_bounded reassemblyEnlarged reassemblyDifferenceSchwartz
      reassemblyEnlarged_absorb _ (reassemblyScale_pos N i) F hFm B hFb (hG i)
  have hs := verticalFrame_synthesis Finset.univ (fun _ : Fin (2*N+1) => reassemblyEnlarged)
    (fun i => reassemblyScale N i) (fun i => reassemblyScale_pos N i)
    (fun _ => reassemblyEnlarged_real) 12 (by norm_num) (fun eta => by
      exact (Fin.sum_univ_eq_sum_range (fun n =>
        ‖reassemblyEnlarged (reassemblyScale N n*eta)‖^2) (2*N+1)).trans_le
          (enlarged_annular_square N eta)) g
  simp only [hid] at hs
  rw [finiteFunctionSum_toLp]
  exact hs

end LipschitzHilbert.PacketRepresentation

end

end OAI
