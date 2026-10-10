import OAI.Analysis.PlanarPacking.ResidualBase
import OAI.Analysis.PlanarPacking.DataTail
import OAI.Analysis.PlanarPacking.TableNorms

namespace OAI

/-!
# Tail bounds for interpolation residuals

Shell estimates control the tails of the residuals beyond the finite interpolation coordinates.
-/

namespace SharpPlanar
open Numerical IntegerBasis
lemma residual_tail_eq (a : Bool) : rowTailNorm (tableResidual a) 100=
    rowTailNorm (transformedJetList (tableData (!a))) 100 := by
  unfold rowTailNorm
  apply tsum_congr
  intro n
  have hn := n.prop
  have hv (d : Bool) : tableResidual a (n.val,d) = -transformedJets (tableData (!a)) (n.val,d) := by
    rw [tableResidual_apply]
    simp only [tableD_large a hn,tableC_large a hn,Rat.cast_zero,ite_self,zero_sub]
    have hh : ¬(a=false ∧ n.val.val=1 ∧ d=true) := by omega
    rw [ite_eq_right hh,add_zero]
  rw [hv false,hv true,abs_neg,abs_neg]
  rfl
lemma residual_tail_bound (a : Bool) :
    ‖tableResidual a-IF (RF (tableResidual a))‖ ≤ (1689:ℝ)/10^12 := by
  rw [finite_discard_norm,residual_tail_eq]
  have hb:=sharp_data_tail (tableData (!a)) 100
  have hr:=rowTable_bounds.2.2.2
  have ha:=atomRowTable_hundred
  have hc:=table_coeff_mass (!a)
  have hC:=table_constant_bound (!a)
  have hp : 0≤ |(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖ := by positivity
  have h1:=mul_le_mul_of_nonneg_left hr.le hp
  have h2:=mul_le_mul_of_nonneg_left ha.le (abs_nonneg (tableData (!a)).C)
  nlinarith
end SharpPlanar

end OAI
