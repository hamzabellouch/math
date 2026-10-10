import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseDeletion
import OAI.Combinatorics.KMedian.Reduction.CloseFromServing

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance badCenterBoundPseudoMetric : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace Serving
variable {U F O : Finset (Fin I.n)}

theorem bad_count (D : Serving (I:=I) U) (hUF : U ⊆ F)
    (α δ η : ℝ) (c : ℕ) (hc : 0 < c) (hδ : 0 < δ) (hη : 0 < η)
    (hC : 0 < cost I O) (hcost : cost I U ≤ α*cost I O)
    (hsp : Sparse (I:=I) F O (δ*η/(2*c)))
    (hstuck : ∀ t : ↥U, η*cost I O/c ≤ cost I (U.erase t.val)-cost I U) :
    ((D.bad O δ).card:ℝ) ≤ 6*α*c/(δ*η) := by
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hcharge := D.bad_count_charge hUF hsp hδ.le (η*cost I O/c) hstuck
  change ((D.bad O δ).card:ℝ)*(δ*(η*cost I O/c)-(δ*η/(2*c))*cost I O) ≤ 3*cost I U at hcharge
  have heq : δ*(η*cost I O/c)-(δ*η/(2*c))*cost I O=
      (δ*η/(2*c))*cost I O := by field_simp; ring
  rw [heq] at hcharge
  have hh := hcharge.trans (mul_le_mul_of_nonneg_left hcost (by norm_num : (0:ℝ) ≤ 3))
  have hh' : ((D.bad O δ).card:ℝ)*(δ*η/(2*c)) ≤ 3*α := by
    apply (mul_le_mul_iff_left₀ hC).mp
    nlinarith only [hh]
  have hdiv : ((D.bad O δ).card:ℝ)*(δ*η) ≤ 6*α*c := by
    have hh'' := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hcR)).mp
      (show (((D.bad O δ).card:ℝ)*(δ*η))/(2*c) ≤ 3*α by simpa only [mul_div_assoc] using hh')
    nlinarith only [hh'']
  exact (le_div_iff₀ (mul_pos hδ hη)).mpr hdiv

end Serving
end MetricKMedian.Reduction
end
end

end OAI
