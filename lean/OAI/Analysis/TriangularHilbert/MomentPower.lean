import OAI.Analysis.TriangularHilbert.CyclicDensity

namespace OAI

universe uκ

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

lemma real_three_halves (x : ℝ) (hx : 0 ≤ x) : x^((3:ℝ)/2) = x*Real.sqrt x := by
  by_cases he : x = 0
  · subst x; norm_num
  · rw [show (3:ℝ)/2 = 1+(1:ℝ)/2 by norm_num,Real.rpow_add (lt_of_le_of_ne hx (Ne.symm he)),Real.rpow_one,Real.sqrt_eq_rpow]

lemma ofReal_complexMoment (z : ℂ) : ENNReal.ofReal (complexMoment z) = ENNReal.ofReal ‖z‖^((3:ℝ)/2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),real_three_halves _ (norm_nonneg _)]
  rfl

lemma ofReal_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ENNReal.ofReal (finiteMoment f) = ⨆ k, ENNReal.ofReal (complexMoment (f k)) := by
  apply le_antisymm
  · obtain ⟨k,hk⟩ := finiteMoment_eq f
    rw [hk]
    exact le_iSup (fun k => ENNReal.ofReal (complexMoment (f k))) k
  · exact iSup_le (fun k => ENNReal.ofReal_le_ofReal (le_finiteMoment f k))
end
end TriangularHilbert
end

end OAI
