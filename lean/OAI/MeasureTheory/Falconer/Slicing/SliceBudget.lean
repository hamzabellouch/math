import OAI.MeasureTheory.Falconer.Slicing.SlicePruningRatios

namespace OAI

/-! # The four deletion costs fit inside the original incidence budget -/

namespace Falconer
open scoped ENNReal

theorem slice_four_cost_budget_real {K B A : ℝ} (hK : 0 < K)
    (hlarge : 4*(1+2*B+A) ≤ K) :
    1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2 < 1/K := by
  have he : 1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2 =
      (K/4+(1+2*B+A))/K^2 := by field_simp; ring
  rw [he]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hK) hK).mpr
  have hh := mul_le_mul_of_nonneg_right hlarge hK.le
  nlinarith

theorem slice_four_cost_budget {K B A : ℝ} (hK : 0 < K) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hlarge : 4*(1+2*B+A) ≤ K)
    {base point direction mass active : ℝ≥0∞}
    (hb : base ≤ ENNReal.ofReal (1/(4*K))) (hp : point ≤ ENNReal.ofReal (1/K^2))
    (hd : direction ≤ ENNReal.ofReal (B/K^2)) (hm : mass ≤ ENNReal.ofReal (B/K^2))
    (ha : active ≤ ENNReal.ofReal (A/K^2)) :
    base+point+direction+mass+active < ENNReal.ofReal (1/K) := by
  calc
    _ ≤ ENNReal.ofReal (1/(4*K))+ENNReal.ofReal (1/K^2)+ENNReal.ofReal (B/K^2)+
        ENNReal.ofReal (B/K^2)+ENNReal.ofReal (A/K^2) :=
      add_le_add (add_le_add (add_le_add (add_le_add hb hp) hd) hm) ha
    _ = ENNReal.ofReal (1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (slice_four_cost_budget_real hK hlarge)

end Falconer

end OAI
