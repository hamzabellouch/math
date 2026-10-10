import Mathlib
import OAI.Computability.VertexCover.Reduction.FiniteMeanUnionBound
import OAI.Computability.VertexCover.Reduction.GridBudget

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem high_count_lower (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (A : Finset (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet (A : Set (Φ.Vertex d))) :
    A.card ≤ (A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))).card + 1 := by
  classical
  have hl : (A.filter (fun v => Φ.compatibilityNorm (Φ.sumVector v) ≤ t)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    exact Φ.low_norm_subsingleton (A : Set (Φ.Vertex d)) hA
      (Finset.mem_filter.mp hv) (Finset.mem_filter.mp hw)
  have he := Finset.card_filter_add_card_filter_not (s := A)
    (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))
  simp only [not_lt] at he
  omega

theorem vertex_card_ge_grid (Φ : LabelCover) {d : ℕ} (hd : 0 < d) :
    2*d+1 ≤ Fintype.card (Φ.Vertex d) := by
  classical
  have hq : 0 < Φ.WeightDimension d := by
    dsimp [WeightDimension]
    exact pow_pos (lt_of_lt_of_le Φ.qU_pos (le_max_left _ _)) _
  have he : 1 ≤ Φ.WeightDimension d * d := Nat.mul_pos hq hd
  rw [Φ.vertex_card]
  have hM : 1 ≤ Φ.M^(d.choose 2) := one_le_pow₀ Φ.M_pos
  have hp : 2*d+1 ≤ (2*d+1)^(Φ.WeightDimension d*d) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2*d+1) he
  exact hp.trans (Nat.le_mul_of_pos_left _ hM)

theorem dense_high_fraction (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m))))
    (hdense : (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) ≤ A.card) :
    Parameters.b₀ m ≤
      ((A.filter (fun v => (Parameters.t m:ℝ) < Φ.compatibilityNorm (Φ.sumVector v))).card:ℝ) /
        Fintype.card (Φ.Vertex (Parameters.d m)) := by
  classical
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN : 2*m < Fintype.card (Φ.Vertex (Parameters.d m)) :=
    (Parameters.grid_budget m hm).2.2.trans_le
      (Φ.vertex_card_ge_grid (by have h := (Parameters.dimensions m hm).1; omega))
  have hNR : (2:ℝ)*m < Fintype.card (Φ.Vertex (Parameters.d m)) := by exact_mod_cast hN
  have hNP : (0:ℝ) < Fintype.card (Φ.Vertex (Parameters.d m)) := by linarith
  have hc : (A.card:ℝ) ≤
      (A.filter (fun v => (Parameters.t m:ℝ) < Φ.compatibilityNorm (Φ.sumVector v))).card + 1 := by
    exact_mod_cast Φ.high_count_lower A hA
  unfold Parameters.b₀
  apply (le_div_iff₀ hNP).mpr
  have hd := (div_le_iff₀ hmR).mp hdense
  have hh : (1/(2*(m:ℝ))) * Fintype.card (Φ.Vertex (Parameters.d m)) =
      Fintype.card (Φ.Vertex (Parameters.d m))/(2*(m:ℝ)) := by ring
  rw [hh]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*m)).mpr
  nlinarith

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
