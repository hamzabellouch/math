import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightPolygon

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma heightPolygon_translate_apply (F : ℕ → ℝ) (r n T : ℝ) (hn : 0 ≤ n) (hT : 0 ≤ T)
    (H : ℕ) (c : ℝ) (t u : unitInterval)
    (hu : (T+1)*n*(u:ℝ) = T*n*(t:ℝ)+(H:ℝ)) :
    heightPolygon (fun k => F (k+H)+c) r n T t =
      heightPolygon F r n (T+1) u+c/r := by
  let j := ⌊T*n*(t:ℝ)⌋₊
  have h0 : 0 ≤ T*n*(t:ℝ) := mul_nonneg (mul_nonneg hT hn) t.2.1
  have hj0 : (j:ℝ) ≤ T*n*(t:ℝ) := Nat.floor_le h0
  have hj1 : T*n*(t:ℝ) ≤ (j:ℝ)+1 := (Nat.lt_floor_add_one _).le
  rw [heightPolygon_formula _ _ _ _ (mul_nonneg hT hn),
    heightPolygon_segment F r n (T+1) (mul_nonneg (by linarith) hn) (j+H) u
      (by rw [hu]; push_cast; linarith)
      (by rw [hu]; push_cast; linarith),hu]
  simp only [Nat.cast_add,Nat.add_assoc,Nat.add_comm 1 H]
  dsimp only [j]
  ring

lemma heightPolygon_translate_norm_le (F : ℕ → ℝ) (r n T : ℝ)
    (hn : 0 < n) (hT : 0 ≤ T) (H : ℕ) (hH : (H:ℝ) ≤ n) (c ε δ : ℝ)
    (hδ : (H:ℝ)/n ≤ δ)
    (hmod : heightPolygon F r n (T+1) ∉ ContinuousOscillation ε δ) :
    ‖heightPolygon (fun k => F (k+H)+c) r n T-heightPolygon F r n T‖ ≤ ε+|c/r| := by
  have hL : 0 < T+1 := by linarith
  have hLn : 0 < (T+1)*n := mul_pos hL hn
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  let s : unitInterval := ⟨T/(T+1)*(t:ℝ),mul_nonneg (div_nonneg hT hL.le) t.2.1,
    (mul_le_of_le_one_right (div_nonneg hT hL.le) t.2.2).trans
      ((div_le_one hL).mpr (by linarith))⟩
  let u : unitInterval := ⟨(T*n*(t:ℝ)+(H:ℝ))/((T+1)*n),
    div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hT hn.le) t.2.1) (Nat.cast_nonneg _)) hLn.le,
    (div_le_one hLn).mpr (by nlinarith [mul_le_of_le_one_right (mul_nonneg hT hn.le) t.2.2])⟩
  have hs : (T+1)*n*(s:ℝ) = T*n*(t:ℝ) := by dsimp [s]; field_simp
  have hu : (T+1)*n*(u:ℝ) = T*n*(t:ℝ)+(H:ℝ) := by dsimp [u]; field_simp
  have hdist : dist u s ≤ δ := by
    have he : (u:ℝ)-(s:ℝ) = (H:ℝ)/((T+1)*n) := by dsimp [u,s]; field_simp; ring
    rw [Subtype.dist_eq,Real.dist_eq,he,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hLn.le)]
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg H) hn (by nlinarith)).trans hδ
  have hm : |heightPolygon F r n (T+1) u-heightPolygon F r n (T+1) s| ≤ ε :=
    le_of_not_gt (fun h => hmod ⟨u,s,hdist,h⟩)
  have hsval := heightPolygon_translate_apply F r n T hn.le hT 0 0 t s (by simpa using hs)
  simp only [add_zero,zero_div] at hsval
  simp only [ContinuousMap.sub_apply,Real.norm_eq_abs]
  rw [heightPolygon_translate_apply F r n T hn.le hT H c t u hu,hsval]
  calc
    |heightPolygon F r n (T+1) u+c/r-heightPolygon F r n (T+1) s|
      = |(heightPolygon F r n (T+1) u-heightPolygon F r n (T+1) s)+c/r| := by ring_nf
    _ ≤ |heightPolygon F r n (T+1) u-heightPolygon F r n (T+1) s|+|c/r| := abs_add_le _ _
    _ ≤ ε+|c/r| := by gcongr

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
