import OAI.MeasureTheory.Falconer.Estimates.DyadicCells
import OAI.MeasureTheory.Falconer.Estimates.DyadicLinearApproximation

namespace OAI

/-! Selection of a bounded-scale family of intervals with uniform linear error. -/
namespace Falconer
open Set

noncomputable def dyadicLinearPieces (f : ℝ → ℝ) (a h η : ℝ) (n m : ℕ) : List (ℝ × ℝ) := by
  classical
  exact (dyadicCells a h n).filter fun c =>
    dyadicSlopeVariance f c.1 c.2 (intervalSecantSlope f c.1 c.2) m ≤ η^2

theorem exists_dyadic_linear_pieces {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h η : ℝ} (hh : 0 < h) (hη : 0 < η) (m L : ℕ) (hL : 0 < L) :
    ∃ n ≤ L*m,
      (dyadicLinearPieces f a h η n m).Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
      h*(1-4/((L : ℝ)*η^2)) ≤ ((dyadicLinearPieces f a h η n m).map Prod.snd).sum ∧
      ∀ c ∈ dyadicLinearPieces f a h η n m,
        a ≤ c.1 ∧ c.1+c.2 ≤ a+h ∧ c.2 = h/(2 : ℝ)^n ∧
        ∀ x ∈ Icc c.1 (c.1+c.2),
          |intervalSecantError f c.1 c.2 x| ≤ c.2*(η+4/(2 : ℝ)^m) := by
  classical
  obtain ⟨j,hj,hinc⟩ := exists_small_dyadic_energy_increment hf a hh m L hL
  let V : ℝ → ℝ → ℝ := fun u l =>
    dyadicSlopeVariance f u l (intervalSecantSlope f u l) m
  let G := dyadicAverage (fun u l => if V u l ≤ η^2 then 1 else 0) a h (j*m)
  let B := dyadicAverage (fun u l => if η^2 < V u l then 1 else 0) a h (j*m)
  have hM : η^2*B ≤ dyadicAverage V a h (j*m) :=
    dyadicAverage_markov (fun u l => dyadicSlopeVariance_nonneg f u l _ m) a h (η^2) (j*m)
  have hE : dyadicAverage V a h (j*m) ≤ 4/(L : ℝ) := by
    dsimp [V]
    rw [dyadicAverage_centered_variance f a hh]
    simpa only [Nat.add_mul,Nat.one_mul] using hinc
  have hB : B ≤ 4/((L : ℝ)*η^2) := by
    rw [← div_div]
    apply (le_div_iff₀ (sq_pos_of_pos hη)).2
    nlinarith [hM.trans hE]
  have hGB : G+B = 1 := by
    dsimp [G,B]
    rw [← dyadicAverage_add]
    have he : (fun u l => (if V u l ≤ η^2 then (1 : ℝ) else 0)+
        (if η^2 < V u l then 1 else 0)) = fun _ _ => (1 : ℝ) := by
      funext u l
      by_cases hv : V u l ≤ η^2
      · simp [hv,not_lt.mpr hv]
      · simp [hv,lt_of_not_ge hv]
    rw [he,dyadicAverage_const]
  have hG : 1-4/((L : ℝ)*η^2) ≤ G := by linarith
  refine ⟨j*m,Nat.mul_le_mul_right m hj.le,?_,?_,?_⟩
  · exact (dyadicCells_ordered a hh.le (j*m)).filter _
  · rw [dyadicLinearPieces,dyadicCells_selected_length (fun u l => V u l ≤ η^2)]
    exact mul_le_mul_of_nonneg_left hG hh.le
  · intro c hc
    obtain ⟨hc,hv⟩ := List.mem_filter.mp hc
    have hb := dyadicCells_bounds a hh.le (j*m) hc
    refine ⟨hb.1,hb.2.1,hb.2.2,?_⟩
    intro x hx
    have hcpos : 0 < c.2 := by rw [hb.2.2]; positivity
    have he := dyadic_linear_approximation hf c.1 hcpos hη.le m (of_decide_eq_true hv) hx
    convert he using 1; ring

end Falconer

end OAI
