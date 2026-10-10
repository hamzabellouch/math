import OAI.MeasureTheory.Falconer.Graphs.GraphScaleDirection

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_strong_separation_endpoints (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center) (hu : dist P.center Q.center ≤ 2000*s)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    96*s ≤ dist x y ∧ dist x y ≤ 2004*s := by
  have hx' := P.dist_le hP.le hx (P.center_mem hP)
  have hy' := Q.dist_le hQ.le hy (Q.center_mem hQ)
  have ht₁ := dist_triangle P.center x Q.center
  have ht₂ := dist_triangle x y Q.center
  have ht₃ := dist_triangle x P.center y
  have ht₄ := dist_triangle P.center Q.center y
  rw [dist_comm P.center x] at ht₁
  rw [dist_comm Q.center y] at ht₄
  constructor <;> linarith

theorem source_strong_separation_frequency (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) (a v : ℝ)
    (hp : P.side ≤ (2:ℝ)^(-a)) (hq : Q.side ≤ (2:ℝ)^(-a))
    (hl : 100*(2:ℝ)^(-a) ≤ dist P.center Q.center)
    (hu : dist P.center Q.center ≤ 2000*(2:ℝ)^(-a))
    (Ψ : ℝ → ℝ) (hΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    {r : ℝ} (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :
    x ≠ y ∧ 0 < r ∧ 24*(2:ℝ)^(v-a) ≤ r*‖x-y‖ ∧
      r*‖x-y‖ ≤ 8016*(2:ℝ)^(v-a) := by
  have hA : 0 < (2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have hS : 0 < (2:ℝ)^(-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hd := dyadic_strong_separation_endpoints P Q hP hQ hp hq hl hu hx hy
  have hdpos : 0 < dist x y := (by positivity : 0 < 96*(2:ℝ)^(-a)).trans_le hd.1
  have hrad := hΨ _ hr
  have hrlo : (2:ℝ)^v/4 < r := by
    have hh := (lt_div_iff₀ hA).mp hrad.1
    linarith
  have hrhi : r < 4*(2:ℝ)^v := (div_lt_iff₀ hA).mp hrad.2
  have hrpos : 0 < r := (by positivity : 0 < (2:ℝ)^v/4).trans hrlo
  have he : (2:ℝ)^(v-a) = (2:ℝ)^v*(2:ℝ)^(-a) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  refine ⟨dist_pos.mp hdpos, hrpos, ?_, ?_⟩
  · rw [← dist_eq_norm, he]
    have hh := mul_le_mul hrlo.le hd.1 (by positivity : 0 ≤ 96*(2:ℝ)^(-a)) hrpos.le
    nlinarith
  · rw [← dist_eq_norm, he]
    have hh := mul_le_mul hrhi.le hd.2 dist_nonneg (by positivity : 0 ≤ 4*(2:ℝ)^v)
    nlinarith

end PlanarFalconer

end OAI
