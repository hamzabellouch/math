import Mathlib
import OAI.Analysis.Crouzeix.HomologicalCauchy

namespace OAI

/-! Separate Holomorphic. -/

noncomputable section

open Set Filter Metric Topology Function Complex MeasureTheory

open scoped Interval

namespace CrouzeixHilbert

lemma differentiableOn_parameter_intervalIntegral_pos {U : Set ℂ} (hU : IsOpen U)
    {T : ℝ} (hT : 0 < T) {f : ℂ → ℝ → ℂ}
    (hf : ContinuousOn (uncurry f) (U ×ˢ Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, DifferentiableOn ℂ (fun z => f z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..T, f z t) U := by
  have hmap : MapsTo (fun p : ℂ × ℝ => (p.1, T * p.2))
      (U ×ˢ Icc (0 : ℝ) 1) (U ×ˢ Icc 0 T) := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    exact ⟨hz, mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩
  have hi := differentiableOn_parameter_intervalIntegral hU
    (f := fun z t => f z (T * t))
    (hf.comp (f := fun p : ℂ × ℝ => (p.1, T * p.2)) (by fun_prop) hmap)
    (fun t ht => hd (T * t) ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩)
  have he (z : ℂ) : T • (∫ t in (0 : ℝ)..1, f z (T * t)) =
      ∫ t in (0 : ℝ)..T, f z t := by
    simpa only [mul_zero, mul_one] using intervalIntegral.smul_integral_comp_mul_left
      (f z) (a := 0) (b := 1) T
  exact (hi.const_smul T).congr (fun z _ => (he z).symm)

lemma deriv_eq_circle_parameter {U : Set ℂ} {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) {u : ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : closedBall u R ⊆ U) :
    deriv f u = (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((circleMap 0 R θ * I) / (circleMap 0 R θ) ^ 2) *
          f (u + circleMap 0 R θ) := by
  have he := (hd.mono hRU).deriv_eq_smul_circleIntegral hR
  have hn : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  calc
    deriv f u = (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ w in C(u,R), (1 / (w-u)^2) • f w) := by
        rw [he, smul_eq_mul, inv_mul_cancel_left₀ hn]
    _ = _ := by
      congr 1
      simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      have hm : circleMap u R θ = u + circleMap 0 R θ := by simp [circleMap]
      dsimp only
      rw [hm, add_sub_cancel_left]
      ring

theorem continuousOn_first_derivative {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ → ℂ → ℂ} (hf : ContinuousOn (uncurry f) (U ×ˢ V))
    (hd : ∀ v ∈ V, DifferentiableOn ℂ (fun u => f u v) U) :
    ContinuousOn (fun p : ℂ × ℂ => deriv (fun u => f u p.2) p.1) (U ×ˢ V) := by
  rintro ⟨u,v⟩ ⟨hu,hv⟩
  obtain ⟨δ,hδ,hδU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hu)
  let R := δ / 3
  have hR : 0 < R := div_pos hδ (by norm_num)
  let P := ball u R ×ˢ V
  have hP : IsOpen P := isOpen_ball.prod hV
  have hp : (u,v) ∈ P := ⟨mem_ball_self hR,hv⟩
  have hshift (p : P) (θ : ℝ) : (p.1.1 + circleMap 0 R θ, p.1.2) ∈ U ×ˢ V := by
    refine ⟨hδU ?_,p.2.2⟩
    rw [mem_closedBall, dist_eq_norm]
    have hn := mem_ball.mp p.2.1
    rw [dist_eq_norm] at hn
    have hm : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    calc
      ‖p.1.1 + circleMap 0 R θ - u‖ = ‖(p.1.1-u) + circleMap 0 R θ‖ := by congr 1; ring
      _ ≤ ‖p.1.1-u‖ + ‖circleMap 0 R θ‖ := norm_add_le _ _
      _ ≤ δ := by rw [hm]; dsimp [R] at hn ⊢; linarith
  have hcoeff : Continuous (fun θ : ℝ => (circleMap 0 R θ * I) / (circleMap 0 R θ)^2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ
    exact pow_ne_zero _ (by
      apply norm_ne_zero_iff.mp
      rw [norm_circleMap_zero, abs_of_pos hR]
      exact hR.ne')
  have hfamily : Continuous (fun q : P × ℝ =>
      ((circleMap 0 R q.2 * I) / (circleMap 0 R q.2)^2) *
        f (q.1.1.1 + circleMap 0 R q.2) q.1.1.2) := by
    apply (hcoeff.comp continuous_snd).mul
    exact hf.comp_continuous (f := fun q : P × ℝ =>
      (q.1.1.1 + circleMap 0 R q.2, q.1.1.2)) (by fun_prop) (fun q => hshift q.1 q.2)
  have hc := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun (p : P) θ => ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
      f (p.1.1 + circleMap 0 R θ) p.1.2) hfamily 0 (2 * Real.pi)).const_mul (2 * (Real.pi : ℂ) * I)⁻¹
  have hc' : ContinuousOn (fun p : ℂ × ℂ => (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
          f (p.1 + circleMap 0 R θ) p.2) P :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  have he : EqOn (fun p : ℂ × ℂ => deriv (fun w => f w p.2) p.1)
      (fun p => (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
          f (p.1 + circleMap 0 R θ) p.2) P := by
    intro p hp
    apply deriv_eq_circle_parameter (hd _ hp.2) hR
    intro w hw
    apply hδU
    have hd1 := mem_ball.mp hp.1
    have hd2 := mem_closedBall.mp hw
    have hd3 := dist_triangle w p.1 u
    rw [mem_closedBall]
    dsimp [R] at hd1 hd2
    linarith
  exact ((hc'.congr he).continuousAt (hP.mem_nhds hp)).continuousWithinAt

theorem differentiableOn_second_first_derivative {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {f : ℂ → ℂ → ℂ}
    (hf : ContinuousOn (uncurry f) (U ×ˢ V))
    (hd : ∀ v ∈ V, DifferentiableOn ℂ (fun u => f u v) U)
    (hv : ∀ u ∈ U, DifferentiableOn ℂ (f u) V) {u : ℂ} (hu : u ∈ U) :
    DifferentiableOn ℂ (fun v => deriv (fun w => f w v) u) V := by
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hu)
  have hshift (θ : ℝ) : u + circleMap 0 R θ ∈ U := by
    apply hRU
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      norm_circleMap_zero, abs_of_pos hR]
  have hcoeff : Continuous (fun θ : ℝ => (circleMap 0 R θ * I) / (circleMap 0 R θ)^2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ
    apply pow_ne_zero
    apply norm_ne_zero_iff.mp
    rw [norm_circleMap_zero, abs_of_pos hR]
    exact hR.ne'
  have hfamily : ContinuousOn (fun q : ℂ × ℝ =>
      ((circleMap 0 R q.2 * I) / (circleMap 0 R q.2)^2) *
        f (u + circleMap 0 R q.2) q.1) (V ×ˢ Icc 0 (2*Real.pi)) := by
    apply (hcoeff.comp continuous_snd).continuousOn.mul
    exact hf.comp (f := fun q : ℂ × ℝ => (u + circleMap 0 R q.2, q.1))
      (by fun_prop) (fun q hq => ⟨hshift q.2,hq.1⟩)
  have hh := differentiableOn_parameter_intervalIntegral_pos hV Real.two_pi_pos
    (f := fun v θ => ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
      f (u + circleMap 0 R θ) v) hfamily
    (fun θ _ => (hv _ (hshift θ)).const_mul _)
  exact (hh.const_mul (2 * (Real.pi : ℂ) * I)⁻¹).congr
    (fun v hv => deriv_eq_circle_parameter (hd v hv) hR hRU)

end CrouzeixHilbert

end

end OAI
