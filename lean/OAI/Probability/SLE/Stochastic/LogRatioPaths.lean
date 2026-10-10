import OAI.Probability.SLE.Stochastic.PlanarLogLifting

namespace OAI

/-! Continuous logarithms used in the local crosscut separation argument.
Moving a puncture along a path gives a logarithm of the endpoint ratio on
the complement of that path. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma continuous_log_ratio_off_path {a b : ℂ} (p : Path a b) :
    ∃ L : C({z : ℂ // z∉range p},ℂ),
      ∀ z, Complex.exp (L z)=((z:ℂ)-b)/((z:ℂ)-a) := by
  let D := {z : ℂ // z∉range p}
  have hn (z : D) (t : unitInterval) : (z:ℂ)-p t≠0 := by
    intro h
    exact z.property ⟨t,(sub_eq_zero.mp h).symm⟩
  have hden (z : D) : (z:ℂ)-a≠0 := by simpa using hn z 0
  let H : C(unitInterval × D,ℂ) :=
    ⟨fun q => ((q.2:ℂ)-p q.1)/((q.2:ℂ)-a),
      ((continuous_subtype_val.comp continuous_snd).sub (p.continuous.comp continuous_fst)).div
        ((continuous_subtype_val.comp continuous_snd).sub continuous_const) (fun q => hden q.2)⟩
  obtain ⟨L,hL⟩ := continuous_log_at_end_of_homotopy H
    (fun q => div_ne_zero (hn q.2 q.1) (hden q.2)) (ContinuousMap.const D 0)
    (fun z => by simp [H,hden z])
  exact ⟨L,fun z => by simpa [H] using hL z⟩

lemma continuous_log_on_ball_away (c a : ℂ) (r : ℝ) (hr : 0<r)
    (ha : a∉ball c r) :
    ∃ L : C(ball c r,ℂ), ∀ z, Complex.exp (L z)=(z:ℂ)-a := by
  have hca : c-a≠0 := by
    intro h
    exact ha (sub_eq_zero.mp h ▸ mem_ball_self hr)
  let H : C(unitInterval × ball c r,ℂ) :=
    ⟨fun q => c+(q.1:ℂ)*((q.2:ℂ)-c)-a,by fun_prop⟩
  have hn (q : unitInterval × ball c r) : H q≠0 := by
    have hm : c+(q.1:ℂ)*((q.2:ℂ)-c)∈ball c r := by
      rw [mem_ball,dist_eq_norm]
      rw [show c+(q.1:ℂ)*((q.2:ℂ)-c)-c=(q.1:ℂ)*((q.2:ℂ)-c) by ring]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg q.1.property.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) q.1.property.2).trans_lt
        (by simpa only [mem_ball,dist_eq_norm] using q.2.property)
    intro h
    exact ha (sub_eq_zero.mp h ▸ hm)
  obtain ⟨L,hL⟩ := continuous_log_at_end_of_homotopy H hn
    (ContinuousMap.const (ball c r) (Complex.log (c-a)))
    (fun z => by simp [H,Complex.exp_log hca])
  refine ⟨L,fun z => ?_⟩
  simpa [H] using hL z

end SLEExactGauge

end

end OAI
