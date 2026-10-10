import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePropagation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeTaylor

namespace OAI

/-! Quantitative Taylor propagation for arbitrary complex initial data. -/

open Set MeasureTheory Filter
namespace DefocusingNLS

theorem radial_free_linear_taylor (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ))
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) (f₀ g₀ : ℂ)
    (heF : ∀ r ∈ Icc l u, F r=f₀+∫ t in l..r, G t)
    (heG : ∀ r ∈ Icc l u, G r=g₀+∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t) :
    ∀ r ∈ Icc l u,
      ‖G r-g₀‖ ≤ 14*‖(f₀,g₀)‖*(r-l) ∧
      ‖F r-f₀-g₀*((r-l : ℝ) : ℂ)‖ ≤ 7*‖(f₀,g₀)‖*(r-l)^2 := by
  have hX := radial_free_components_state b l u (by linarith) F G hF hG f₀ g₀ heF heG
  have hbound := radial_free_state_bound b l u hb hl hu hlu hwidth
    (fun t => (F t,G t)) (hF.prodMk hG) (f₀,g₀) hX
  have hGb : ∀ r ∈ Icc l u, ‖G r-g₀‖ ≤ 14*‖(f₀,g₀)‖*(r-l) := by
    intro r hr
    have he : G r-g₀=∫ t in l..r, -radialFreeCoefficient t*G t-(b : ℂ)*F t := by
      rw [heG r hr]; ring
    rw [he]
    apply radial_complex_integral_bound l r _ hr.1
    intro t ht
    exact (norm_snd_le (radialFreeField b t (F t,G t))).trans
      ((radialFreeField_norm b t hb ⟨hl.trans ht.1,ht.2.trans (hr.2.trans hu)⟩ (F t,G t)).trans
        (by nlinarith [hbound t ⟨ht.1,ht.2.trans hr.2⟩]))
  intro r hr
  refine ⟨hGb r hr,?_⟩
  have he : F r-f₀-g₀*((r-l : ℝ) : ℂ)=∫ t in l..r, G t-g₀ := by
    rw [intervalIntegral.integral_sub (f := G) (g := fun _ : ℝ => g₀)
      (hG.intervalIntegrable l r) (continuous_const.intervalIntegrable l r),
      intervalIntegral.integral_const,Complex.real_smul,heF r hr]
    ring
  rw [he]
  have hi : (∫ t in l..r, 14*‖(f₀,g₀)‖*(t-l))=7*‖(f₀,g₀)‖*(r-l)^2 := by
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
      (f := fun t : ℝ => t) (g := fun _ : ℝ => l)
      (continuous_id.intervalIntegrable l r) (continuous_const.intervalIntegrable l r),
      integral_id,intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [← hi]
  exact intervalIntegral.norm_integral_le_of_norm_le hr.1
    (Eventually.of_forall (fun t ht => hGb t ⟨ht.1.le,ht.2.trans hr.2⟩))
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable l r)

end DefocusingNLS

end OAI
