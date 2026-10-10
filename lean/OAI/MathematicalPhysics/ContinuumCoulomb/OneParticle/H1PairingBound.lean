import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakH1Pairing

namespace OAI

/-! An L2 residual controls its pairing with every weak-H1 state. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem h1_real_pairing_sq_le {n : ℕ} (v : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (φ : Configuration n → ℝ) (hφ : MemLp φ 2) :
    ‖∫ x, v.value s x*(φ x : ℂ)‖^2 ≤
      (∫ x, φ x^2)*(∫ x, ‖v.value s x‖^2) := by
  let Φ : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    hφ.ofReal.toLp (fun x => (φ x : ℂ))
  have hm : MemLp (fun x => (φ x : ℂ)) 2 := hφ.ofReal
  have hnorm : ‖Φ‖^2 = ∫ x, φ x^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    change Φ x = (φ x : ℂ) at hx
    rw [real_inner_self_eq_norm_sq,hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [← h1_inner_real_orbital v s φ hφ]
  change ‖inner ℂ Φ (h1Coordinates v (Sum.inl s))‖^2 ≤ _
  have h := pow_le_pow_left₀ (norm_nonneg (inner ℂ Φ (h1Coordinates v (Sum.inl s))))
    (norm_inner_le_norm (𝕜 := ℂ) Φ (h1Coordinates v (Sum.inl s))) 2
  rw [mul_pow,hnorm,h1Coordinates_norm_sq] at h
  exact h

end ContinuumCoulomb

end

end OAI
