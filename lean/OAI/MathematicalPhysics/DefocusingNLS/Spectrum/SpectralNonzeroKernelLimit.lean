import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactKernelLimit

namespace OAI

/-! Normalize an eventual sequence of nonzero kernels before taking its compact limit. -/

open Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_kernel_limit_of_eventually_nonzero
    (K : ℕ → E →L[ℂ] E) (K₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hc : IsCompactOperator K₀)
    (v : ℕ → E) (hv : ∀ᶠ n in atTop, K n (v n)=v n ∧ v n ≠ 0) :
    ∃ v₀ : E, ‖v₀‖=1 ∧ K₀ v₀=v₀ := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hv
  let w := fun n => ((‖v (n+N)‖ : ℂ)⁻¹) • v (n+N)
  have hne (n : ℕ) : ‖v (n+N)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hN (n+N) (Nat.le_add_left N n)).2
  have hw (n : ℕ) : ‖w n‖=1 := by
    dsimp [w]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (hne n)]
  have he (n : ℕ) : K (n+N) (w n)=w n := by
    dsimp [w]
    rw [map_smul,(hN (n+N) (Nat.le_add_left N n)).1]
  exact compact_kernel_limit (fun n => K (n+N)) K₀
    (hK.comp (tendsto_add_atTop_nat N)) hc w hw he

end DefocusingNLS

end OAI
