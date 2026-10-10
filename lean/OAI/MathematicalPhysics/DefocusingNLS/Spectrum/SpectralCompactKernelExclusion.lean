import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactKernelLimit
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

/-! Absence of a limiting compact kernel excludes nearby kernels. -/

open Filter Topology
namespace DefocusingNLS

theorem compact_kernel_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : ℕ → E →L[ℂ] E) (K₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hc : IsCompactOperator K₀)
    (hzero : ∀ v, K₀ v=v → v=0) :
    ∀ᶠ n in atTop, ∀ v, K n v=v → v=0 := by
  have hunit : ∀ᶠ n in atTop, ¬∃ v, ‖v‖=1 ∧ K n v=v := by
    by_contra h
    have hf : ∃ᶠ n in atTop, ∃ v, ‖v‖=1 ∧ K n v=v := by
      exact h
    obtain ⟨φ,hφ,hv⟩ := exists_seq_forall_of_frequently hf
    choose v hvn hve using hv
    obtain ⟨v₀,hn,he⟩ := compact_kernel_limit (K ∘ φ) K₀ (hK.comp hφ) hc v hvn hve
    rw [hzero v₀ he,norm_zero] at hn
    exact zero_ne_one hn
  filter_upwards [hunit] with n hn v hv
  by_contra hne
  apply hn
  refine ⟨((‖v‖ : ℂ)⁻¹) • v,?_,?_⟩
  · rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  · rw [map_smul,hv]

end DefocusingNLS

end OAI
