import Mathlib
import OAI.Analysis.HardSphere.Density.GroundSpace
import OAI.Analysis.HardSphere.Fourier.FreeCompactForm
import OAI.Analysis.HardSphere.Thermodynamics.MixedCondensation

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology ComplexOrder ENNReal
namespace HardSphere

lemma groundSpace_finiteDimensional (N : ℕ) (L : Length) {a : ℝ} (ha : 0<a) :
    FiniteDimensional ℂ (groundSpace N L a) := by
  classical
  by_cases hg : ∃u : Jet N L,IsGroundVector N L a u
  · obtain ⟨u,hu⟩ := hg
    have hE : 0≤energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hc : (1+(energy u:ℂ))⁻¹≠0 := by
      apply inv_ne_zero
      exact_mod_cast (show (1:ℝ)+energy u≠0 by linarith)
    have := ContinuousLinearMap.finite_dimensional_eigenspace
      (formResolvent_compact N L ha) ((1+(energy u:ℂ))⁻¹) hc
    exact Submodule.finiteDimensional_of_le ((groundSpace_le_resolvent hu).trans inf_le_left)
  · rw [groundSpace_eq_bot_of_no_ground hg]
    infer_instance

lemma groundSupported_iff_support_le {N : ℕ} {L : Length} {a : ℝ}
    (T : Density.Operator (ScalarL2 N L)) :
    GroundSupported a T ↔ T.toCLM.kerᗮ≤groundSpace N L a := by
  constructor
  · intro hT ψ hψ
    by_cases hz : ψ=0
    · rw [hz]; exact (groundSpace N L a).zero_mem
    · have hn : ‖ψ‖≠0 := norm_ne_zero_iff.mpr hz
      let z : ℂ := (‖ψ‖:ℂ)⁻¹
      have hzn : ‖z‖=‖ψ‖⁻¹ := by
        simp only [z,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg ψ)]
      have hunit : ‖z • ψ‖=1 := by rw [norm_smul,hzn,inv_mul_cancel₀ hn]
      obtain ⟨u,hu,hg⟩ := hT (z • ψ) ((T.toCLM.kerᗮ).smul_mem z hψ) hunit
      have hm : z • ψ∈groundSpace N L a := hu ▸ hg.mem_groundSpace
      have hh := (groundSpace N L a).smul_mem (‖ψ‖:ℂ) hm
      have hc : (‖ψ‖:ℂ)≠0 := by exact_mod_cast hn
      simpa only [z,smul_smul,mul_inv_cancel₀ hc,one_smul] using hh
  · intro hT ψ hψ hn
    exact (groundSpace_normalized_iff hn).mp (hT hψ)

attribute [local instance] scalarL2_norm_exponent
attribute [local instance] scalarL2_normedAddCommGroup
attribute [local instance] scalarL2_innerProductSpace
attribute [local instance] scalarL2_module
attribute [local instance] scalarL2_completeSpace

lemma groundSpace_nontrivial_of_ne_bot (N : ℕ) (L : Length) (a : ℝ)
    (hG : @Ne (@Submodule ℂ (ScalarL2 N L) Complex.instSemiring
      (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L))
      (groundSpace N L a) (@Bot.bot
        (@Submodule ℂ (ScalarL2 N L) Complex.instSemiring
          (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L))
        (@Submodule.instBot ℂ (ScalarL2 N L) Complex.instSemiring
        (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L)))) :
    Nontrivial (groundSpace N L a) :=
  Submodule.nontrivial_iff_ne_bot.mpr hG

/-- Precisely Π/Tr Π for the orthogonal projection on the entire bosonic ground space.
The nonzero condition is exactly the domain of normalization, not a finite-rank assumption. -/
abbrev normalizedGroundProjection (N : ℕ) (L : Length) (a : ℝ)
    (ha : @LT.lt ℝ Real.instLT (@Zero.zero ℝ Real.instZero) a)
    (hG : @Ne (@Submodule ℂ (ScalarL2 N L) Complex.instSemiring
      (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L))
      (groundSpace N L a) (@Bot.bot
        (@Submodule ℂ (ScalarL2 N L) Complex.instSemiring
          (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L))
        (@Submodule.instBot ℂ (ScalarL2 N L) Complex.instSemiring
        (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L)))) :
    @Density.Operator (ScalarL2 N L) (scalarL2_normedAddCommGroup N L)
      (scalarL2_innerProductSpace N L) (scalarL2_completeSpace N L) :=
  @Density.normalizedProjection.{0} (ScalarL2 N L)
    (scalarL2_normedAddCommGroup N L) (scalarL2_innerProductSpace N L)
    (scalarL2_completeSpace N L)
    (groundSpace N L a) (@groundSpace_finiteDimensional N L a ha)
    (groundSpace_nontrivial_of_ne_bot N L a hG)

lemma normalizedGroundProjection_formula (N : ℕ) (L : Length) (a : ℝ) (ha : 0<a)
    (hG : groundSpace N L a≠⊥) :
    let := groundSpace_finiteDimensional N L ha
    (normalizedGroundProjection N L a ha hG).toCLM =
      ((Module.finrank ℂ (groundSpace N L a):ℝ)⁻¹) • (groundSpace N L a).starProjection := by
  rfl

lemma normalizedGroundProjection_supported (N : ℕ) (L : Length) (a : ℝ) (ha : 0<a)
    (hG : groundSpace N L a≠⊥) :
    GroundSupported a (normalizedGroundProjection N L a ha hG) := by
  let := groundSpace_finiteDimensional N L ha
  let := Submodule.nontrivial_iff_ne_bot.mpr hG
  rw [groundSupported_iff_support_le]
  change (Density.normalizedProjection (groundSpace N L a)).toCLM.kerᗮ≤groundSpace N L a
  rw [Density.normalizedProjection_support]

lemma IsGroundVector.groundSpace_ne_bot {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) : groundSpace N L a≠⊥ :=
  Submodule.nontrivial_iff_ne_bot.mp (groundSpace_nontrivial hu)

end HardSphere
end
end

end OAI
