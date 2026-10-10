import OAI.Analysis.FiniteFactor.CrossedProduct.TorusRotation
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

abbrev sourceRotationL2 (θ : SourceCoordinate → ℝ) :
    Lp ℂ 2 sourceTorusHaar →ₗᵢ[ℂ] Lp ℂ 2 sourceTorusHaar :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceTorusRotationStep θ) (sourceTorusRotationStep_preserving θ)

theorem sourceCharacterL2_zero_inner :
    inner ℂ (sourceCharacterL2 0) (sourceCharacterL2 0) = 1 := by
  rw [ContinuousMap.inner_toLp]
  simp [sourceCharacter_zero]

theorem sourceRotationL2_zero_character (θ : SourceCoordinate → ℝ) :
    sourceRotationL2 θ (sourceCharacterL2 0) = sourceCharacterL2 0 := by
  change Lp.compMeasurePreserving _ _ _ = _
  rw [sourceCharacterL2_rotation,sourceCharacter_zero]
  simp

/-- An invariant vector orthogonal to the constant character is zero. -/
theorem sourceRotationL2_fixed_orthogonal_zero (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (f : Lp ℂ 2 sourceTorusHaar)
    (hf : sourceRotationL2 θ f = f) (h0 : inner ℂ (sourceCharacterL2 0) f = 0) : f = 0 := by
  have hchar (v : SourceCoordinate →₀ ℤ) : inner ℂ f (sourceCharacterL2 v) = 0 := by
    by_cases hv : v = 0
    · subst v
      exact inner_eq_zero_symm.mpr h0
    · have he := (sourceRotationL2 θ).inner_map_map f (sourceCharacterL2 v)
      rw [hf] at he
      change inner ℂ f (Lp.compMeasurePreserving _ _ _) = _ at he
      rw [sourceCharacterL2_rotation,inner_smul_right] at he
      have hn := sourceCharacter_nonresonant θ hr v hv
      by_contra hz
      exact hn (mul_right_cancel₀ hz (he.trans (one_mul _).symm))
  have hs : span ℂ (range sourceCharacterL2) ≤ (innerSL ℂ f).ker := by
    apply span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact hchar v
  have ht : (span ℂ (range sourceCharacterL2)).topologicalClosure ≤ (innerSL ℂ f).ker :=
    Submodule.topologicalClosure_minimal _ hs (innerSL ℂ f).isClosed_ker
  rw [sourceCharacterL2_span_dense] at ht
  have hh : inner ℂ f f = 0 := ht (show f ∈ (⊤ : Submodule ℂ (Lp ℂ 2 sourceTorusHaar)) from trivial)
  exact inner_self_eq_zero.mp hh

theorem sourceRotationL2_fixed_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (f : Lp ℂ 2 sourceTorusHaar)
    (hf : sourceRotationL2 θ f = f) :
    ∃ c : ℂ, f = c • sourceCharacterL2 0 := by
  let c := inner ℂ (sourceCharacterL2 0) f
  refine ⟨c,sub_eq_zero.mp (sourceRotationL2_fixed_orthogonal_zero θ hr
    (f-c • sourceCharacterL2 0) ?_ ?_)⟩
  · rw [map_sub,map_smul,hf,sourceRotationL2_zero_character]
  · rw [inner_sub_right,inner_smul_right,sourceCharacterL2_zero_inner,mul_one]
    exact sub_self _

theorem sourceTorus_invariant_memLp_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) {f : SourceTorus → ℂ}
    (hf : MemLp f 2 sourceTorusHaar)
    (hinv : f ∘ sourceTorusRotationStep θ =ᵐ[sourceTorusHaar] f) :
    ∃ c : ℂ, f =ᵐ[sourceTorusHaar] fun _ => c := by
  have hfix : sourceRotationL2 θ (hf.toLp f) = hf.toLp f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hf.toLp f) (sourceTorusRotationStep_preserving θ),
      (sourceTorusRotationStep_preserving θ).quasiMeasurePreserving.ae hf.coeFn_toLp,
      hf.coeFn_toLp,hinv] with x hc ht hx hi
    exact hc.trans (ht.trans (hi.trans hx.symm))
  obtain ⟨c,hc⟩ := sourceRotationL2_fixed_constant θ hr (hf.toLp f) hfix
  refine ⟨c,?_⟩
  have he := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ℝ≥0∞)) sourceTorusHaar (sourceCharacter 0)
  filter_upwards [hf.coeFn_toLp,Lp.coeFn_smul c (sourceCharacterL2 0),he] with x hx hs he
  rw [hc,hs,Pi.smul_apply,smul_eq_mul,he,sourceCharacter_zero] at hx
  simpa using hx.symm

/-- Ergodicity of the constructed countable-torus rotation itself. -/
theorem sourceTorusRotationStep_ergodic (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) : Ergodic (sourceTorusRotationStep θ) sourceTorusHaar := by
  classical
  refine ⟨sourceTorusRotationStep_preserving θ,⟨fun s hs hi => ?_⟩⟩
  have hm : MemLp (s.indicator (fun _ : SourceTorus => (1 : ℂ))) 2 sourceTorusHaar :=
    (memLp_const (1 : ℂ)).indicator hs
  have hinv : (s.indicator (fun _ : SourceTorus => (1 : ℂ))) ∘ sourceTorusRotationStep θ =ᵐ[sourceTorusHaar]
      s.indicator (fun _ : SourceTorus => (1 : ℂ)) := by
    apply Eventually.of_forall
    intro x
    have hh : sourceTorusRotationStep θ x ∈ s ↔ x ∈ s := by
      change x ∈ (sourceTorusRotationStep θ) ⁻¹' s ↔ x ∈ s
      rw [hi]
    by_cases hx : x ∈ s
    · simp [Function.comp_apply,hx,hh.mpr hx]
    · have ht : sourceTorusRotationStep θ x ∉ s := fun h => hx (hh.mp h)
      simp [Function.comp_apply,hx,ht]
  obtain ⟨c,hc⟩ := sourceTorus_invariant_memLp_constant θ hr hm hinv
  rw [Filter.eventuallyEmptyOrUniv_iff']
  by_cases h1 : c = 1
  · right
    filter_upwards [hc] with x hx
    apply propext
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs,h1] at hx
  · left
    filter_upwards [hc] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs] at hx
      exact (h1 hx.symm).elim
    · apply propext
      simp [hxs]

end
end FiniteFactor

end OAI
