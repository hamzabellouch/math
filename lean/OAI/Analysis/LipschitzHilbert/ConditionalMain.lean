import OAI.Analysis.LipschitzHilbert.Estimates.ConditionalUniformTruncation
import OAI.Analysis.LipschitzHilbert.Estimates.ShortTransformExtension

namespace OAI

/-! Theorem 1.1 of the supplied manuscript, conditional on the four
precisely cited published inputs. The principal value is the actual
pointwise symmetric limit on Schwartz functions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

def ShortHilbertConclusion (a : ℝ) (C : ℝ≥0) : Prop :=
  ∀ v : Plane → Plane, LipschitzWith 1 v → (∀ x, ‖v x‖=1) →
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a → ∀ f : SchwartzMap Plane ℂ,
      eLpNorm (twoSidedTruncation v epsilon a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ,
      eLpNorm (smoothPrincipalValue v a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ, ∀ level : ℝ≥0∞, level≠0 → level≠∞ →
      volume {x | level<‖smoothPrincipalValue v a f x‖ₑ}≤
        level⁻¹^2*((C:ℝ≥0∞)*eLpNorm f 2 volume)^2) ∧
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a →
      ∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
        ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
          (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] twoSidedTruncation v epsilon a f) ∧
    (∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
      ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
        (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] smoothPrincipalValue v a f)

theorem conditional_main (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C := by
  obtain ⟨B,hB,hbound⟩ := conditional_uniform_truncation hVariation hLL hH hReassembly
  let C : ℝ≥0 := ⟨B,hB.le⟩
  let a : ℝ := 1/1000000
  have ha : 0<a := by norm_num [a]
  have hBcoe : ENNReal.ofReal B=(C:ℝ≥0∞) := by
    change ENNReal.ofReal (C:ℝ)=(C:ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  refine ⟨a,⟨ha,by norm_num [a]⟩,C,hB,?_⟩
  intro v hv hunit
  have hb (f : SchwartzMap Plane ℂ) (epsilon : ℝ) (he : 0<epsilon) (hea : epsilon<a) :
      eLpNorm (shortTransform v epsilon a f) 2 volume≤C*eLpNorm f 2 volume := by
    have h := hbound 1 (by norm_num) epsilon a he hea.le (by norm_num [a]) v hv hunit f
    rw [ENNReal.ofReal_mul hB.le,SchwartzMap.norm_toLp,
      ENNReal.ofReal_toReal (f.memLp 2 volume).eLpNorm_ne_top,hBcoe] at h
    exact h
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro epsilon he hea f
    have heq : twoSidedTruncation v epsilon a f=shortTransform v epsilon a f := by
      funext x
      exact twoSidedTruncation_eq_shortTransform v f.continuous he hea.le x
    rw [heq]
    exact hb f epsilon he hea
  · intro f
    exact smoothPrincipalValue_eLpNorm_le hv.continuous f.differentiable ha (hb f)
  · intro f level hl hlfin
    exact smoothPrincipalValue_weak_two hv.continuous f.differentiable ha (hb f) hl hlfin
  · intro epsilon he hea
    obtain ⟨T,hT,hTf⟩ := exists_shortTransform_extension v epsilon a he hea.le C
      (fun f => hb f epsilon he hea)
    refine ⟨T,hT,?_⟩
    intro f
    have heq : twoSidedTruncation v epsilon a f=shortTransform v epsilon a f := by
      funext x
      exact twoSidedTruncation_eq_shortTransform v f.continuous he hea.le x
    rw [heq]
    exact hTf f
  · exact exists_smoothPrincipalValue_extension hv.continuous ha hb

end LipschitzHilbert

end

end OAI
