import OAI.Geometry.SurfaceImmersion.Correction.LinearPhaseMeanGeometry
import OAI.Geometry.SurfaceImmersion.Correction.CompactMeanBudgets

namespace OAI

/-! Actual numerical mean budgets for the restricted linear phase chart,
obtained from compact containment in the immersion's good-direction set. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean

theorem linear_phase_budgets {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ Ω, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor F x) ξ)
    {ψ : Base → ℝ} (hψ : ContDiff ℝ ∞ ψ) (Q : PhaseMean.Tensor →L[ℝ] ℝ) :
    Nonempty (Budgets U (linearPhaseChart ξ hξ U hU).target 1
      (F ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
      (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm) := by
  let L := phaseEquiv ξ hξ
  let V := L '' U
  let KV := L '' K
  let ΩV := L '' Ω
  have hV : IsOpen V := L.isOpenMap U hU
  have hKV : IsCompact KV := hK.image L.continuous
  have hVK : V ⊆ KV := image_mono hUK
  have hKVΩ : KV ⊆ ΩV := image_mono hKΩ
  have hmap : ContDiff ℝ ∞ (F ∘ L.symm) := hF.comp L.symm.contDiff
  have hdom : RealModeDomain (F ∘ L.symm) ΩV :=
    realModeDomain_phase hF hΩ hξ hImm hgood
  have hpull : ContDiffOn ℝ ∞ (pullbackField (linearPhaseChart ξ hξ U hU)) univ := by
    have hh : pullbackField (linearPhaseChart ξ hξ U hU) =
        fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [hh]
    exact contDiffOn_const
  exact compact_mean_budgets hU hV isOpen_univ hK hKV hUK hVK (subset_univ K) hKVΩ
    hmap hdom hψ.contDiffOn contDiffOn_const
    (linearPhaseChart_smooth ξ hξ U hU).1.contDiffOn
    (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn hpull

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
