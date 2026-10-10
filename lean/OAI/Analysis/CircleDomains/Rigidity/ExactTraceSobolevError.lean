import OAI.Analysis.CircleDomains.Rigidity.ExactTraceSmoothing
import OAI.Analysis.CircleDomains.Rigidity.ZeroTraceEnergy
import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev

namespace OAI

/-! The exact-trace smoothing has a global Sobolev difference. Thus changing
a test to its smooth representative preserves its original boundary trace
and changes its global gradient by an arbitrarily small amount. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem zeroTraceWitness_component_eLpNorm
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    eLpNorm (fun x => (zeroTraceWitness hU hu hs hz hw).weakGrad x i) 2 volume =
      eLpNorm (fun x => hw.weakGrad x i) 2 (volume.restrict U) := by
  have he : (fun x => (zeroTraceWitness hU hu hs hz hw).weakGrad x i) =ᵐ[volume]
      U.indicator (fun x => hw.weakGrad x i) := by
    have hl := zeroTraceWitness_gradient_on hU hu hs hz hw i
    change ∀ᵐ x ∂volume.restrict U, (zeroTraceWitness hU hu hs hz hw).weakGrad x i = hw.weakGrad x i at hl
    have hl' := (ae_restrict_iff' hU.measurableSet).mp hl
    filter_upwards [hl'] with x hx
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
      exact hx hxU
    · rw [indicator_of_notMem hxU]
      exact zeroTraceWitness_zero hU hu hs hz hw i hxU
  rw [eLpNorm_congr_ae he, eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet]

 theorem exists_exact_trace_smoothing_global_error
    (Ω : TopologicalSpace.Opens EuclideanPlane) (hne : (Ω : Set EuclideanPlane)ᶜ.Nonempty)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (hunit : ∀ x, u x ∈ Icc 0 1) (hw : DeGiorgi.MemW1pWitness 2 u Ω)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ v : EuclideanPlane → ℝ, Continuous v ∧ HasCompactSupport v ∧
      ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ (∀ x, v x ∈ Icc 0 1) ∧
      EqOn v u (Ω : Set EuclideanPlane)ᶜ ∧
      ∃ H : DeGiorgi.MemW1pWitness 2 (fun x => u x - v x) univ,
        ∀ i : Fin 2, eLpNorm (fun x => H.weakGrad x i) 2 volume < ε := by
  obtain ⟨v, hvc, hvs, hvsmooth, hvunit, hvtrace, hvgrad⟩ :=
    exists_exact_trace_smoothing Ω hne hu hs hunit hw hε
  let V := smoothPlaneSobolevWitness Ω.isOpen (hvsmooth.of_le (by simp))
    ((hvc.memLp_of_hasCompactSupport hvs).restrict Ω) (fun i => (hvgrad i).1)
  let D := hw.sub V
  have hz : ∀ x ∉ (Ω : Set EuclideanPlane), u x - v x = 0 := by
    intro x hx
    rw [hvtrace hx, sub_self]
  let H := zeroTraceWitness Ω.isOpen (hu.sub hvc) (hs.sub hvs) hz D
  refine ⟨v, hvc, hvs, hvsmooth, hvunit, hvtrace, H, ?_⟩
  intro i
  change eLpNorm (fun x => (zeroTraceWitness Ω.isOpen (hu.sub hvc) (hs.sub hvs) hz D).weakGrad x i) 2 volume < ε
  rw [zeroTraceWitness_component_eLpNorm]
  have hd : (fun x => D.weakGrad x i) =
      fun x => -(fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i) := by
    funext x
    change hw.weakGrad x i + (-1) * fderiv ℝ v x (EuclideanSpace.single i 1) = _
    ring
  rw [hd]
  change eLpNorm (-(fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i)) 2 (volume.restrict (Ω : Set EuclideanPlane)) < ε
  rw [eLpNorm_neg]
  exact (hvgrad i).2

end CircleDomainRigidity

end

end OAI
