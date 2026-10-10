import OAI.Dynamics.EntropyCounterexample.Conjugacy
import OAI.Geometry.SingularHomology.HomologyTransfer

namespace OAI

noncomputable section

namespace Problem340

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def realHomologyEquiv (n : ℕ) (e : X ≃ₜ Y) :
    RealSingularHomology n X ≃ₗ[ℝ] RealSingularHomology n Y :=
  LinearEquiv.ofBijective (realHomologyMap n e e.continuous)
    ⟨realHomologyMap_injective_of_retraction n e e.symm e.continuous
      e.symm.continuous (fun x => e.symm_apply_apply x),
    realHomologyMap_surjective_of_section n e e.symm e.continuous
      e.symm.continuous (fun y => e.apply_symm_apply y)⟩

@[simp] theorem realHomologyEquiv_apply (n : ℕ) (e : X ≃ₜ Y)
    (v : RealSingularHomology n X) :
    realHomologyEquiv n e v = realHomologyMap n e e.continuous v := rfl

theorem realHomologyMap_conjugateMap_intertwines (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) :
    (realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf)).comp
        (realHomologyMap n e e.continuous) =
      (realHomologyMap n e e.continuous).comp (realHomologyMap n f hf) := by
  rw [← realHomologyMap_comp, ← realHomologyMap_comp]
  congr 1
  funext x
  simp

theorem realHomologyEquiv_conjugateMap (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) (v : RealSingularHomology n X) :
    realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf)
        (realHomologyEquiv n e v) =
      realHomologyEquiv n e (realHomologyMap n f hf v) := by
  exact congrArg (fun A : RealSingularHomology n X →ₗ[ℝ] RealSingularHomology n Y => A v)
    (realHomologyMap_conjugateMap_intertwines n e hf)

theorem realHomologyMap_eigenvector_conjugateMap (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) (c : ℝ)
    (v : RealSingularHomology n X) (hv : v ≠ 0)
    (heig : realHomologyMap n f hf v = c • v) :
    ∃ w : RealSingularHomology n Y, w ≠ 0 ∧
      realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf) w = c • w := by
  refine ⟨realHomologyEquiv n e v, ?_, ?_⟩
  · exact (map_ne_zero_iff (realHomologyEquiv n e) (realHomologyEquiv n e).injective).2 hv
  · rw [realHomologyEquiv_conjugateMap n e hf, heig, map_smul]

theorem realHomologyMap_complexPair_conjugateMap (n : ℕ) (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) (a b : ℝ)
    (u v : RealSingularHomology n X) (huv : u ≠ 0 ∨ v ≠ 0)
    (hu : realHomologyMap n f hf u = a • u - b • v)
    (hv : realHomologyMap n f hf v = b • u + a • v) :
    ∃ u' v' : RealSingularHomology n Y,
      (u' ≠ 0 ∨ v' ≠ 0) ∧
      realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf) u' =
        a • u' - b • v' ∧
      realHomologyMap n (conjugateMap e f) (continuous_conjugateMap e hf) v' =
        b • u' + a • v' := by
  refine ⟨realHomologyEquiv n e u, realHomologyEquiv n e v, ?_, ?_, ?_⟩
  · simpa only [map_ne_zero_iff (realHomologyEquiv n e)
      (realHomologyEquiv n e).injective] using huv
  · rw [realHomologyEquiv_conjugateMap n e hf, hu, map_sub, map_smul, map_smul]
  · rw [realHomologyEquiv_conjugateMap n e hf, hv, map_add, map_smul, map_smul]

theorem totalRealHomologySpectralRadius_conjugateMap (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) :
    totalRealHomologySpectralRadius (conjugateMap e f) (continuous_conjugateMap e hf) =
      totalRealHomologySpectralRadius f hf := by
  unfold totalRealHomologySpectralRadius
  congr 1
  ext r
  constructor
  · rintro ⟨n, a, b, u, v, huv, hu, hv, hr⟩
    obtain ⟨u', v', huv', hu', hv'⟩ := realHomologyMap_complexPair_conjugateMap
      n e.symm (continuous_conjugateMap e hf) a b u v huv hu hv
    exact ⟨n, a, b, u', v', huv', by simpa using hu', by simpa using hv', hr⟩
  · rintro ⟨n, a, b, u, v, huv, hu, hv, hr⟩
    obtain ⟨u', v', huv', hu', hv'⟩ := realHomologyMap_complexPair_conjugateMap
      n e hf a b u v huv hu hv
    exact ⟨n, a, b, u', v', huv', hu', hv', hr⟩

end Problem340

end

end OAI
