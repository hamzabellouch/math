import OAI.Analysis.CircleDomains.Probability.HorizontalNullPair
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevNullLevels

namespace OAI

/-! The horizontal trace-pair lemma is local in the Sobolev coordinate.
A compact plateau reduces it to the global trace-pair statement. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_horizontal_pair_null_image
    (hcoarea : PlanarSobolevCoarea)
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hKΩ : complexPlaneCoordinates ⁻¹' F ⊆ Ω)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U Ω)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), W.weakGrad p = 0) :
    volume ((fun z => (U (complexPlaneCoordinates.symm z), z.re)) '' F) = 0 := by
  let K := complexPlaneCoordinates ⁻¹' F
  have hK : IsCompact K := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hF
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hsub
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hΩ W.memW1p hη hsη hsub
  have hg (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVΩ W Ww hone i)
  have hzero : ∀ᵐ p ∂volume.restrict K, Ww.weakGrad p = 0 := by
    filter_upwards [hz, hg 0, hg 1] with p hp hp0 hp1
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    fin_cases i <;> simp_all
  have hh := sobolev_horizontal_pair_null_image hcoarea hF hQ hFQ
    (hη.continuous.mul hU) Ww hzero
  apply measure_mono_null (t := (fun z =>
    (η (complexPlaneCoordinates.symm z)*U (complexPlaneCoordinates.symm z), z.re)) '' F) ?_ hh
  rintro _ ⟨z, hzF, rfl⟩
  refine ⟨z, hzF, ?_⟩
  have hzK : complexPlaneCoordinates.symm z ∈ K := by
    change complexPlaneCoordinates (complexPlaneCoordinates.symm z) ∈ F
    rwa [complexPlaneCoordinates.apply_symm_apply]
  simp only [hone _ (hKV hzK), one_mul]

end CircleDomainRigidity

end

end OAI
