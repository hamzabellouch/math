import OAI.Analysis.CircleDomains.Sobolev.SobolevClassicalPartials
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! Localizing the actual coordinate derivative theorem by a smooth
compact cutoff equal to one near the chosen compact core. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_core_sobolev_coordinate_derivative
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u Ω) (i : Fin 2) :
    ∃ V : Set EuclideanPlane, IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∀ᵐ y ∂volume, ∀ᵐ t ∂volume, physicalCoordinateLine i y t ∈ V →
        HasDerivAt (fun s => u (physicalCoordinateLine i y s))
          (W.weakGrad (physicalCoordinateLine i y t) i) t := by
  obtain ⟨η, V, hη, hsη, _, hηΩ, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hηΩ
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hΩ W.memW1p hη hsη hηΩ
  have heq : EqOn w u V := fun p hp => by dsimp only [w]; rw [hone p hp, one_mul]
  have hg : ∀ᵐ p ∂volume, p ∈ V → Ww.weakGrad p i = W.weakGrad p i :=
    (ae_restrict_iff' hV.measurableSet).mp (weakGrad_eq_on_cutoff_plateau hV hVΩ W Ww hone i)
  refine ⟨V, hV, hKV, hVΩ, ?_⟩
  filter_upwards [sobolev_coordinate_ae_hasDerivAt (hη.continuous.mul hu) hsη.mul_right Ww i,
    ae_ae_physicalCoordinateLine hg i] with y hy hgy
  filter_upwards [hy, hgy] with t ht hgt
  intro htV
  rw [hgt htV] at ht
  apply ht.congr_of_eventuallyEq
  have hn : ∀ᶠ s in 𝓝 t, physicalCoordinateLine i y s ∈ V :=
    (physicalCoordinateLine_contDiff i y).continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds htV)
  filter_upwards [hn] with s hs
  exact (heq hs).symm

end CircleDomainRigidity

end

end OAI
