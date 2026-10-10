import OAI.Analysis.CircleDomains.Modulus.CompactBarrierProjection
import OAI.Analysis.CircleDomains.Topology.AnchoredCurveImages
import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals

namespace OAI

/-! Concrete compact global barriers surrounding a fixed compact set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

structure CompactBarrierData (K : Set EuclideanPlane) (L η : ℝ) where
  region : Set EuclideanPlane
  open_region : IsOpen region
  compact_closure : IsCompact (closure region)
  contains : K ⊆ closure region
  value : EuclideanPlane → ℝ
  witness : DeGiorgi.MemW1pWitness 2 value univ
  continuous : Continuous value
  support : tsupport value ⊆ ball 0 L
  one : ∀ x ∈ frontier region, value x = 1
  energy : (∫ x, ‖witness.weakGrad x‖^2) < η^2

 theorem compact_barrier_data_subsingleton
    {K : Set EuclideanPlane} (hK : IsCompact K) (hc : IsConnected K)
    {L : ℝ} (hL : 0 < L)
    (D : ∀ s : ℕ, CompactBarrierData K L (1/((s:ℝ)+1))) : K.Subsingleton := by
  have hE : Tendsto (fun s => ∫ x, ‖(D s).witness.weakGrad x‖^2) atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    simp only [zero_pow (by decide : 2 ≠ 0)] at ht
    exact squeeze_zero (fun s => integral_nonneg (fun x => sq_nonneg _))
      (fun s => (D s).energy.le) ht
  apply physical_subsingleton_of_zero_projection_measure hK hc
  intro i
  exact projection_measure_zero_of_compact_barriers hK
    (fun s => (D s).open_region) (fun s => (D s).compact_closure)
    (fun s => (D s).witness) (fun s => (D s).continuous) hL
    (fun s => (D s).support) hE
    (Eventually.of_forall (fun s => ⟨(D s).contains,(D s).one⟩)) i

 theorem exists_compact_barrier_of_curve_images
    {K : Set ℂ} (hK : IsCompact K) (J : ℂ ≃ₜ ℂ) (Jn : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior J))
    (hfrontn : ∀ n, range (γn n) = frontier (jordanInterior (Jn n)))
    (hlim : TendstoUniformly γn γ atTop)
    {q : ℂ} {qn : ℕ → ℂ} (hq : q ∈ jordanInterior J)
    (hqlim : Tendsto qn atTop (𝓝 q)) (hqn : ∀ n, qn n ∈ jordanInterior (Jn n))
    (hKJ : K ⊆ jordanInterior J) {L η : ℝ}
    (hbarrier : ∀ᶠ n in atTop,
      ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
        Continuous v ∧ tsupport v ⊆ ball 0 L ∧
        (∀ t, v (complexPlaneCoordinates.symm (γn n t)) = 1) ∧
        (∫ x, ‖W.weakGrad x‖^2) < η^2) :
    Nonempty (CompactBarrierData (complexPlaneCoordinates.symm '' K) L η) := by
  have hret := eventually_compact_subset_jordanInterior_of_anchor J Jn γ γn hγ hfront
    (Eventually.of_forall hfrontn) hlim hq hqlim (Eventually.of_forall hqn) hK hKJ
  obtain ⟨n,hn,hb⟩ := (hret.and hbarrier).exists
  obtain ⟨v,W,hv,hs,hone,hE⟩ := hb
  let U := complexPlaneCoordinates ⁻¹' jordanInterior (Jn n)
  have hUc : IsCompact (closure U) := by
    have he : closure U = complexPlaneCoordinates.symm '' closure (jordanInterior (Jn n)) := by
      calc
        closure U = complexPlaneCoordinates ⁻¹' closure (jordanInterior (Jn n)) :=
          (complexPlaneCoordinates.toHomeomorph.preimage_closure _).symm
        _ = _ := by
          ext x
          constructor
          · intro hx
            exact ⟨complexPlaneCoordinates x,hx,complexPlaneCoordinates.symm_apply_apply x⟩
          · rintro ⟨z,hz,rfl⟩
            simpa only [mem_preimage,complexPlaneCoordinates.apply_symm_apply] using hz
    rw [he]
    exact (isCompact_closure_jordanInterior (Jn n)).image complexPlaneCoordinates.symm.continuous
  refine ⟨⟨U,(jordanInterior_isOpen _).preimage complexPlaneCoordinates.continuous,hUc,
    ?_,v,W,hv,hs,?_,hE⟩⟩
  · rintro x ⟨z,hz,rfl⟩
    apply subset_closure
    change complexPlaneCoordinates (complexPlaneCoordinates.symm z) ∈ jordanInterior (Jn n)
    rw [complexPlaneCoordinates.apply_symm_apply]
    exact hn hz
  · intro x hx
    have hx' : complexPlaneCoordinates x ∈ frontier (jordanInterior (Jn n)) := by
      change x ∈ complexPlaneCoordinates ⁻¹' frontier (jordanInterior (Jn n))
      have he : complexPlaneCoordinates ⁻¹' frontier (jordanInterior (Jn n)) = frontier U :=
        complexPlaneCoordinates.toHomeomorph.preimage_frontier _
      rwa [he]
    obtain ⟨t,ht⟩ := (hfrontn n).symm ▸ hx'
    have h := hone t
    rwa [ht,complexPlaneCoordinates.symm_apply_apply] at h

end CircleDomainRigidity

end

end OAI
