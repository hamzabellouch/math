import OAI.Analysis.CircleDomains.Sobolev.PrincipalScalarWeakLimit
import OAI.Analysis.CircleDomains.Sobolev.SmallGradientNeighborhood
import OAI.Analysis.CircleDomains.Sobolev.ScalarWeakLimitZeroSet

namespace OAI

/-! The zero gradient on a compact source set is preserved by the actual
principal-map limit. This follows from compact containment and localized
smooth energy bounds, without invoking a quasiconformal chain rule. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane
variable {g : PlaneL2} {k R : ℝ} {S : PrincipalSmoothApproximation g k R}

lemma PrincipalMapLimit.inverse_mapsTo_neighborhood (L : PrincipalMapLimit S)
    {F U : Set EuclideanPlane} (hF : IsCompact F) (hU : IsOpen U) (hFU : F ⊆ U) :
    ∀ᶠ n in atTop, MapsTo (physicalHomeomorph (S.map (L.index n)).symm)
      (physicalHomeomorph L.map '' F) U := by
  let A := physicalHomeomorph L.map '' F
  have hA : IsCompact A := hF.image (physicalHomeomorph L.map).continuous
  have hlim : MapsTo (homeomorphMap L.map.symm) (complexPlaneCoordinates '' A)
      (complexPlaneCoordinates.symm ⁻¹' U) := by
    rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    change physicalHomeomorph L.map.symm (physicalHomeomorph L.map x) ∈ U
    rw [← physicalHomeomorph_symm, Homeomorph.symm_apply_apply]
    exact hFU hx
  have he := eventually_mapsTo_of_compact_convergence L.inverse
    (hA.image complexPlaneCoordinates.continuous) (hU.preimage complexPlaneCoordinates.symm.continuous) hlim
  filter_upwards [he] with n hn x hx
  exact hn (mem_image_of_mem complexPlaneCoordinates hx)

lemma PrincipalMapLimit.scalar_energy_zero_set (L : PrincipalMapLimit S)
    (hk : 0 ≤ k) (hk1 : k < 1) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hz : ∀ i, ∀ᵐ x ∂volume, x ∈ F → W.weakGrad x i=0) :
    Tendsto (fun n => ∫ x in physicalHomeomorph L.map '' F,
      physicalSmoothEnergy (principalScalarApproximation L u n) x) atTop (𝓝 0) := by
  let K := (1+k)/(1-k)
  have hK : 0 ≤ K := div_nonneg (by linarith) (by linarith)
  let e (x : EuclideanPlane) := (W.weakGrad x 0)^2+(W.weakGrad x 1)^2
  have hg (i : Fin 2) : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  have hi : Integrable e volume := (hg 0).integrable_sq.add (hg 1).integrable_sq
  have hez : ∀ᵐ x ∂volume, x ∈ F → e x=0 := by
    filter_upwards [hz 0, hz 1] with x h0 h1 hx
    simp only [e, h0 hx, h1 hx, zero_pow two_ne_zero, add_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := ε/(K+1)
  have ht : 0 < t := div_pos hε (by linarith)
  have hKt : K*t < ε := by
    dsimp only [t]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < K+1)).mpr
    nlinarith
  obtain ⟨U, hU, hFU, heU⟩ := exists_open_integral_small_of_zero_on_closed hi hF.isClosed hez ht
  have henergy := planarMollification_energy_tendsto W hs U
  have hen : ∀ᶠ n in atTop, (∫ x in U, physicalSmoothEnergy (planarMollification u n) x) < t :=
    henergy.eventually (gt_mem_nhds heU)
  filter_upwards [L.inverse_mapsTo_neighborhood hF hU hFU, hen] with n hn he
  have hd := (smooth_beltrami_two_sided_distortion (S.map (L.index n))
    (S.smooth _) (S.inverse_smooth _) (S.coefficient _) hk hk1
    (S.coefficient_bound _) (S.equation _)).2
  have hb := physicalSmoothPullback_energy_subset (S.map (L.index n)).symm
    (S.inverse_smooth _) (planarMollification_smooth hu.locallyIntegrable n)
    (planarMollification_hasCompactSupport hs n) hK hd
    (hF.image (physicalHomeomorph L.map).continuous) hn
  have hsmall := (hb.trans (mul_le_mul_of_nonneg_left he.le hK)).trans_lt hKt
  have hnn : 0 ≤ ∫ x in physicalHomeomorph L.map '' F,
      physicalSmoothEnergy (principalScalarApproximation L u n) x :=
    integral_nonneg fun x => physicalSmoothEnergy_nonneg _ x
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn]
  change (∫ x in physicalHomeomorph L.map '' F,
    physicalSmoothEnergy (planarMollification u n ∘ physicalHomeomorph (S.map (L.index n)).symm) x) < ε
  exact hsmall

lemma PrincipalMapLimit.scalar_transport_zero_set (L : PrincipalMapLimit S)
    (hk : 0 ≤ k) (hk1 : k < 1) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hz : ∀ i, ∀ᵐ x ∂volume, x ∈ F → W.weakGrad x i=0) :
    ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph L.map.symm) univ,
      ∀ i, ∀ᵐ x ∂volume, x ∈ physicalHomeomorph L.map '' F → V.weakGrad x i=0 := by
  obtain ⟨T⟩ := L.scalar_weak_limit hk hk1 hu hs W
  exact ⟨T.witness, T.gradient_zero_of_energy
    (fun n i => physicalSmoothPartial_memLp (L.scalar_approximation_smooth hu n)
      (L.scalar_approximation_compact hs n) i)
    (hF.image (physicalHomeomorph L.map).continuous).measurableSet
    (L.scalar_energy_zero_set hk hk1 hu hs W hF hz)⟩

end CircleDomainRigidity

end

end OAI
