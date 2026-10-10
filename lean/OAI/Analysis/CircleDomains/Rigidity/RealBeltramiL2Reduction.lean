import OAI.Analysis.CircleDomains.Rigidity.ConjugateBeltramiL2
import OAI.Analysis.CircleDomains.Rigidity.RealBeltramiCoefficientReduction

namespace OAI

/-! A measurable standard coefficient built from the actual conductivity
L2 density. The zero-derivative set requires no division hypothesis. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : MemLp q 2 volume) (k : ℝ≥0) (hk : k < 1)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ),
      AEStronglyMeasurable μ volume ∧
      (∀ᵐ x ∂volume, ‖μ x‖ ≤ k) ∧
      (∀ x, q x = 0 → μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) ∧
      ‖h‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) := by
  obtain ⟨h, heq, hn⟩ := exists_actual_conductivity_density q hq k hk hb
  let μ : EuclideanPlane → ℂ := fun x =>
    realBeltramiStandardCoefficient (q x) (1 + physicalBeurling h x)
  refine ⟨h, μ, realBeltramiStandardCoefficient_aeStronglyMeasurable q _
    hq.aestronglyMeasurable
    (aestronglyMeasurable_const.add (Lp.aestronglyMeasurable _)), ?_, ?_, heq, ?_, hn⟩
  · filter_upwards [hb] with x hx
    exact (realBeltramiStandardCoefficient_norm_le _ _).trans hx
  · intro x hx
    simp only [μ, hx, realBeltramiStandardCoefficient_zero]
  · filter_upwards [heq] with x hx
    exact hx.trans (realBeltramiStandardCoefficient_mul _ _).symm

lemma real_beltrami_memLp_of_compact_support (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) : MemLp q 2 volume := by
  have hm : MemLp (K.indicator (fun _ : EuclideanPlane => (k : ℝ))) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  apply hm.of_le hq
  filter_upwards [hb] with x hx
  by_cases hxK : x ∈ K
  · simpa only [indicator_of_mem hxK, Real.norm_eq_abs] using
      hx.trans (le_abs_self (k : ℝ))
  · simp only [hzero x hxK, norm_zero, indicator_of_notMem hxK, le_refl]

lemma exists_compact_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ),
      AEStronglyMeasurable μ volume ∧ (∀ᵐ x ∂volume, ‖μ x‖ ≤ k) ∧
      (∀ x ∉ K, μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) := by
  obtain ⟨h, μ, hm, hbμ, hzμ, hqeq, hμeq, _⟩ := exists_real_beltrami_l2_reduction q
    (real_beltrami_memLp_of_compact_support q hq hK hzero k hb) k hk hb
  exact ⟨h, μ, hm, hbμ, fun x hx => hzμ x (hzero x hx), hqeq, hμeq⟩

lemma exists_bounded_compact_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ), Measurable μ ∧
      (∀ x, ‖μ x‖ ≤ k) ∧ (∀ x ∉ K, μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) := by
  obtain ⟨h, μ, hm, hbm, hzm, hqeq, hmeq⟩ :=
    exists_compact_real_beltrami_l2_reduction q hq hK hzero k hk hb
  obtain ⟨ν, hνm, hνb, hνz, heq⟩ :=
    exists_compact_coefficient_representative μ hm hK hzm k hbm
  refine ⟨h, ν, hνm, hνb, hνz, hqeq, ?_⟩
  filter_upwards [hmeq, heq] with x hx he
  rwa [he] at hx

lemma exists_complex_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (g : CannonBeltrami.PlaneL2) (μ : ℂ → ℂ), Measurable μ ∧
      (∀ z, ‖μ z‖ ≤ k) ∧
      (∀ z ∉ complexPlaneCoordinates '' K, μ z = 0) ∧
      (∀ᵐ z ∂volume,
        g z = (q (complexPlaneCoordinates.symm z) : ℂ) *
          star (1+CannonBeltrami.beurling g z)) ∧
      (∀ᵐ z ∂volume, g z = μ z*(1+CannonBeltrami.beurling g z)) := by
  obtain ⟨h, ν, hνm, hνb, hνz, hqe, hνe⟩ :=
    exists_bounded_compact_real_beltrami_l2_reduction q hq hK hzero k hk hb
  let g := physicalLpToComplex h
  let μ : ℂ → ℂ := ν ∘ complexPlaneCoordinates.symm
  have hmp := complexPlaneCoordinates_measurePreserving.symm
    complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv
  refine ⟨g, μ, hνm.comp complexPlaneCoordinates.symm.continuous.measurable,
    fun z => hνb _, ?_, ?_, ?_⟩
  · intro z hz
    exact hνz _ (fun h => hz ⟨_, h, complexPlaneCoordinates.apply_symm_apply z⟩)
  · filter_upwards [hmp.quasiMeasurePreserving.ae hqe, physicalLpToComplex_coe h,
      physicalBeurling_complex_coe h] with z hqz hgz hBz
    change physicalLpToComplex h z = _
    rw [hgz, hBz]
    exact hqz
  · filter_upwards [hmp.quasiMeasurePreserving.ae hνe, physicalLpToComplex_coe h,
      physicalBeurling_complex_coe h] with z hνz hgz hBz
    change physicalLpToComplex h z = _
    rw [hgz, hBz]
    exact hνz

end CircleDomainRigidity

end

end OAI
