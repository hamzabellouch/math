import OAI.Analysis.CircleDomains.Rigidity.PrincipalScalarSolver
import OAI.Analysis.CircleDomains.Selection.PrincipalScalarZeroSet
import OAI.Analysis.CircleDomains.Rigidity.PrincipalRealBeltramiProof

namespace OAI

/-! The internal conductivity/scalar interface is constructed from the
actual principal smooth approximation. No quasiconformal Sobolev calculus
is assumed. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_principal_real_with_scalar_pullback
    (q : EuclideanPlane → ℝ) (hq : AEStronglyMeasurable q volume)
    {F : Set EuclideanPlane} (hF : IsCompact F) (hFzero : ∀ x ∉ F, q x=0)
    (k : ℝ≥0) (hk : k<1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      (∀ᵐ x ∂volume,
        planarDbar (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1) =
        q x • star (planarDz (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1))) ∧
      CompactScalarPullback φ := by
  obtain ⟨g, μ, hm, hbound, hzero, hreal, he⟩ :=
    exists_complex_real_beltrami_l2_reduction q hq hF hFzero k hk hb
  obtain ⟨R, hR⟩ := (hF.image complexPlaneCoordinates.continuous).isBounded.subset_ball 0
  have hs : ∀ z, R ≤ ‖z‖ → μ z=0 := by
    intro z hz
    apply hzero
    intro hzF
    have hh := hR hzF
    simp only [Metric.mem_ball, dist_zero_right] at hh
    linarith
  have hk0 : 0 ≤ (k : ℝ) := k.2
  have hk1 : (k : ℝ) < 1 := by exact_mod_cast hk
  obtain ⟨S⟩ := exists_principal_smooth_approximation μ hm.aestronglyMeasurable
    hk0 hk1 hbound hs g he
  let T := max (R+2) 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨L⟩ := S.exists_principal_limit_data
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk0 hk1 hT (le_max_left _ _)
  refine ⟨L.map, principalPhysicalWitness L.map g L.weak, L.principal,
    principalPhysicalWitness_equation L.map g L.weak q hreal, ?_⟩
  intro u hu hsupport W A hA hz
  exact L.scalar_transport_zero_set hk0 hk1 hu hsupport W hA hz

lemma principalConductivityScalarSolver : PrincipalConductivityScalarSolver := by
  intro F hF n hn
  obtain ⟨φ, D, ht, he, hscalar⟩ := exists_principal_real_with_scalar_pullback
    (conductivityCoefficient F n) (conductivityCoefficient_memLp hF n).aestronglyMeasurable
    hF (fun x hx => indicator_of_notMem hx _)
    (conductivityRatio n hn) (conductivityRatio_lt_one n hn)
    (.of_forall (conductivityCoefficient_bound F n hn))
  refine ⟨φ, D, ht, ?_, hscalar⟩
  filter_upwards [he] with x hx
  have hk : 0 ≤ conductivityValue F n x := by
    classical
    unfold conductivityValue
    split <;> positivity
  apply (conductivity_system_iff hk).mp
  rwa [conductivityCoefficient_ratio] at hx

end CircleDomainRigidity

end

end OAI
