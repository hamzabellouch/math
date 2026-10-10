import OAI.Geometry.RCD.Heat.CompactHeatOsmoticVanishing
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # A uniform local gradient bound for any osmotic representative

Locality makes this bound apply to the actual representatives used in
second variation, independent of the chosen compact extension.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem osmotic_local_gradient (hε1 : ∀ k, ε k≤1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0≤ρ₀ x) (hp₁ : ∀ x, 0≤ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x|≤C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x|≤C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R r δ : ℝ} (hR : 0≤R)
    (hS : ∀ a:S, dist z a≤R) (hT : ∀ b:T, dist z b≤R) (hδ : 0<δ) :
    ∃ H : ℝ, 0≤H ∧ ∀ k (t : InteriorHeatTime δ)
      (η : SobolevSpace (hausdorff n X) hX.quadratic) {Ω : Set X}, Ω⊆closedBall z r →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η
        =ᵐ[(hausdorff n X).restrict Ω] D.osmoticPotential k t.val) →
      ∀ᵐ x ∂(hausdorff n X).restrict Ω,
        localGamma (hausdorff n X) hX.quadratic η η x≤H := by
  let m := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨H₀,hH₀,hleft⟩ := hX.compact_scaled_log_uniform_bound hn p μ ρ₀ hm₀ hp₀ hC₀ hμ
    z hR hS hδ (r := r)
  obtain ⟨H₁,hH₁,hright⟩ := hX.compact_scaled_log_uniform_bound hn p ν ρ₁ hm₁ hp₁ hC₁ hν
    z hR hT hδ (r := r)
  let H := max H₀ H₁
  have hH : 0≤H := hH₀.trans (le_max_left _ _)
  refine ⟨H,hH,?_⟩
  intro k t η Ω hΩ hη
  let c := ε k/4
  have hc : 0<c := div_pos (hε k) (by norm_num)
  have hc2 : 2*c≤1 := by dsimp only [c]; linarith [hε1 k]
  obtain ⟨P,hP,hPg⟩ := hleft (D.left k) (D.left_pos k) hc hc2 t.property.1 t.val.property.2.le
  obtain ⟨V,hV,hVg⟩ := hright (D.right k) (D.right_pos k) hc hc2 t.property.2
    (by linarith [t.val.property.1])
  have hPg' := hPg.mono fun _ hx => hx.trans (le_max_left H₀ H₁)
  have hVg' := hVg.mono fun _ hx => hx.trans (le_max_right H₀ H₁)
  obtain ⟨U,W,hU,hW,-,hg⟩ := scaled_log_pair_bounds m Q _ _ P V hc hH hP hV hPg' hVg'
  have hrep : SobolevSpace.toLp m Q (c • (U+W)) =ᵐ[m.restrict (closedBall z r)]
      D.osmoticPotential k t.val := by
    filter_upwards [hU,hW,ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp m Q U)
      (SobolevSpace.toLp m Q W)),ae_restrict_of_ae
      (Lp.coeFn_smul c (SobolevSpace.toLp m Q (U+W)))] with x hu hw ha hs
    change SobolevSpace.toLp m Q (c • (U+W)) x=c*SobolevSpace.toLp m Q (U+W) x at hs
    simp only [Pi.add_apply] at ha
    rw [hs]
    simp only [map_add]
    rw [ha,hu,hw]
    dsimp only [osmoticPotential,interpolationDensity]
    rw [Real.log_mul
      (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x).ne'
      (hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x).ne']
  have heq : SobolevSpace.toLp m Q η =ᵐ[m.restrict Ω]
      SobolevSpace.toLp m Q (c • (U+W)) := by
    filter_upwards [hη,ae_restrict_of_ae_restrict_of_subset hΩ hrep] with x hx hy
    exact hx.trans hy.symm
  have hgamma := localGamma_pair_congr_ae m Q heq heq
  filter_upwards [hgamma,ae_restrict_of_ae_restrict_of_subset hΩ hg,
    ae_restrict_of_ae (localGamma_self m Q (c • (U+W))),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr
      (SobolevSpace.minimalSlope_nonneg m Q (c • (U+W))))]
    with x hsame hbound hsq hnonneg
  rw [hsame,hsq]
  change 0≤SobolevSpace.minimalSlope m Q (c • (U+W)) x at hnonneg
  exact (pow_le_pow_left₀ hnonneg hbound 2).trans_eq (Real.sq_sqrt hH)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
