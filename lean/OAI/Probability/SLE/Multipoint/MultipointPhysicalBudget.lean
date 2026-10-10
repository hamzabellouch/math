import OAI.Probability.SLE.Multipoint.MultipointPhysicalGeometry
import OAI.Probability.SLE.Multipoint.MultipointLoewnerDrop

namespace OAI

/-! The actual physical-domain interaction budget. This statement uses
capacity-two time throughout: the radius clocks satisfy `R = b exp(-4u)`,
and the Green derivative has coefficient four. No bound on the derivative
of the original conformal map is assumed. -/

noncomputable section
open Set Metric Filter MeasureTheory Complex
open scoped Topology NNReal ComplexConjugate

namespace SLEExactGauge

/-- A conformal-radius upper bound suffices for geometric interaction
decay; the physical clock need not be specified by equality. -/
theorem IsCapacityTwoWitness.physical_interaction_decay_of_radius_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane)
    (t : ℝ≥0) (z w : ℂ) (hz : z ∈ survivingDomain γ t)
    (hw' : w ∈ survivingDomain γ t) (hne : z ≠ w)
    (b a u : ℝ) (hb : b ≤ dist (J z) (J w))
    (hR : physicalConformalRadius J G t z ≤ b * Real.exp (-2 * a * u)) :
    halfPlaneGreen (G t z) (G t w) ≤ Real.exp (-a * u) := by
  let b' := physicalConformalRadius J G t z / Real.exp (-2 * a * u)
  have hb' : b' ≤ dist (J z) (J w) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    exact hR.trans (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le)
  apply hw.physical_interaction_decay hgrowth J hJ hJinj t z w hz hw' hne b' a u hb'
  exact (div_mul_cancel₀ _ (Real.exp_ne_zero _)).symm

lemma halfPlaneGreen_symm (z w : ℂ) : halfPlaneGreen z w = halfPlaneGreen w z := by
  have hn : ‖z - conj w‖ = ‖w - conj z‖ := by
    calc
      _ = ‖conj (z - conj w)‖ := (Complex.norm_conj _).symm
      _ = ‖-(w - conj z)‖ := by
        congr 1
        simp only [map_sub, Complex.conj_conj]
        ring
      _ = _ := norm_neg _
  unfold halfPlaneGreen
  rw [norm_div, norm_div, hn, norm_sub_rev z w]

/-- Both radius caps yield the decay in the maximum of the two clocks;
the proved Green drop then pays for every weighted interaction shell. -/
theorem IsCapacityTwoWitness.physical_pair_interaction_budget
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane)
    (s T : ℝ≥0) (hsT : s ≤ T) (z w : ℂ)
    (hz : z ∈ survivingDomain γ T) (hw' : w ∈ survivingDomain γ T) (hne : z ≠ w)
    (bz bw : ℝ) (hbz : bz ≤ dist (J z) (J w)) (hbw : bw ≤ dist (J z) (J w))
    {c : ℝ} (hc : 0 ≤ c) (hca : 2 * c < 2) (u v : ℝ → ℝ)
    (hu : ContinuousOn u (Icc (s : ℝ) (T : ℝ)))
    (hv : ContinuousOn v (Icc (s : ℝ) (T : ℝ)))
    (hu0 : ∀ t ∈ Icc (s : ℝ) (T : ℝ), 0 ≤ u t)
    (hv0 : ∀ t ∈ Icc (s : ℝ) (T : ℝ), 0 ≤ v t)
    (hRu : ∀ t ∈ Icc (s : ℝ) (T : ℝ),
      physicalConformalRadius J G t.toNNReal z ≤ bz * Real.exp (-4 * u t))
    (hRv : ∀ t ∈ Icc (s : ℝ) (T : ℝ),
      physicalConformalRadius J G t.toNNReal w ≤ bw * Real.exp (-4 * v t)) :
    (∫ t in (s : ℝ)..(T : ℝ), Real.exp (c * (u t + v t)) *
      (chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w)) ≤
        Multipoint.interactionBudget 2 c := by
  have hdecay : ∀ t ∈ Icc (s : ℝ) (T : ℝ),
      halfPlaneGreen (G t.toNNReal z) (G t.toNNReal w) ≤
        Real.exp (-2 * max (u t) (v t)) := by
    intro t ht
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have hzt := survivingDomain_antitone γ htT hz
    have hwt := survivingDomain_antitone γ htT hw'
    have hdz := hw.physical_interaction_decay_of_radius_le hgrowth J hJ hJinj t.toNNReal z w
      hzt hwt hne bz 2 (u t) hbz (by
        simpa only [show (-2 : ℝ) * 2 = -4 by norm_num] using hRu t ht)
    have hdw := hw.physical_interaction_decay_of_radius_le hgrowth J hJ hJinj t.toNNReal w z
      hwt hzt hne.symm bw 2 (v t) (by simpa only [dist_comm] using hbw) (by
        simpa only [show (-2 : ℝ) * 2 = -4 by norm_num] using hRv t ht)
    rw [halfPlaneGreen_symm (G t.toNNReal w) (G t.toNNReal z)] at hdw
    exact Multipoint.interaction_decay_max hdz hdw
  simpa only [one_mul] using hw.weighted_interaction_integral_le hU s T hsT z w hz hw' hne
    (M := 1) zero_le_one hc hca u v hu hv hu0 hv0
    (by simpa only [one_mul] using hdecay)

end SLEExactGauge

end

end OAI
