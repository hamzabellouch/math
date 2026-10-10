import OAI.MeasureTheory.Falconer.Radial.UniformRadialRestrictions
import OAI.MeasureTheory.Falconer.Radial.RadialLpEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem source_uniform_radial_restrictions (μ₀ ν₀ : ProbabilityMeasure Plane)
    (hμK : IsCompact (μ₀ : Measure Plane).support)
    (hνK : IsCompact (ν₀ : Measure Plane).support)
    (hsep : Disjoint (μ₀ : Measure Plane).support (ν₀ : Measure Plane).support)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 < C)
    (hμball : BallBound μ₀ (1+δ) C) (hνball : BallBound ν₀ (1+δ) C) :
    ∃ μ ν : ProbabilityMeasure Plane,
      IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
      (μ : Measure Plane).support ⊆ (μ₀ : Measure Plane).support ∧
      (ν : Measure Plane).support ⊆ (ν₀ : Measure Plane).support ∧
      ∃ D : ℝ, 0 < D ∧ BallBound μ (1+δ) D ∧ BallBound ν (1+δ) D ∧
      ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  obtain ⟨hs1, hs2, hp1, hp2, ht0, hupt, htp, hsδ, htδ⟩ := radial_parameters hδ hδ1
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have hIμ := finite_radial_Lp_integral (ν₀ : Measure Plane) μ₀ hνK hμK hsep.symm
    (ν₀ : Measure Plane).support_mem_ae (μ₀ : Measure Plane).support_mem_ae
    hpq hp2 hs1 hs2 (by simpa [mul_comm] using hupt) htp
    (rieszEnergy_lt_top_of_ball_bound ν₀ (zero_lt_one.trans hs1) hsδ hνball)
    (rieszEnergy_lt_top_of_ball_bound μ₀ ht0 htδ hμball)
  have hIν := finite_radial_Lp_integral (μ₀ : Measure Plane) ν₀ hμK hνK hsep
    (μ₀ : Measure Plane).support_mem_ae (ν₀ : Measure Plane).support_mem_ae
    hpq hp2 hs1 hs2 (by simpa [mul_comm] using hupt) htp
    (rieszEnergy_lt_top_of_ball_bound μ₀ (zero_lt_one.trans hs1) hsδ hμball)
    (rieszEnergy_lt_top_of_ball_bound ν₀ ht0 htδ hνball)
  exact uniform_restrictions_of_finite_radial_moments μ₀ ν₀ hμK hνK
    (add_pos zero_lt_one hδ) hC hμball hνball hpq hIμ hIν

theorem exists_uniform_radial_frostman_pair (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ μ ν : ProbabilityMeasure Plane,
      IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
      (μ : Measure Plane).support ⊆ E ∧ (ν : Measure Plane).support ⊆ E ∧
      ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ BallBound μ (1+δ) C ∧ BallBound ν (1+δ) C ∧
      (∀ x ∈ (μ : Measure Plane).support, ∀ y ∈ (ν : Measure Plane).support,
        d/2 ≤ dist x y ∧ dist x y ≤ 2*d) ∧
      ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  obtain ⟨δ, hδ, hδ1, μ₀, ν₀, hμK, hνK, hμE, hνE, C, d, hC, hd, hbμ, hbν, hdist, _⟩ :=
    exists_separated_frostman_pair E hE hd
  have hsep : Disjoint (μ₀ : Measure Plane).support (ν₀ : Measure Plane).support := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h := (hdist x hx x hy).1
    rw [dist_self] at h
    exact (not_le_of_gt (half_pos hd)) h
  obtain ⟨μ, ν, hμ, hν, hμsub, hνsub, D, hD, hbμ', hbν', K, hK, huμ, huν⟩ :=
    source_uniform_radial_restrictions μ₀ ν₀ hμK hνK hsep hδ hδ1 hC hbμ hbν
  exact ⟨δ, hδ, hδ1, μ, ν, hμ, hν, hμsub.trans hμE, hνsub.trans hνE,
    D, d, hD, hd, hbμ', hbν', fun x hx y hy => hdist x (hμsub hx) y (hνsub hy),
    K, hK, huμ, huν⟩

end PlanarFalconer

end OAI
