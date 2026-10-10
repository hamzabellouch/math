import OAI.MeasureTheory.Falconer.Radial.LatePlateFiber
import OAI.MeasureTheory.Falconer.Measures.ExceptionalFiberMass

namespace OAI

/-! # Initial and later product-mass losses for finite plate covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem initial_plate_fiber_bound (ν ρ : Measure (Space d))
    (S : Finset (Space d × ℝ)) (G : Set (Space d × Space d))
    {R τ M : ℝ} {η : ℝ≥0∞} (hν : ν ≤ ρ)
    (hbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M)
    (hsmall : ∀ p ∈ S, ρ {y | |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*R} ≤ η)
    (hcover : G ⊆ ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ R})
    (x : Space d) (hx : ‖x‖ ≤ M) (hgood : x ∉ slabPairException S R τ) :
    ν {y | (x,y) ∈ G} ≤ η := by
  classical
  let F := {y | (x,y) ∈ G}
  by_cases hF : F.Nonempty
  · obtain ⟨y₀,hy₀⟩ := hF
    obtain ⟨p,hp,hxp,_⟩ := mem_iUnion₂.mp (hcover hy₀)
    have hfiber : ∀ᵐ y ∂ν, y ∈ F → |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*R := by
      filter_upwards [hbounded] with y hy hGy
      obtain ⟨q,hq,hxq,hyq⟩ := mem_iUnion₂.mp (hcover hGy)
      exact cluster_outside_slabPairException S hx hgood hp hxp q hq hxq y hy hyq
    exact (measure_mono_ae hfiber).trans ((hν _).trans (hsmall p hp))
  · change ν F ≤ _
    rw [not_nonempty_iff_eq_empty.mp hF,measure_empty]
    exact bot_le

theorem late_plate_pair_mass (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (j j' : ℕ) (S : Finset (Space d × ℝ))
    (G : Set (Space d × Space d)) (hGm : MeasurableSet G)
    {r m r' m' R τ M s C : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hwidth : 2*M*τ+3*R ≤ r') (hsmall : 10*R/τ ≤ 1)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hG : G ⊆ heavyPlateCellPairs ρ Q j r m \ heavyPlateCellPairs ρ Q j' r' m')
    (hcover : heavyPlateCellPairs ρ Q j r m ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ {y | |inner ℝ p.1 y-p.2| ≤ R}) :
    (μ.prod ν) G ≤ (S.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*R/τ)^(s-((d-2:ℕ):ℝ))) + ENNReal.ofReal m' := by
  apply (product_mass_of_exceptional_fibers μ ν G hGm (slabPairException S R τ) (B := ENNReal.ofReal m')
    (measurableSet_slabPairException S R τ) ?_).trans
    (add_le_add (slabPairException_mass μ S hM hC hμbounded hfrost
      hunit hτ hτ1 hR hsmall) le_rfl)
  filter_upwards [hμbounded] with x hx hgood
  exact late_plate_fiber_bound ν ρ Q j j' S G hM hR.le hτ.le hwidth hν hνbounded
    hunit hG hcover x hx hgood

theorem initial_plate_pair_mass (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Finset (Space d × ℝ)) (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    {R τ M s C : ℝ} {η : ℝ≥0∞}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hsmall : 10*R/τ ≤ 1) (hν : ν ≤ ρ)
    (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C) (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hslab : ∀ p ∈ S, ρ {y | |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*R} ≤ η)
    (hcover : G ⊆ ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ R}) :
    (μ.prod ν) G ≤ (S.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*R/τ)^(s-((d-2:ℕ):ℝ))) + η := by
  apply (product_mass_of_exceptional_fibers μ ν G hG (slabPairException S R τ) (B := η)
    (measurableSet_slabPairException S R τ) ?_).trans
    (add_le_add (slabPairException_mass μ S hM hC hμbounded hfrost
      hunit hτ hτ1 hR hsmall) le_rfl)
  filter_upwards [hμbounded] with x hx hgood
  exact initial_plate_fiber_bound ν ρ S G hν hνbounded hslab hcover x hx hgood

end Falconer

end OAI
