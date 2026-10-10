import OAI.MeasureTheory.Falconer.Radial.OriginalHeavyPlateCover
import OAI.MeasureTheory.Falconer.Radial.HeavyPlateCover

namespace OAI

/-! # Finite thicker-plate covers of the actual original dyadic exclusions -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem dyadic_heavy_plate_covers (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d))
    (Q : DyadicCube d) (hQ : 0 < Q.side) {M s C : ℝ}
    (hM : 0 ≤ M) (hroot : ∀ x ∈ Q.carrier, ‖x‖ ≤ M)
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ j : ℕ, let δ := (2:ℝ)^(-(j:ℝ))
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ A*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        heavyPlateCellPairs ((μ : Measure (Space d))+(ν : Measure (Space d))) Q j δ
          (2*δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ⊆
          ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ A*δ^(1/4:ℝ)} ×ˢ
            {y | |inner ℝ p.1 y-p.2| ≤ A*δ^(1/4:ℝ)} := by
  obtain ⟨K,hK,hcover⟩ := original_heavy_plate_cover hpublished hd μ ν hM hs hs' hC
    hμbounded hνbounded hμfrost hνfrost
  let D := Real.sqrt d*Q.side
  have hD : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) hQ.le
  refine ⟨K+D,by linarith only [hK,hD],?_⟩
  intro j
  let δ := (2:ℝ)^(-(j:ℝ))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by norm_num) _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hδeq : δ = 1/(2:ℝ)^j := by
    dsimp [δ]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover δ hδ hδ1
  refine ⟨S,hunit,hcard.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith only [hD]) (Real.rpow_nonneg hδ.le _)
  · have hdiam : ∀ p ∈ cubePaths d j, ∀ x ∈ (Q.descendant p).carrier,
        ∀ y ∈ (Q.descendant p).carrier, dist x y ≤ D*δ := by
      intro p hp x hx y hy
      have hh := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hx hy
      rw [Q.descendant_side,(mem_cubePaths d j p).mp hp] at hh
      apply hh.trans_eq
      rw [hδeq]
      dsimp [D]
      ring
    have hc := heavyPlateCellPairs_finite_cover
      ((μ : Measure (Space d))+(ν : Measure (Space d))) Q j S hunit hdiam
      (fun w hw t ht => by
        obtain ⟨p,hp,hpc⟩ := hcoverS w hw t ht
        exact ⟨p,hp,fun x hx hxt => hpc x (hroot x hx) hxt⟩)
    have hδgrow : δ ≤ δ^(1/4:ℝ) := by
      calc
        δ = δ^(1:ℝ) := (Real.rpow_one δ).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
    have hwidth : K*δ^(1/4:ℝ)+D*δ ≤ (K+D)*δ^(1/4:ℝ) := by
      nlinarith only [mul_le_mul_of_nonneg_left hδgrow hD]
    intro xy hxy
    obtain ⟨p,hp,hx,hy⟩ := mem_iUnion₂.mp (hc hxy)
    exact mem_iUnion₂.mpr ⟨p,hp,hx.trans hwidth,hy.trans hwidth⟩

end Falconer

end OAI
