import OAI.MeasureTheory.Falconer.Estimates.ScalarRoundingScale

namespace OAI

/-! The scalar projection theorem for arbitrary separated points in the
 unit interval. Dyadic rounding has been removed from the hypotheses. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_unit_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ B M0 : ℕ, ∃ ε : ℝ, 0 < B ∧ 0 < M0 ∧ 0 < ε ∧
      ∀ M : ℕ, M0 ≤ M →
      let δ := (1/2:ℝ)^(B*M)
      let W := Real.exp (ε*(B:ℝ)*(M:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, 0 ≤ x ∧ x < 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  obtain ⟨B,N0,η,hB,hN0,hη,hgrowth⟩ := scalar_weak_projection hκ hκ1
  obtain ⟨N1,hN1,hscale⟩ := scalar_rounding_scale hη hκ.le B hB
  refine ⟨B,max N0 N1,η/4,hB,lt_of_lt_of_le hN0 (le_max_left _ _),by positivity,?_⟩
  intro M hM
  dsimp only
  intro X hX hXunit hsep hsize hadd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^(B*M)
  let W := Real.exp ((η/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
  let W0 := Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  obtain ⟨hfive,htwo⟩ := hscale M ((le_max_right _ _).trans hM)
  change 5*W ≤ W0 at hfive
  change (2:ℝ)^κ*W ≤ W0 at htwo
  have hWle : W ≤ W0 := by linarith
  let L := scalarPointLeaves (B*M) X
  have hL : L ⊆ cubePaths 1 (B*M) := scalarPointLeaves_subset _ X hXunit
  have hLne : L.Nonempty := hX.image _
  have hLcard : L.card = X.card := scalarPointLeaves_card _ X hXunit hsep
  have hYcard : (scalarRoundedPoints (B*M) X).card = X.card := scalarRoundedPoints_card _ X hXunit hsep
  have hnear := scalarRoundedPoints_near (B*M) X hXunit
  have hdoubling : ((scalarCells δ (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
      W0*(L.card:ℝ) := by
    have hh := scalar_matched_projection_cover (a := (1:ℝ)) hδ (by norm_num) X
      (scalarRoundedPoints (B*M) X) hnear
    have hh' : ((scalarCells δ (scalarRoundedPoints (B*M) X+scalarRoundedPoints (B*M) X)).card:ℝ) ≤
        5*((scalarCells δ (X+X)).card:ℝ) := by exact_mod_cast (by simpa using hh)
    change ((scalarCells δ (scalarRoundedPoints (B*M) X+scalarRoundedPoints (B*M) X)).card:ℝ) ≤ _
    rw [hLcard]
    have hm := mul_le_mul_of_nonneg_right hfive (Nat.cast_nonneg X.card)
    nlinarith
  have hballs : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u r ≤ W0*r^κ*(L.card:ℝ) := by
    intro u r hr hr1
    have hh := scalar_rounding_ball_bound (B*M) X hXunit hsep hW1 hκ.le hpoint u r hr hr1
    rw [hYcard] at hh
    have hm := mul_le_mul_of_nonneg_right htwo
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) κ) (Nat.cast_nonneg X.card))
    change scalarBallMass (scalarRoundedPoints (B*M) X) u r ≤ _
    rw [hLcard]
    nlinarith
  have hEballs : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ W0*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr hr1
    have hh := hEball u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hWle
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    nlinarith
  have hsizeL : Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 := by rwa [hLcard]
  obtain ⟨a,ha,hgain⟩ := hgrowth M ((le_max_left _ _).trans hM) L hL hLne hsizeL
    hdoubling hballs E hE hEbound hEballs
  by_contra hn
  push Not at hn
  have hh := scalar_matched_projection_cover hδ (hEbound a ha) X
    (scalarRoundedPoints (B*M) X) hnear
  have hhR : ((scalarCells δ (scalarRoundedPoints (B*M) X+
      (scalarRoundedPoints (B*M) X).image (fun x => a*x))).card:ℝ) ≤
      5*((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by exact_mod_cast hh
  have hp := hn a ha
  have hm := mul_le_mul_of_nonneg_right hfive (Nat.cast_nonneg X.card)
  rw [hLcard] at hgain
  change W0*(X.card:ℝ) < ((scalarCells δ (scalarRoundedPoints (B*M) X+
    (scalarRoundedPoints (B*M) X).image (fun x => a*x))).card:ℝ) at hgain
  nlinarith

end Falconer.Regularization

end OAI
