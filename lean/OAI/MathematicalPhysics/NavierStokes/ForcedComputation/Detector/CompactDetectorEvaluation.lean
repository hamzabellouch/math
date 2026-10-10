import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorOracle

namespace OAI

/-! A terminating evaluator for the finite relative detector expressions.
It works at arbitrary fast-named spacetime points and for all ordered mixed
derivatives.  The only oracle calls evaluate derivatives of the input V. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.DetectorExpr
open ShearFlows Filter
open scoped ContDiff Topology BigOperators

variable {F : PlanarComponents}

def Ready (o : PlanarJetOracle F) (e : DetectorExpr) (he : e.Valid)
    (q : RationalSpaceTime) (ε : ℚ) (n : ℕ) : Prop :=
  (e.enclose o he q n).radius ≤ ε

instance readyDecidable (o : PlanarJetOracle F) (e : DetectorExpr) (he : e.Valid)
    (q : RationalSpaceTime) (ε : ℚ) (n : ℕ) : Decidable (Ready o e he q ε n) :=
  inferInstanceAs (Decidable ((e.enclose o he q n).radius ≤ ε))

theorem ready_exists (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (q : RationalSpaceTime)
    {ε : ℚ} (hε : 0 < ε) : ∃ n, Ready o e he q ε n := by
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := ((e.enclose_converges o hF he q).2.eventually_lt_const hε').exists
  exact ⟨n, by exact_mod_cast hn.le⟩

def evaluateRational (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (e : DetectorExpr) (he : e.Valid) (q : RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : ℚ :=
  (e.enclose o he q (Nat.find (ready_exists o hF he q hε))).center

theorem evaluateRational_spec (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (q : RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) :
    |e.val F (rationalPoint q) - (evaluateRational o hF e he q ε hε : ℝ)| ≤ (ε : ℝ) := by
  exact (e.enclose_contains o hF he q (Nat.find (ready_exists o hF he q hε))).trans
    (by exact_mod_cast Nat.find_spec (ready_exists o hF he q hε))

def derivativeBound (o : PlanarJetOracle F) (e : DetectorExpr) (M : ℚ) : ℚ :=
  ∑ k : Fin 4, (e.diff k).bound o M

theorem derivativeBound_nonneg (o : PlanarJetOracle F) (e : DetectorExpr) (M : ℚ) :
    0 ≤ derivativeBound o e M :=
  Finset.sum_nonneg (fun k _ => (e.diff k).bound_nonneg o M)

theorem fderiv_bound (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (M : ℚ) (y : SpaceTime)
    (hy : |y.1| ≤ |(M : ℝ)|) : ‖fderiv ℝ (e.val F) y‖ ≤ (derivativeBound o e M : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Rat.cast_nonneg.mpr (derivativeBound_nonneg o e M))
  intro v
  conv_lhs => rw [← spaceTimeDirections_sum v]
  rw [map_sum]
  calc
    _ ≤ ∑ k : Fin 4, ‖fderiv ℝ (e.val F) y
        (timeSpaceCoord k v • spaceTimeDirection k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin 4, ‖v‖ * ((e.diff k).bound o M : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [map_smul, norm_smul]
      have hk : ‖fderiv ℝ (e.val F) y (spaceTimeDirection k)‖ ≤
          ((e.diff k).bound o M : ℝ) := by
        rw [← e.val_diff hF he k y, Real.norm_eq_abs]
        exact val_bound o (valid_diff he k) M y hy
      exact mul_le_mul (timeSpaceCoord_norm k v) hk (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      rw [derivativeBound, Rat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem lipschitz_bound (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (M : ℚ) (x y : SpaceTime)
    (hx : |x.1| ≤ |(M : ℝ)|) (hy : |y.1| ≤ |(M : ℝ)|) :
    |e.val F x - e.val F y| ≤ (derivativeBound o e M : ℝ) * ‖x - y‖ := by
  let S : Set SpaceTime := Set.Icc (-|(M : ℝ)|) |(M : ℝ)| ×ˢ Set.univ
  have hc : Convex ℝ S := (convex_Icc _ _).prod convex_univ
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (e.smooth hF he).differentiable (by simp) z)
    (fun z hz => fderiv_bound o hF he M z (abs_le.mpr hz.1)) hc
    (show y ∈ S from ⟨abs_le.mp hy, Set.mem_univ _⟩)
    (show x ∈ S from ⟨abs_le.mp hx, Set.mem_univ _⟩)
  simpa only [Real.norm_eq_abs] using h

def inputPrecision (o : PlanarJetOracle F) (e : DetectorExpr) (M ε : ℚ) : ℕ :=
  ⌈2 * derivativeBound o e M / ε⌉₊ + 1

theorem inputPrecision_spec (o : PlanarJetOracle F) (e : DetectorExpr)
    (M : ℚ) {ε : ℚ} (hε : 0 < ε) :
    (derivativeBound o e M : ℝ) * errorTolerance (inputPrecision o e M ε) ≤ (ε : ℝ) / 2 := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have hn : 2 * (derivativeBound o e M : ℝ) / ε ≤ (inputPrecision o e M ε : ℝ) := by
    have h : 2 * derivativeBound o e M / ε ≤ (inputPrecision o e M ε : ℚ) :=
      (Nat.le_ceil _).trans (by simp [inputPrecision])
    exact_mod_cast h
  have hp : (inputPrecision o e M ε : ℝ) ≤ (2 : ℝ) ^ inputPrecision o e M ε := by
    exact_mod_cast (Nat.lt_two_pow_self (n := inputPrecision o e M ε)).le
  have hle := hn.trans hp
  have hpow : (0 : ℝ) < 2 ^ inputPrecision o e M ε := by positivity
  rw [errorTolerance, ← div_eq_mul_inv]
  apply (div_le_iff₀ hpow).mpr
  have h := (div_le_iff₀ he).mp hle
  linarith

def evaluate (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (e : DetectorExpr) (he : e.Valid) (a : ℕ → RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : ℚ :=
  evaluateRational o hF e he
    (a (inputPrecision o e (ClockedExpr.nameRadius a) ε)) (ε / 2) (by positivity)

theorem evaluate_spec (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (a : ℕ → RationalSpaceTime)
    {y : SpaceTime} (ha : IsFastName a y) (ε : ℚ) (hε : 0 < ε) :
    |e.val F y - (evaluate o hF e he a ε hε : ℝ)| ≤ (ε : ℝ) := by
  let n := inputPrecision o e (ClockedExpr.nameRadius a) ε
  let q := a n
  obtain ⟨hy, hq⟩ := ClockedExpr.nameRadius_bounds ha n
  calc
    _ ≤ |e.val F y - e.val F (rationalPoint q)| +
        |e.val F (rationalPoint q) - (evaluate o hF e he a ε hε : ℝ)| := abs_sub_le _ _ _
    _ ≤ (ε : ℝ) / 2 + (ε : ℝ) / 2 := by
      apply add_le_add
      · exact (lipschitz_bound o hF he (ClockedExpr.nameRadius a) y (rationalPoint q) hy hq).trans
          ((mul_le_mul_of_nonneg_left (ha n)
            (Rat.cast_nonneg.mpr (derivativeBound_nonneg o e _))).trans
            (inputPrecision_spec o e _ hε))
      · simpa only [evaluate, Rat.cast_div, Rat.cast_ofNat] using
          evaluateRational_spec o hF he q (ε / 2) (by positivity)
    _ = _ := by ring

theorem evaluate_mixed_spec (o : PlanarJetOracle F) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (α : List (Fin 4)) (a : ℕ → RationalSpaceTime)
    {y : SpaceTime} (ha : IsFastName a y) (ε : ℚ) (hε : 0 < ε) :
    |ClockedExpr.scalarMixed (e.val F) α y -
      (evaluate o hF (e.diffWord α) (valid_diffWord he α) a ε hε : ℝ)| ≤ (ε : ℝ) := by
  rw [← e.val_diffWord hF he α]
  exact evaluate_spec o hF (valid_diffWord he α) a ha ε hε

end ForcedComputation.VelocityDetector.DetectorExpr

end

end OAI
