import OAI.Probability.SLE.Multipoint.MultipointDiscountCost

namespace OAI

/-! A single finite-order Young coefficient controls every active subset.
The coefficient is chosen before the stopping-time pattern is known. -/

noncomputable section
open scoped BigOperators

namespace SLEExactGauge.Multipoint

/-- The Young coefficient associated with one active subset. -/
def patternYoungConstant {ι : Type*} (κ : ℝ) (s : Finset ι) : ℝ :=
  let p := greenExponent κ
  youngConstant p (angularCoefficientConstant p^2)
    ((negativeDrift p/2)/(4*((s.card : ℝ)+1)))

/-- A common coefficient for all active subsets of a fixed finite family. -/
def allPatternYoungConstant {ι : Type*} (κ : ℝ) (I : Finset ι) : ℝ :=
  ∑ s ∈ I.powerset, patternYoungConstant κ s

lemma patternYoungConstant_pos {ι : Type*} {κ : ℝ}
    (hκ : 0 < κ) (hκ8 : κ < 8) (s : Finset ι) :
    0 < patternYoungConstant κ s := by
  have hp : 0 < greenExponent κ := by
    unfold greenExponent
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  exact youngConstant_pos hp (sq_pos_of_pos (angularCoefficientConstant_pos hp))
    (absorption_epsilon_pos (div_pos (negativeDrift_pos hp) (by norm_num)) s.card)

lemma patternYoungConstant_le_all {ι : Type*} [DecidableEq ι] {κ : ℝ}
    (hκ : 0 < κ) (hκ8 : κ < 8) {I s : Finset ι} (hs : s ⊆ I) :
    patternYoungConstant κ s ≤ allPatternYoungConstant κ I := by
  exact Finset.single_le_sum (fun t _ => (patternYoungConstant_pos hκ hκ8 t).le)
    (Finset.mem_powerset.mpr hs)

lemma allPatternYoungConstant_pos {ι : Type*} [DecidableEq ι] {κ : ℝ}
    (hκ : 0 < κ) (hκ8 : κ < 8) (I : Finset ι) :
    0 < allPatternYoungConstant κ I :=
  (patternYoungConstant_pos hκ hκ8 (∅ : Finset ι)).trans_le
    (patternYoungConstant_le_all hκ hκ8 (Finset.empty_subset I))

/-- The actual drift cost is controlled by one deterministic coefficient,
while keeping precisely the current active single and pair sums. -/
theorem productDriftCost_le_uniform {ι : Type*} [DecidableEq ι]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {I s : Finset ι} (hs : s ⊆ I)
    (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i) (z : ι → ℂ × ℝ) (x : ℝ) :
    productDriftCost s κ D σ z x ≤
      κ*((driftAllowance (greenExponent κ)*
          driftThreshold (greenExponent κ)^(-greenExponent κ))*
        (∑ i ∈ s, branchRegulator κ (D i) (σ i) (z i)*logVelocity κ (z i) x^2) +
        allPatternYoungConstant κ I *
          (∑ ij ∈ s.offDiag,
            (branchRegulator κ (D ij.1) (σ ij.1) (z ij.1)*
              branchRegulator κ (D ij.2) (σ ij.2) (z ij.2))^(-exponent (greenExponent κ))*
            (logVelocity κ (z ij.1) x*logVelocity κ (z ij.2) x))) := by
  have hpair : 0 ≤ ∑ ij ∈ s.offDiag,
      (branchRegulator κ (D ij.1) (σ ij.1) (z ij.1)*
        branchRegulator κ (D ij.2) (σ ij.2) (z ij.2))^(-exponent (greenExponent κ))*
      (logVelocity κ (z ij.1) x*logVelocity κ (z ij.2) x) := by
    apply Finset.sum_nonneg
    intro ij hij
    obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
    exact mul_nonneg (Real.rpow_nonneg (mul_nonneg
      (mul_pos (hD _ hi) (Real.exp_pos _)).le
      (mul_pos (hD _ hj) (Real.exp_pos _)).le) _)
      (mul_pos (logVelocity_pos κ (z ij.1) x) (logVelocity_pos κ (z ij.2) x)).le
  unfold productDriftCost
  apply mul_le_mul_of_nonneg_left _ hκ.le
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (patternYoungConstant_le_all hκ hκ8 hs) hpair)

end SLEExactGauge.Multipoint

end

end OAI
