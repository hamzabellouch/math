import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppedSupport
import OAI.NumberTheory.CubicMoment.Estimates.GeometricPrimeBins

namespace OAI

/-! The sparse-support hypotheses follow from the actual descending
geometric bins and the ordinary X^.36 then X^.38 stopping thresholds. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometric_late_prime_bound {ρ B M : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {h : ℕ} (hboundary : ρ*geometricBinLower ρ B h ≤ M)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B)
    (hbin : h ≤ geometricPrimeBin ρ B p) : norm p ≤ M := by
  have hlower : geometricBinLower ρ B (geometricPrimeBin ρ B p) ≤
      geometricBinLower ρ B h := by
    apply pow_le_pow_right₀ hρ.le
    omega
  exact (((geometricPrimeBin_cell hρ hρ₂ hp hpB).2.trans_le
    (mul_le_mul_of_nonneg_left hlower (zero_le_one.trans hρ.le))).trans_le hboundary).le

lemma ordinary_late_threshold_ratio {X : ℝ} (hX : 0 < X) :
    X^(38/100:ℝ)/X^(36/100:ℝ) = X^(1/50:ℝ) := by
  rw [←Real.rpow_sub hX]
  norm_num

theorem ordinary_late_stopped_support
    (R D : Finset Eisenstein) (f : Eisenstein → ℂ) (w : ℝ)
    {X B ρ C : ℝ} (hX : 0 < X) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j k h : ℕ) (hboundary : ρ*geometricBinLower ρ X h ≤ (Real.log X)^C)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    {b : Eisenstein} (hb : primary b) (hsb : Squarefree b) (hbB : norm b ≤ B)
    (hβ : stoppedBeta R D f primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b ≠ 0) :
    b ∈ sparseLateSupport X C (1/50) B := by
  apply stoppedBeta_late_mem_sparse R D f w (geometricPrimeBin ρ X)
    (geometricBinLower ρ X) j k h (Real.rpow_pos_of_pos hX _) _ hR
    (fun d hd => (hD d hd).1) _ _ hb hsb hbB hβ
  · exact (ordinary_late_threshold_ratio hX).ge
  · intro d hd p hp
    have hpp := (primaryPrimeFactor_spec (hD d hd).1 hp).1
    have hpX := (norm_le_of_dvd (primary_ne_zero (hD d hd).1)
      (primaryPrimeFactor_spec (hD d hd).1 hp).2).trans (hD d hd).2
    exact ⟨zero_lt_one.trans (geometricBinLower_gt_one hρ
      (geometricPrimeBin_index hρ hρ₂ hpp hpX)),(geometricPrimeBin_cell hρ hρ₂ hpp hpX).1⟩
  · intro d hd p hp hbin
    have hpp := (primaryPrimeFactor_spec (hD d hd).1 hp).1
    have hpX := (norm_le_of_dvd (primary_ne_zero (hD d hd).1)
      (primaryPrimeFactor_spec (hD d hd).1 hp).2).trans (hD d hd).2
    exact geometric_late_prime_bound hρ hρ₂ hboundary hpp hpX hbin

/-- The literal ordinary late-stop coefficient has power-saving energy.
Only the concrete location of the roughness boundary is required; the
large divisor and its sparse multiple support follow from the stopping condition. -/
theorem ordinary_late_stopped_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ : ℝ), 0 ≤ B → B ≤ X → 1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D U : Finset Eisenstein),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d ∧ norm d ≤ X) →
      (∀ b ∈ U, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∑ b ∈ U, ‖stoppedBeta R D
        (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
        primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b‖^2) ≤ K*B*X^(-δ) := by
  obtain ⟨δ,K,hδ,hK,hbound⟩ := sparse_stopped_beta_energy (ι := ι) (η := 1/50)
    hpnt hC (by norm_num) hξ hξz
  refine ⟨δ,K,hδ,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hbound hX
  intro B ρ hB hBX hρ hρ₂ j k h hboundary S W R D U hS hW hR hD hU
  apply hbound B (X^(38/100:ℝ)) (X^(36/100:ℝ)) hB hBX
    (Real.rpow_pos_of_pos hX _) ((ordinary_late_threshold_ratio hX).ge)
    S W R D U (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k h hS hW hR
    (fun d hd => (hD d hd).1) _ _ hU
  · intro d hd p hp
    have hpp := (primaryPrimeFactor_spec (hD d hd).1 hp).1
    have hpX := (norm_le_of_dvd (primary_ne_zero (hD d hd).1)
      (primaryPrimeFactor_spec (hD d hd).1 hp).2).trans (hD d hd).2
    exact ⟨zero_lt_one.trans (geometricBinLower_gt_one hρ
      (geometricPrimeBin_index hρ hρ₂ hpp hpX)),(geometricPrimeBin_cell hρ hρ₂ hpp hpX).1⟩
  · intro d hd p hp hbin
    have hpp := (primaryPrimeFactor_spec (hD d hd).1 hp).1
    have hpX := (norm_le_of_dvd (primary_ne_zero (hD d hd).1)
      (primaryPrimeFactor_spec (hD d hd).1 hp).2).trans (hD d hd).2
    exact geometric_late_prime_bound hρ hρ₂ hboundary hpp hpX hbin

end CubicFirstMoment

end

end OAI
