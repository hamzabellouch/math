import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedLongBinSaving
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedShortBinSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSequenceSW
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLongBinSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedShortBinSaving

namespace OAI

/-! The complete Kummer sequence condition for the literal stopped
coefficient: exact long/short splitting, both largest-prime roles,
all bin costs, and the smooth remainder are derived. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_sequence_kummer_sw (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ A D H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖angular_stoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/ξ)
  have hgap : 1 < ξ*m := by
    have ht := (div_lt_iff₀ hξ).mp hm
    simpa only [mul_comm] using ht
  obtain ⟨K,hK,hlong⟩ := angular_stoppedBeta_long_bins_log_saving (ι := ι) m hEF ℓ hℓ
    (E := E) hA hD hH hF hJ hξ hξz hgap
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [hlong,angular_stoppedBeta_short_bin_log_saving ℓ (ι := ι) (D := D)
    hpnt hξ hξz hκ,eventually_gt_atTop (1:ℝ)] with X hlong hshort hX
  intro δ a b u V hδ hδone hwidth ha hblow hbX hV hu hVF W hW hWi hWd
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hρ : 1 < 1+δ := by linarith
  have hρ₂ : 1+δ ≤ 2 := by linarith
  have hb : 0 ≤ b := (Real.rpow_pos_of_pos (zero_lt_one.trans hX) κ).le.trans hblow
  let S := fun _ : ι => primeCutoff X
  let R := orderedConvolutionSupport S
  let T := primaryElementBall X
  let f := distinguishedTupleCoefficient S (fun l p => W l (norm p))
    primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let U := primaryPairSupport R T
  let F := fun n : Eisenstein =>
    if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
      then normTwist u n*angularCubicSymbol ℓ n v else 0
  have hS : ∀ l, ∀ p ∈ S l, primaryPrime p := fun _ _ hp => (mem_primeCutoff.mp hp).1
  have hR : ∀ r ∈ R, primary r := fun r hr =>
    orderedPrimarySupport_primary S (fun l p hp => (hS l p hp).1) hr
  have hT : ∀ t ∈ T, primary t := fun _ ht => (mem_primaryElementBall.mp ht).1
  have hU : ∀ n ∈ U, primary n := fun _ hn => primaryPairSupport_primary R T hR hT hn
  have hF : ∀ n, ¬(Squarefree n ∧ 1 < norm n ∧ norm n ≤ X) → F n = 0 := by
    intro n hn
    dsimp [F]
    split_ifs with hc
    · exact (hn ⟨hc.1,ha.trans_lt hc.2.2.1,hc.2.2.2.trans hbX⟩).elim
    · rfl
  have heq := stopped_long_bin_moment_decomposition U R T hU f F X (1+δ)
    (Real.exp (Real.sqrt (Real.log X))) (X^ξ) hρ hρ₂ hF j₀ k h Z Q early
  have hs : ‖angular_stoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
      (stoppedShortBinTest X (1+δ) (Real.exp (Real.sqrt (Real.log X))) j₀ k h Z Q early) v e‖ ≤
      b/(Real.log X)^D :=
    hshort X (1+δ) a b u hρ hρ₂ ha hbX hblow hbX S (fun l p => W l (norm p)) R T
      hS (fun l p _ => hW l _) hR hT j₀ k h Z Q early v e
  have hl := hlong δ a b u V hδ hδone hwidth hb hbX hV hu hVF
    W hW hWi hWd v e hv hnc hNv he heX j₀ k h Z Q early
  change ‖∑ n ∈ U, stoppedBeta R T f primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k h Z Q early) n*F n‖ ≤ _
  rw [heq]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs hl).trans_eq
  ring

end CubicFirstMoment

end

end OAI
