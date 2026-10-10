import OAI.NumberTheory.TwoPoint.Walks.HighRankActualDecay
import OAI.NumberTheory.TwoPoint.Bounds.WeightedTupleDesignation

namespace OAI

/-! Column-rank decay applied to the actual weighted mixed-difference majorants. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_weighted_high_rank_words
    (h : ℕ) (Cj Cm Cw : ℝ) (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (J R M Q D B H Z : ℕ)
      (P : Fin J → Finset ℕ) (Qp : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (j : Fin J) (perfect : Finset (Fin R)) (cut : Fin R)
      (origin : ColumnPrimeAssignment J R P → (Fin R → ℕ) → ℤ)
      (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpZ : ∀ i, p i ≤ Z)
      (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → ι)
      (target : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → Fin Z)
      (base : ι → Fin Z) (U : Finset (Fin R × Fin J))
      (weight G : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → (ι → Fin Z) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass Qp ≤ L ^ (2 : ℕ) → 1 ≤ primeHarmonicMass (P j) →
      (∀ l, ∀ r ∈ P l, r.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ r ∈ P j, H ≤ r) → (∀ r ∈ P j, r ≤ B) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (B : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i, Squarefree (a.2 i)) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors ⊆ Qp) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors.card ≤ M) →
      (∀ a ∈ F, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
        (by change 0 < R; omega) h perfect cut ⌊L ^ (1 / 50 : ℝ)⌋₊) →
      (∀ a ∈ F, ∀ i ∈ perfect, ((a.1 j i).val : ℤ) ∣ origin a.1 a.2 +
        wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val)) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      Function.Injective p →
      (∀ a ∈ F, U ⊆ nonsingletonSlots (label a)) →
      (∀ a ∈ F, ∀ i ∈ nonsingletonLabels (label a), (H : ℝ) ≤ p i) →
      (∀ a ∈ F, Disjoint (tuplePrimeSupport a.1) (paddingPrimeSupport a.2)) →
      (∀ a ∈ F, ∀ i ∈ univ.image (label a),
        p i ∈ wordDivisorPrimeSupport (columnTupleWord a.1 forward a.2)) →
      (∀ a ∈ F, ∀ r ∈ wordDivisorPrimeSupport (columnTupleWord a.1 forward a.2), ∃ i, p i = r) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, |G a x| ≤ 1) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        RetainedMainTests p (univ.image (label a)) h Z (columnTupleWord a.1 forward a.2) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, designatedReciprocal p (singletonLabels (label a))
        (nonsingletonSlots (label a) \ U) U (label a) *
        (FiniteLaw.independent (fun i => uniformResidueLaw Z (p i) (hp i) (hpZ i))).average
          (fun x => weight a x * |selectedMixedDifference (singletonLabels (label a))
            (singletonTarget (label a) (target a) base)
            (fun y => G a (forceCoordinates ((nonsingletonSlots (label a) \ U).image (label a))
              (litForcedTarget (nonsingletonSlots (label a) \ U) (label a) (target a) base) y)) x|)) ≤
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_actual_high_rank_decay h Cj Cm Cw hCj hCm hCw] with L hL hdecay
  intro ι _ _ J R M Q D B H Z P Qp F forward j perfect cut origin p hp hpZ label target base U
    weight G cap W hR hRL hJ hM hT hRp hmass hQmass hV hprime hdisjoint hlo hB hQ hD
    hBexp hH hq hd hsq hpool hcount hrank hlit hW hWexp hinj hU hpH hsep hseen hcover
    hcap hw hwcap hG hretain hcost
  have hHone : (1 : ℝ) ≤ H :=
    (Real.one_le_exp (Real.rpow_nonneg (by linarith) _)).trans hH
  apply le_trans _ (hdecay J R M Q D B H P Qp F forward j perfect cut origin
    (fun a => cap a * 2 ^ (singletonLabels (label a)).card) W
    hR hRL hJ hM hT hRp hmass hQmass hV (hprime j) hlo hB hQ hD hBexp hH
    hq hd hsq hpool hcount hrank hlit hW hWexp hcost)
  apply sum_le_sum
  intro a ha
  have hb := weighted_designation_le_tuple_weight a.1 forward a.2 hprime hdisjoint
    (fun i => (hsq a ha i).ne_zero) (hsep a ha) Z h p hinj hp hpZ
    (label a) (target a) base U (hU a ha) H (cap a) hHone (hcap a ha) (hpH a ha)
    (hseen a ha) (hcover a ha) (weight a) (G a) (hw a ha) (hwcap a ha) (hG a ha) (hretain a ha)
  exact hb

end TwoPointCorrelations

end OAI
