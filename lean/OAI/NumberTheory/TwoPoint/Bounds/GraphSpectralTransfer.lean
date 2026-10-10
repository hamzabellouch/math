import OAI.NumberTheory.TwoPoint.Bounds.ActualCenterDegree
import OAI.NumberTheory.TwoPoint.Bounds.CoordinateProjection
import OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyGraph

namespace OAI

/-! Apply the noncommuting transfer to the literal prime graph and its
degree projection. The single-edge and square-function bounds are proved. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical NNReal ENNReal

theorem prime_graph_compression_bound {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible g L K extra h gate
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    ∀ R : ℝ, 0 ≤ R → 2 * K ≤ R → 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2 →
      spectralRadius ℂ (nonbacktrackingContinuous B) ≤ ENNReal.ofReal R →
      ‖proj * (∑ d, B d) * proj‖ ≤ 3 * R := by
  dsimp only
  intro R hR hsingle hsquare hradius
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
    site Q u eligible g L K extra h gate
  let keep := fun i : V => (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection keep
  apply noncommuting_spectral_transfer B
    (fun d => primeFamilyGraphOperator_selfAdjoint _ _ _ _ _ _ _ _ _ _ _ _ hgate d)
    proj (coordinateProjection_selfAdjoint keep) (coordinateProjection_idempotent keep)
    ⟨R, hR⟩
  · intro d
    exact (primeFamilyGraphOperator_norm_le _ (fun j p => hprime j _ p.property)
      _ _ hinj _ _ _ _ _ _ _ _ _ hgate hL hK hu hg d).trans hsingle
  · intro v hv
    change (∑ d, ‖B d v‖ ^ 2) ≤ R ^ 2 * ‖v‖ ^ 2
    have hs := primeFamilyGraphOperator_square_sum (fun j (p : P j) => p.val)
      (fun j p => hprime j _ p.property) (fun _ _ => 0) site hinj
      Q u eligible g L K W extra h gate hgate hL hK hu hg hV v ?_
    · apply hs.trans
      exact mul_le_mul_of_nonneg_right (by simpa only [Fintype.card_fin] using hsquare)
        (sq_nonneg ‖v‖)
    · intro i hi
      have hk := coordinateProjection_support keep v hv i hi
      simpa only [zero_add, prime_band_indicator_sum P hdisjoint, Fintype.card_fin] using hk
  · convert hradius using 1
    exact (ENNReal.ofReal_eq_coe_nnreal hR).symm

end TwoPointCorrelations

end OAI
