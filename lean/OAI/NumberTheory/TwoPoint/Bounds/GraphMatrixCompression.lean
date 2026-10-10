import OAI.NumberTheory.TwoPoint.Bounds.GraphSpectralTransfer
import OAI.NumberTheory.TwoPoint.Walks.BlockOperatorSpectrum

namespace OAI

/-! The real integer-edge matrix, its complex graph operator, and the
nonbacktracking block have exactly the same spectral parameter. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical NNReal ENNReal

noncomputable def primeRealEdgeMatrix {J : ℕ} {V : Type*} [Fintype V]
    (P : Fin J → Finset ℕ) (site : V → ℤ) (Q : Finset ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (d : (j : Fin J) → P j) : Matrix V V ℝ :=
  fun i j => if gate (∏ k, (d k).val) i j then
    integerEdgeMatrix site Q u (eligible (∏ k, (d k).val)) g
      (centeredTuple (∏ k, (d k).val).primeFactors) L K
      (extra (∏ k, (d k).val)) h (∏ k, (d k).val) i j else 0

lemma primeFamilyGraphOperator_eq_realMatrix {J : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (d : (j : Fin J) → P j) :
    primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible g L K extra h gate d =
    matrixOperator (fun i j => (primeRealEdgeMatrix P site Q u eligible g L K extra h gate d i j : ℂ)) := by
  have hc : familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d =
      centeredTuple (∏ j, (d j).val).primeFactors := by
    funext n
    exact familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
      d (selectedPrimeValues_injective d hdisjoint) n
  unfold primeFamilyGraphOperator
  rw [hc]
  congr 1
  funext i j
  simp only [maskedIntegerEdgeMatrix, maskMatrix, primeRealEdgeMatrix, familyTuple]
  split_ifs <;> simp

theorem prime_graph_compression_of_matrix_radius {J : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (R : ℝ) (hR : 0 ≤ R) (hsingle : 2 * K ≤ R)
    (hsquare : 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2)
    (hradius : realMatrixSpectralRadius (blockNonbacktrackingMatrix
      (primeRealEdgeMatrix P site Q u eligible g L K extra h gate)) ≤ R) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible g L K extra h gate
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    ‖proj * (∑ d, B d) * proj‖ ≤ 3 * R := by
  apply prime_graph_compression_bound P hprime hdisjoint site hinj Q u eligible g
    L K W extra h gate hgate hL hK hu hg hV R hR hsingle hsquare
  have he : primeFamilyGraphOperator (fun j (p : P j) => p.val)
      (fun _ _ => 0) site Q u eligible g L K extra h gate =
      (fun d => matrixOperator (fun i j =>
        (primeRealEdgeMatrix P site Q u eligible g L K extra h gate d i j : ℂ))) := by
    funext d
    exact primeFamilyGraphOperator_eq_realMatrix P hprime hdisjoint site Q u eligible g
      L K extra h gate d
  rw [he, blockNonbacktracking_spectralRadius]
  have ht : spectralRadius ℂ (matrixOperator (fun i j =>
      (blockNonbacktrackingMatrix
        (primeRealEdgeMatrix P site Q u eligible g L K extra h gate) i j : ℂ))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) _)
  rw [← ENNReal.ofReal_toReal ht]
  exact ENNReal.ofReal_le_ofReal hradius

end TwoPointCorrelations

end OAI
