import OAI.NumberTheory.TwoPoint.Bounds.GraphMatrixCompression
import OAI.NumberTheory.TwoPoint.Bounds.ShiftMatrixTranslation

namespace OAI

/-! Match the translated physical matrix with the concrete prime graph,
including the original endpoint masks. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem primePhysicalMatrix_eq {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (site : V → ℤ) (Q : Finset ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (c : ℤ) :
    shiftMatrix (fun x : ((j : Fin J) → P j) × V => (x.1, site x.2))
      (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
      (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h
        (fun d n m => gate (∏ j, (d j).val) n m)
        (fun t n => maskedSignedIntegerWeight Q u eligible g
          (fun d => centeredTuple d.primeFactors) L K extra h keep t (n + c))) =
    blockNonbacktrackingMatrix (primeRealEdgeMatrix P (fun i => site i + c)
      Q u eligible g L K extra h (fun d i j =>
        gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c))) := by
  have hs := physicalBlockMatrix_eq_integer site Q (fun d : (j : Fin J) → P j => ∏ j, (d j).val) h
    (fun d n m => gate (∏ j, (d j).val) n m) u eligible g
    (fun d => centeredTuple d.primeFactors) L K extra keep c
  apply hs.trans
  congr 1
  funext d i j
  unfold primeRealEdgeMatrix
  by_cases hc : gate (∏ j, (d j).val) (site i) (site j) ∧
      keep (site i + c) ∧ keep (site j + c)
  · simp only [ite_eq_left hc]
  · simp only [ite_eq_right hc]

theorem prime_physical_compression {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (c : ℤ)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (R : ℝ) (hR : 0 ≤ R) (hsingle : 2 * K ≤ R)
    (hsquare : 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2)
    (hradius : realMatrixSpectralRadius
      (shiftMatrix (fun x : ((j : Fin J) → P j) × V => (x.1, site x.2))
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h
          (fun d n m => gate (∏ j, (d j).val) n m)
          (fun t n => maskedSignedIntegerWeight Q u eligible g
            (fun d => centeredTuple d.primeFactors) L K extra h keep t (n + c)))) ≤ R) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      (fun i => site i + c) Q u eligible g L K extra h
      (fun d i j => gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c))
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i + c) : ℝ) ≤ 6 * W * J)
    ‖proj * (∑ d, B d) * proj‖ ≤ 3 * R := by
  rw [primePhysicalMatrix_eq] at hradius
  apply prime_graph_compression_of_matrix_radius P hprime hdisjoint (fun i => site i + c)
    (fun i j hij => hinj (add_right_cancel hij)) Q u eligible g L K W extra h
    (fun d i j => gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c))
    ?_ hL hK hu hg hV R hR hsingle hsquare hradius
  intro d i j
  rw [hgate d (site i) (site j)]
  tauto

end TwoPointCorrelations

end OAI
