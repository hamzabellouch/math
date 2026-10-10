import OAI.NumberTheory.TwoPoint.Bounds.PrimeComplexMatrix
import OAI.NumberTheory.TwoPoint.Walks.FiveColorBilinear

namespace OAI

/-! The ten-color reduction applies to the actual retained prime graph. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma retainedDirectedMatrix_short_support {V : Type*}
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (D : ℤ)
    (hshift : ∀ q ∈ Q, eligible q → D ≤ (h * q * d : ℕ) ∧ (h * q * d : ℕ) < 2 * D)
    (i j : V) (hne : retainedDirectedMatrix site Q u eligible g center L K
      extra keep h d gate i j ≠ 0) : D ≤ site j - site i ∧ site j - site i < 2 * D := by
  by_contra hbad
  apply hne
  unfold retainedDirectedMatrix
  split_ifs
  · apply sum_eq_zero
    intro q hq
    apply Complex.ofReal_eq_zero.mpr
    unfold retainedRealEdge
    split_ifs with he
    · apply False.elim
      apply hbad
      have hr := hshift q hq he.2.2.2.2.1
      rw [he.2.2.2.1, add_sub_cancel_left]
      exact hr
    · rfl
  · rfl

lemma retainedPrimeMatrix_short_support {J : ℕ} {V : Type*} [Fintype V]
    (P : Fin J → Finset ℕ) (site : V → ℤ) (Q : Finset ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (D : ℤ)
    (hshift : ∀ d : (j : Fin J) → P j, ∀ q ∈ Q, eligible (∏ j, (d j).val) q →
      D ≤ (h * q * ∏ j, (d j).val : ℕ) ∧ (h * q * ∏ j, (d j).val : ℕ) < 2 * D)
    (i j : V) (hne : retainedPrimeMatrix P site Q u eligible g L K extra keep h gate i j ≠ 0) :
    D ≤ site j - site i ∧ site j - site i < 2 * D := by
  by_contra hbad
  apply hne
  simp only [retainedPrimeMatrix, Matrix.sum_apply]
  apply sum_eq_zero
  intro d _
  by_contra hd
  exact hbad (retainedDirectedMatrix_short_support site Q u _ g _ L K _ keep h _ _ D
    (hshift d) i j hd)

theorem projected_prime_directed_identity {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (D : ℤ) (hD : 0 < D)
    (hshift : ∀ d : (j : Fin J) → P j, ∀ q ∈ Q, eligible (∏ j, (d j).val) q →
      D ≤ (h * q * ∏ j, (d j).val : ℕ) ∧ (h * q * ∏ j, (d j).val : ℕ) < 2 * D)
    (F G : ℤ → ℂ) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate
    let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
    let proj := coordinateProjection (fun i => keep (site i))
    let A := retainedPrimeMatrix P site Q u eligible (actualPaddingVertex Qp) L K extra
      (fun n => keep n ∧ actualPaddingDegreeCut Qp L n) h gate
    (∑ i, ∑ j, F (site i) * G (site j) * A i j) =
      ∑ c : ForwardColorCode,
        let vf := paddingTestVector Qp L site
          (fun n => star (if sourceColor D c n then F n else 0))
        let vg := paddingTestVector Qp L site
          (fun n => if targetColor D c n then G n else 0)
        inner ℂ vf ((proj * (∑ d, B d) * proj) vg) := by
  dsimp only
  let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
  let A := retainedPrimeMatrix P site Q u eligible (actualPaddingVertex Qp) L K extra
    (fun n => keep n ∧ actualPaddingDegreeCut Qp L n) h gate
  have hs := retainedPrimeMatrix_short_support P site Q u eligible (actualPaddingVertex Qp)
    L K extra (fun n => keep n ∧ actualPaddingDegreeCut Qp L n) h gate D hshift
  have hc := five_color_bilinear_identity D hD site A hs
    (fun i => F (site i)) (fun i => G (site i))
  rw [← hc]
  apply sum_congr rfl
  intro c _
  exact (projected_prime_complex_bilinear P hprime hdisjoint site Q Qp u eligible L K W
    extra h gate hgate (fun n => if sourceColor D c n then F n else 0)
      (fun n => if targetColor D c n then G n else 0)).symm

end TwoPointCorrelations

end OAI
