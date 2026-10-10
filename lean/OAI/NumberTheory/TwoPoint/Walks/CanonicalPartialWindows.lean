import OAI.NumberTheory.TwoPoint.Walks.CanonicalTupleSlices
import OAI.NumberTheory.TwoPoint.Bounds.ExtractedWindowScale
import OAI.NumberTheory.TwoPoint.Bounds.BinCutoffGeometry

namespace OAI

/-! Actual logarithmic bins and bounded padding provide the window and
length hypotheses in the quantitative partial-centering estimate. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma partial_bin_window (q t z : ℕ) (hq : 0 < q) (ht : 0 < t) (hz : 0 < z)
    (η : ℝ) (j : ℤ) (hbin : actualPaddingBin η (Real.log (t * z : ℕ)) j q) :
    Real.exp ((j : ℝ) * η) / (q * t : ℕ) ≤ (z : ℝ) ∧
      (z : ℝ) ≤ Real.exp η * (Real.exp ((j : ℝ) * η) / (q * t : ℕ)) := by
  have hd := Nat.mul_pos ht hz
  have hc := actualPaddingBin_cutoff (t * z) q hd hq η 1 (by norm_num) j hbin
  have hu : (0 : ℝ) < (q * t : ℕ) := by exact_mod_cast Nat.mul_pos hq ht
  have hv : (0 : ℝ) < (t * z * q : ℕ) := by exact_mod_cast Nat.mul_pos hd hq
  simp only [one_mul] at hc
  constructor
  · apply (div_le_iff₀ hu).mpr
    have hh := (div_le_iff₀ hv).mp hc.2
    push_cast at hh ⊢
    nlinarith
  · have hh := (le_div_iff₀ hv).mp hc.1
    have he : Real.exp η * Real.exp (-η) = 1 := by
      rw [← Real.exp_add]; simp
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos η).le
    have heq : Real.exp η * (Real.exp (-η) * (t * z * q : ℕ)) = (t * z * q : ℕ) := by
      rw [← mul_assoc, he, one_mul]
    rw [heq] at hm
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hu).mpr
    push_cast at hm ⊢
    nlinarith

theorem ModFiveThetaInput.eventually_partial_extracted_windows (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ∀ (I : Finset (Fin J)) (q : ℕ),
      q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊ →
      ∀ (y : (j : {j // j ∉ I}) → P j) (T : ℝ), Real.exp (L ^ (1000 : ℝ)) ≤ T →
        Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤
          ((⌊T⌋₊ / (q * ∏ j, (y j).val) : ℕ) : ℝ) := by
  filter_upwards [hP.eventually_canonical_tuple_slices E W hW,
    eventually_ge_atTop (1000 : ℝ)] with L hs hL
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hp := centeredPrimeBands_prime E A W J
  have hA : 0 < A := Real.rpow_pos_of_pos (by linarith) _
  have hend := primeSupplyScale_endpoint W L (by linarith) (by linarith)
  intro I q hq y T hT
  have hqp : 0 < q := retainedPrimeDivisor_pos _ (fun _ hp => paddingPrimeSupply_prime hp)
    (mem_filter.mp hq).1
  have htp : 0 < ∏ j, (y j).val := prod_pos fun j _ => (hp j _ (y j).property).pos
  have ht : ((∏ j, (y j).val : ℕ) : ℝ) ≤ Real.exp (2 * L) := by
    apply retainedTuple_le_full_bound P I hp hs.1 _ _ y
    intro d hd
    exact (show (d : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by
      exact_mod_cast centeredPrimeTuple_upper E A W L J hA hW hend hd).trans
        (Nat.floor_le (Real.exp_pos _).le)
  have hqbound := boundedPaddingDivisor_real_upper E L (by linarith) q hq
  apply extracted_window_lower L T _ hL (Nat.mul_pos hqp htp) hT
  calc
    _ = (q : ℝ) * ((∏ j, (y j).val : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (100 * L ^ 2) * Real.exp (2 * L) :=
      mul_le_mul hqbound ht (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end TwoPointCorrelations

end OAI
