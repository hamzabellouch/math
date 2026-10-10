import OAI.Geometry.IsometricImmersion.Taylor.TaylorCoefficientBounds
import OAI.Geometry.IsometricImmersion.Taylor.FiniteTaylorComparison
import Mathlib.Data.Nat.Choose.Sum

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem normalizedTimePower_abs_le_one (a t : ℝ) (m : ℕ) (ht : |t - a| ≤ 1) :
    |normalizedTimePower a m t| ≤ 1 := by
  have hpow : |t - a|^m ≤ (1 : ℝ) := pow_le_one₀ (abs_nonneg _) ht
  have hfact : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ m.factorial from Nat.factorial_pos m)
  rw [normalizedTimePower, abs_div, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg m.factorial : (0 : ℝ) ≤ (m.factorial : ℝ))]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hfact)).mpr (by simpa using hpow.trans hfact)

theorem normalizedTimePower_zero (a : ℝ) : normalizedTimePower a 0 = fun _ => (1 : ℝ) := by
  funext t
  simp [normalizedTimePower]

theorem normalizedTimePower_iteratedDeriv_abs_le_one (a t : ℝ) (m k : ℕ)
    (ht : |t - a| ≤ 1) : |iteratedDeriv k (normalizedTimePower a m) t| ≤ 1 := by
  induction k generalizing m with
  | zero => exact normalizedTimePower_abs_le_one a t m ht
  | succ k hk =>
    cases m with
    | zero =>
      rw [normalizedTimePower_zero]
      simp [iteratedDeriv_const]
    | succ m =>
      rw [iteratedDeriv_succ', normalizedTimePower_deriv]
      exact hk m

theorem normalizedTimePower_fullJet_le_one (a t : ℝ) (m k : ℕ)
    (ht : |t - a| ≤ 1) : ‖iteratedFDeriv ℝ k (normalizedTimePower a m) t‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact normalizedTimePower_iteratedDeriv_abs_le_one a t m k ht

theorem product_fullJet_bound {f h : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hh : ContDiffOn ℝ ∞ h V) (hV : IsOpen V)
    {p : Coord} (hp : p ∈ V) (k : ℕ) {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hfB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f p‖ ≤ A)
    (hhB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j h p‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun q => f q * h q) p‖ ≤ (2 : ℝ)^k * A * B := by
  have hm := norm_iteratedFDerivWithin_mul_le hf hh hV.uniqueDiffOn hp
    (n := k) (WithTop.coe_le_coe.mpr le_top)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hV hp] at hm
  have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ)^k := by
    exact_mod_cast Nat.sum_range_choose k
  apply hm.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfB j hjk) (Nat.cast_nonneg _))
        (hhB (k - j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ)^k * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

theorem spatialCoefficient_fullJet_le {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) {p : Coord} (hp : p 0 ∈ I) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : Coord => C (q 0)) p‖ ≤ ‖iteratedFDeriv ℝ k C (p 0)‖ := by
  have hh := norm_iteratedFDeriv_comp_contraction
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ) (f := C) hC hI
    (coordinateProjection_norm_le 0) (p := p) hp k
  change ‖iteratedFDeriv ℝ k (fun q : Coord => C (q 0)) p‖ ≤
    ‖iteratedFDeriv ℝ k C (p 0)‖ at hh
  exact hh

theorem timeMonomial_fullJet_le_one (a : ℝ) (m : ℕ) {p : Coord}
    (hp : |p 1 - a| ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : Coord => normalizedTimePower a m (q 1)) p‖ ≤ 1 := by
  have hh := norm_iteratedFDeriv_comp_contraction
    (ContinuousLinearMap.proj 1 : Coord →L[ℝ] ℝ) (f := normalizedTimePower a m)
    (normalizedTimePower_contDiff a m).contDiffOn isOpen_univ (coordinateProjection_norm_le 1)
      (p := p) (mem_univ (p 1)) k
  change ‖iteratedFDeriv ℝ k (fun q : Coord => normalizedTimePower a m (q 1)) p‖ ≤
    ‖iteratedFDeriv ℝ k (normalizedTimePower a m) (p 1)‖ at hh
  exact hh.trans (normalizedTimePower_fullJet_le_one a (p 1) m k hp)

theorem separatedTimePower_fullJet_bound {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (m k : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) (ht : |p 1 - a| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hCB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j C (p 0)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (separatedProduct C (normalizedTimePower a m)) p‖ ≤ (2 : ℝ)^k * B := by
  have hc : ContDiffOn ℝ ∞ (fun q : Coord => C (q 0)) (spatialStrip I) :=
    hC.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)
  have ht' : ContDiffOn ℝ ∞ (fun q : Coord => normalizedTimePower a m (q 1)) (spatialStrip I) :=
    ((normalizedTimePower_contDiff a m).comp (contDiff_apply ℝ ℝ 1)).contDiffOn
  have hb := product_fullJet_bound hc ht' (spatialStrip_isOpen hI) hp k hB zero_le_one
    (fun j hj => (spatialCoefficient_fullJet_le hC hI hp j).trans (hCB j hj))
    (fun order _ => timeMonomial_fullJet_le_one a m ht order)
  change ‖iteratedFDeriv ℝ k (separatedProduct C (normalizedTimePower a m)) p‖ ≤
    (2 : ℝ)^k * B * 1 at hb
  rw [mul_one] at hb
  exact hb

theorem linearCauchy_fullJet_bound {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I) (hI : IsOpen I)
    (a : ℝ) (k : ℕ) {p : Coord} (hp : p ∈ spatialStrip I) (ht : |p 1 - a| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (h0B : ∀ j ≤ k, ‖iteratedFDeriv ℝ j u0 (p 0)‖ ≤ B)
    (h1B : ∀ j ≤ k, ‖iteratedFDeriv ℝ j u1 (p 0)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (linearCauchy a u0 u1) p‖ ≤ (1 + (2 : ℝ)^k) * B := by
  have hf0 : ContDiffOn ℝ ∞ (fun q : Coord => u0 (q 0)) (spatialStrip I) :=
    h0.comp (contDiffOn_apply ℝ ℝ 0 _) (fun _ hp => hp)
  have hf1 := separatedProduct_contDiffOn h1 _ (normalizedTimePower_contDiff a 1)
  have he : linearCauchy a u0 u1 = (fun q => u0 (q 0)) +
      separatedProduct u1 (normalizedTimePower a 1) := by
    funext q
    simp [linearCauchy, separatedProduct, normalizedTimePower]
  rw [he, iteratedFDeriv_add_apply
    ((hf0.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hf1.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))]
  have hval := (norm_add_le _ _).trans (add_le_add
    ((spatialCoefficient_fullJet_le h0 hI hp k).trans (h0B k le_rfl))
    (separatedTimePower_fullJet_bound h1 hI a 1 k hp ht hB h1B))
  convert hval using 1
  first | rfl | ring

end SmoothLocal.Taylor

end

end OAI
