import Mathlib.Algebra.Order.Archimedean.Real.Basic
import OAI.Computability.UniqueGames.Inverse.MatrixChartIntervalsLemmas
import OAI.Computability.UniqueGames.Inverse.ShortcodeFiberConditioning
import OAI.Computability.UniqueGames.Inverse.ShortcodeFiberLemmas
import OAI.Computability.UniqueGames.Inverse.ShortcodeInterfaceLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

/-- The exact self-loop mass when independent uniform binary factors include
zero. The overlap of the two zero events is subtracted once. -/
def zeroFactorMass (ell m : ℕ) : ℝ :=
  ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹

/-- A common lower bound on both dimensions makes the zero-factor probability
as small as required. This threshold depends only on the acceptance parameter.
-/
theorem exists_zeroFactorMass_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ ell m : ℕ, N ≤ ell → N ≤ m → zeroFactorMass ell m ≤ η / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < η / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro ell m hell hm
  have hpow (n : ℕ) (hn : N ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ η / 4 := by
    have hmon : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    simpa only [one_div, inv_pow] using hmon.trans hN.le
  have hell' := hpow ell hell
  have hm' := hpow m hm
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (ell + m))⁻¹ := by positivity
  unfold zeroFactorMass
  linarith

/-- OPEN finite sampling bridge, stated on the actual equality test, actual
lifted output fibers, and actual Grassmann retention. The positive dimensions
exclude the degenerate empty-neighbor cases. No KMS or inverse principle is
part of this proposition. -/
def ChartFiberRetention : Prop :=
  ∀ {ell m : ℕ}, 1 ≤ ell → 1 ≤ m →
    ∀ η : ℝ, 0 < η → η < 1 → zeroFactorMass ell m ≤ η / 2 →
      ∀ f : Mat ell m → Vector ell, η ≤ equalityAcceptance f →
        ∃ y : Vector ell, (liftedFiber f y).Nonempty ∧
          η / 4 ≤ KMS.retention (liftedFiber f y)

theorem inversePrinciple_of_expansion_and_chart
    (hKMS : KMS.ExpansionPrinciple) (hChart : ChartFiberRetention) :
    InversePrinciple := by
  intro η hη hη1
  obtain ⟨α, hαpos, hαone, r, hr, ellKMS, hKMSell⟩ :=
    hKMS (η / 4) (by positivity) (by linarith)
  obtain ⟨N, hN⟩ := exists_zeroFactorMass_threshold hη
  refine ⟨α, hαpos, hαone, r, hr, max ellKMS (max 1 N), ?_⟩
  intro ell hell
  have hellKMS : ellKMS ≤ ell := (le_max_left _ _).trans hell
  have hellone : 1 ≤ ell := (le_max_left 1 N).trans ((le_max_right _ _).trans hell)
  have hellN : N ≤ ell := (le_max_right 1 N).trans ((le_max_right _ _).trans hell)
  obtain ⟨nKMS, hKMSn⟩ := hKMSell ell hellKMS
  refine ⟨max nKMS (max 1 N), ?_⟩
  intro m hm f haccept
  have hmKMS : nKMS ≤ m := (le_max_left _ _).trans hm
  have hmone : 1 ≤ m := (le_max_left 1 N).trans ((le_max_right _ _).trans hm)
  have hmN : N ≤ m := (le_max_right 1 N).trans ((le_max_right _ _).trans hm)
  obtain ⟨y, hnonempty, hretention⟩ :=
    hChart hellone hmone η hη hη1 (hN ell m hellN hmN) f haccept
  obtain ⟨A, B, _hAB, hbudget, hintersection, hdense⟩ :=
    hKMSn (ell + m) (by omega) (liftedFiber f y) hnonempty hretention
  change Module.finrank (ZMod 2) A +
    ((ell + m) - Module.finrank (ZMod 2) B) ≤ r at hbudget
  obtain ⟨S, hrows, hcolumns, hcontains⟩ := exists_shortcode_slice A B
  apply hasAffineSlice_of_dense_interval f y (KMS.interval A B) S
  · intro M
    simpa only [KMS.interval, Finset.mem_filter, Finset.mem_univ, true_and]
      using hcontains M
  · omega
  · omega
  · exact hintersection
  · exact hdense

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

/-!
The exact finite sampling conversion in the v2 shortcode proof. Independent
nonzero binary vector factors parametrize chart neighbors bijectively; the full
Grassmann degree is twice the chart degree. These identities imply the exact
factor one half, including its averaging over a nonempty output fiber.
-/

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- Relative density is uniform expectation on the predicate subtype. -/
theorem relativeDensity_filter_eq_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (P : Ω → Prop) [DecidablePred P] :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- Lifting a finite set along an injection preserves its uniform starting
law. No regularity or nonempty-neighbor hypothesis is needed for this step. -/
theorem retention_image {X : Type*} [DecidableEq X] {n ell : ℕ}
    (S : Finset X) (e : X → KMS.Vertex n ell) (he : Function.Injective e) :
    KMS.retention (S.image e) =
      S.expect fun x => KMS.relativeDensity (S.image e) (KMS.neighbors (e x)) := by
  have h : KMS.retention (S.image e) =
      (S.image e).expect fun L => KMS.relativeDensity (S.image e) (KMS.neighbors L) := by
    rw [Finset.expect_eq_sum_div_card]
    rfl
  rw [h]
  exact Finset.expect_image he.injOn

/-- At every starting matrix the full-neighbor retention is half the uniform
nonzero-factor retention. This follows from exact finite bijections and degree
counts; the zero-factor law is handled separately before this theorem. -/
theorem relativeDensity_neighbors_eq_nonzero_average_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M)) =
      (𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  let C := KMS.neighbors (matrixVertex M) ∩ matrixChart ell m
  have hC : C = Finset.univ.filter (fun L : KMS.Vertex (ell + m) ell =>
      KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m) := by
    ext L
    simp [C, KMS.neighbors]
  have hcardC : C.card = (2 ^ ell - 1) * (2 ^ m - 1) := by
    rw [hC]
    have h := card_matrixVertexChartNeighbors M
    simpa only [MatrixVertexChartNeighbors, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using h
  have hcard : (KMS.neighbors (matrixVertex M)).card = 2 * C.card := by
    rw [hcardC]
    exact card_full_neighbors_twice M
  have hnumerator : liftedFiber f y ∩ C =
      liftedFiber f y ∩ KMS.neighbors (matrixVertex M) :=
    KMS.inter_chart_eq _ _ _ (liftedFiber_subset_chart f y)
  have hhalf : KMS.relativeDensity (liftedFiber f y)
      (KMS.neighbors (matrixVertex M)) =
        KMS.relativeDensity (liftedFiber f y) C / 2 := by
    unfold KMS.relativeDensity
    rw [hcard, ← hnumerator, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm (2 : ℝ), div_mul_eq_div_div]
  rw [hhalf]
  congr 1
  rw [hC]
  trans (𝔼 L : MatrixVertexChartNeighbors M,
    if L.val ∈ liftedFiber f y then (1 : ℝ) else 0)
  · exact relativeDensity_filter_eq_expect (liftedFiber f y)
      (fun L => KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m)
  symm
  apply Fintype.expect_equiv (vectorFactorsEquivMatrixVertexChartNeighbors M)
  intro p
  simp only [vectorFactorsEquivMatrixVertexChartNeighbors_apply,
    matrixVertex_mem_liftedFiber]

/-- The exact Grassmann retention of an output fiber is half its retention
under independent uniform nonzero vector factors. Empty fibers and degenerate
dimensions also satisfy this identity with zero-expectation conventions. -/
theorem liftedFiber_retention_eq_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    KMS.retention (liftedFiber f y) =
      (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  unfold liftedFiber
  rw [retention_image _ _ matrixVertex_injective]
  change (𝔼 M ∈ matrixFiber f y,
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M))) = _
  simp_rw [relativeDensity_neighbors_eq_nonzero_average_half]
  exact (Finset.expect_div _ _ _).symm

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- The finite sampling bridge has no expansion or inverse premise. -/
theorem chartFiberRetention : ChartFiberRetention := by
  intro ell m _hell _hm η hη hη1 hzero f haccept
  obtain ⟨y, hnonempty, hretention⟩ :=
    conditioned_output_fiber f hη hη1 hzero haccept
  refine ⟨y, ?_, ?_⟩
  · exact Finset.image_nonempty.mpr hnonempty
  · rw [liftedFiber_retention_eq_half]
    have h : η / 2 ≤ (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := hretention
    linarith

/-- Conditional Grassmann-to-matrix implication, preserving all quantifiers
and the affine target. KMS expansion is the sole remaining displayed premise.
-/
theorem inversePrinciple_of_expansion (hKMS : KMS.ExpansionPrinciple) :
    Shortcode.InversePrinciple :=
  inversePrinciple_of_expansion_and_chart hKMS chartFiberRetention

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
