import Mathlib.Algebra.Order.BigOperators.Expect
import OAI.Computability.UniqueGames.Inverse.EqualityFiber
import OAI.Computability.UniqueGames.Inverse.FactorSampling
import OAI.Computability.UniqueGames.Inverse.MatrixChartLemmas
import OAI.Computability.UniqueGames.Inverse.ShortcodeInterfaceLemmas

namespace OAI

section

/-! The actual uniform matrix test supplies a positive-mass output fiber with
large retention. The transition kernel averages independent full vectors,
including zero. -/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Information

def matrixWeight {ell m : ℕ} (_ : Mat ell m) : ℝ :=
  (Fintype.card (Mat ell m) : ℝ)⁻¹

theorem matrixWeight_probability (ell m : ℕ) :
    IsProbability (matrixWeight (ell := ell) (m := m)) := by
  constructor
  · intro M
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [matrixWeight, hcard]

def matrixKernel {ell m : ℕ} (M N : Mat ell m) : ℝ :=
  𝔼 a : Vector ell, 𝔼 l : Vector m,
    if N = M + rankOne a l then 1 else 0

theorem matrixKernel_nonneg {ell m : ℕ} (M N : Mat ell m) :
    0 ≤ matrixKernel M N := by
  apply Finset.expect_nonneg
  intro a _
  apply Finset.expect_nonneg
  intro l _
  split <;> norm_num

theorem matrixKernel_probability {ell m : ℕ} (M : Mat ell m) :
    IsProbability (matrixKernel M) := by
  refine ⟨matrixKernel_nonneg M, ?_⟩
  unfold matrixKernel
  rw [← Finset.expect_sum_comm]
  have hpoint (a : Vector ell) :
      (∑ N : Mat ell m, 𝔼 l : Vector m,
        if N = M + rankOne a l then (1 : ℝ) else 0) = 1 := by
    rw [← Finset.expect_sum_comm]
    simp
  simp only [hpoint]
  simp

theorem matrixKernel_equality {ell m : ℕ} (f : Mat ell m → Vector ell)
    (M : Mat ell m) :
    (∑ N, matrixKernel M N * if f M = f N then (1 : ℝ) else 0) =
      𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0 := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem equalityAcceptance_eq_kernel {ell m : ℕ} (f : Mat ell m → Vector ell) :
    equalityAcceptance f = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
  calc
    equalityAcceptance f = ∑ M, matrixWeight M *
        (𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then (1 : ℝ) else 0) := by
      unfold equalityAcceptance matrixWeight
      rw [Fintype.expect_eq_sum_div_card]
      simp only [div_eq_mul_inv, ← Finset.mul_sum, mul_comm]
    _ = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
      unfold EqualityFiber.equalityAcceptance
      apply Finset.sum_congr rfl
      intro M _
      congr 1
      convert (matrixKernel_equality f M).symm using 1
      apply Finset.sum_congr rfl
      intro N _
      by_cases h : f M = f N <;> simp [h]

/-- Positive-mass fibers, with their actual transition flow, are obtained from
the full uniform factor law. This is the first step before conditioning both
factors to be nonzero and passing to Grassmann neighbors. -/
theorem exists_output_fiber {ell m : ℕ} (f : Mat ell m → Vector ell)
    {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y : Vector ell, 0 < EqualityFiber.fiberMass matrixWeight f y ∧
      η ≤ EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
        EqualityFiber.fiberMass matrixWeight f y := by
  apply EqualityFiber.exists_fiber_retention matrixWeight matrixKernel
    (matrixWeight_probability ell m) matrixKernel_probability f
  rwa [← equalityAcceptance_eq_kernel]

end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

def matrixFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (Mat ell m) := Finset.univ.filter fun M => f M = y

def liftedFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (KMS.Vertex (ell + m) ell) := (matrixFiber f y).image matrixVertex

theorem liftedFiber_subset_chart {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    liftedFiber f y ⊆ matrixChart ell m := by
  intro L hL
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hL
  exact (mem_matrixChart _).mpr ⟨M, rfl⟩

@[simp] theorem matrixVertex_mem_liftedFiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    matrixVertex M ∈ liftedFiber f y ↔ f M = y := by
  constructor
  · intro h
    obtain ⟨N, hN, hNM⟩ := Finset.mem_image.mp h
    have : N = M := matrixVertex_injective hNM
    subst N
    exact (Finset.mem_filter.mp hN).2
  · intro h
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- The slice and the interval intersected with the chart correspond exactly.
The hypothesis states equality of the actual membership predicates. -/
theorem image_slice_points {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I) :
    S.points.image matrixVertex = I ∩ matrixChart ell m := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_inter.mpr ⟨(hS M).mp (Finset.mem_filter.mp hM).2,
      (mem_matrixChart _).mpr ⟨M, rfl⟩⟩
  · intro h
    obtain ⟨hI, hC⟩ := Finset.mem_inter.mp h
    obtain ⟨M, rfl⟩ := (mem_matrixChart _).mp hC
    exact Finset.mem_image.mpr ⟨M,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS M).mpr hI⟩, rfl⟩

theorem image_slice_fiber {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    (S.points.filter fun M => f M = y).image matrixVertex =
      liftedFiber f y ∩ (I ∩ matrixChart ell m) := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpoints, hfy⟩ := Finset.mem_filter.mp hM
    refine Finset.mem_inter.mpr ⟨(matrixVertex_mem_liftedFiber f y M).mpr hfy, ?_⟩
    rw [← image_slice_points S I hS]
    exact Finset.mem_image.mpr ⟨M, hpoints, rfl⟩
  · intro h
    obtain ⟨hf, hIC⟩ := Finset.mem_inter.mp h
    rw [← image_slice_points S I hS] at hIC
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hIC
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr
      ⟨hM, (matrixVertex_mem_liftedFiber f y M).mp hf⟩, rfl⟩

/-- Uniform agreement on a slice is the actual Grassmann fiber density in the
chart-intersected interval.  Empty sets are allowed on both sides of this
identity, with the standard zero-denominator convention. -/
theorem constantAgreement_eq_chart_density {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    S.constantAgreement f y =
      KMS.relativeDensity (liftedFiber f y) (I ∩ matrixChart ell m) := by
  unfold Slice.constantAgreement KMS.relativeDensity
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  rw [← image_slice_fiber S I hS f y, ← image_slice_points S I hS]
  simp only [Finset.card_image_of_injective _ matrixVertex_injective]

theorem hasAffineSlice_of_dense_interval {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (S : Slice ell m) (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    {α : ℝ} {r : ℕ} (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : (liftedFiber f y ∩ I).Nonempty)
    (hdense : α ≤ KMS.relativeDensity (liftedFiber f y) I) :
    HasAffineSlice f α r := by
  obtain ⟨hIC, hα⟩ := KMS.density_bound_passes_to_chart
    (liftedFiber f y) I (matrixChart ell m)
    (liftedFiber_subset_chart f y) hne hdense
  have hpoints : S.points.Nonempty := by
    rw [← image_slice_points S I hS] at hIC
    exact Finset.image_nonempty.mp hIC
  apply hasAffineSlice_of_constant f α r S hrows hcolumns hpoints y
  rw [constantAgreement_eq_chart_density S I hS f y]
  exact hα

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

/-! Exact finite output-fiber sampling identities. These connect the weighted
kernel extraction to uniform sampling of a matrix in the actual output fiber.
-/

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode UniqueGamesTheorem.Foundations.Information

theorem matrixKernel_average {ell m : ℕ} (M : Mat ell m) (g : Mat ell m → ℝ) :
    (∑ N, matrixKernel M N * g N) = 𝔼 a, 𝔼 l, g (M + rankOne a l) := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp [ite_mul]

theorem fiberMass_eq_card {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberMass matrixWeight f y =
      ((matrixFiber f y).card : ℝ) / Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberMass
  calc
    _ = ∑ M ∈ matrixFiber f y, matrixWeight M := by
      rw [matrixFiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _
      by_cases h : f M = y <;> simp [h]
    _ = _ := by simp [matrixWeight, div_eq_mul_inv]

theorem fiberMass_pos_iff {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    0 < EqualityFiber.fiberMass matrixWeight f y ↔ (matrixFiber f y).Nonempty := by
  rw [fiberMass_eq_card]
  have hcard : (0 : ℝ) < Fintype.card (Mat ell m) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right hcard, Nat.cast_pos, Finset.card_pos]

def fiberFactorRetention {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) (a : Vector ell) (l : Vector m) : ℝ :=
  (matrixFiber f y).expect fun M => if f (M + rankOne a l) = y then 1 else 0

theorem fiberFlow_eq {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y =
      (∑ M ∈ matrixFiber f y,
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) /
        Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberFlow
  simp_rw [matrixKernel_average]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [matrixFiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : f M = y
  · simp [h, matrixWeight, mul_comm]
  · simp [h]

theorem fiber_retention_eq_factor_average {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
      EqualityFiber.fiberMass matrixWeight f y =
        𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  rw [fiberFlow_eq, fiberMass_eq_card]
  have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hswap : (𝔼 a, 𝔼 l, fiberFactorRetention f y a l) =
      (matrixFiber f y).expect (fun M =>
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
    unfold fiberFactorRetention
    calc
      _ = 𝔼 a, (matrixFiber f y).expect (fun M =>
          𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
        apply Finset.expect_congr rfl
        intro a _
        rw [Finset.expect_comm]
      _ = _ := Finset.expect_comm _ _ _
  rw [hswap, Finset.expect_eq_sum_div_card]
  simp [div_div_div_cancel_right₀ hcard]

theorem fiberFactorRetention_zero_left {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (l : Vector m) :
    fiberFactorRetention f y 0 l = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne (0 : Vector ell) l) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

theorem fiberFactorRetention_zero_right {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (a : Vector ell) :
    fiberFactorRetention f y a 0 = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne a (0 : Vector m)) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

/-- A nonempty actual output fiber whose retention under the full factor law
is at least the original equality acceptance threshold. -/
theorem exists_output_fiber_factor_retention {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧ η ≤ 𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  obtain ⟨y, hy, hret⟩ := Shortcode.exists_output_fiber f haccept
  exact ⟨y, (fiberMass_pos_iff f y).mp hy,
    by simpa only [fiber_retention_eq_factor_average] using hret⟩

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
