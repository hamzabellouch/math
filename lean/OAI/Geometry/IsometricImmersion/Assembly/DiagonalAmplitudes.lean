import OAI.Geometry.IsometricImmersion.Assembly.FlatPatchSum

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set

namespace SmoothLocal.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem exists_positive_diagonal_amplitudes (f : ℕ → Coord → V)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun q => δ n • f n q) p‖ ≤ patchSeriesWeight ε n := by
  classical
  have hC (k n : ℕ) : ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ k (f n) p‖ ≤ C :=
    compactSmooth_has_derivative_bounds (f n) (hf n) (hc n) k
  choose C hC using hC
  let D : ℕ → ℝ := fun n => 1 + ∑ k ∈ Finset.range (n + 1), |C k n|
  have hD (n : ℕ) : 0 < D n := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (n + 1), |C k n| :=
      Finset.sum_nonneg (fun k _ => abs_nonneg (C k n))
    dsimp [D]
    linarith
  have hCD (n k : ℕ) (hkn : k ≤ n) : C k n ≤ D n := by
    have hk : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkn)
    have hs : |C k n| ≤ ∑ j ∈ Finset.range (n + 1), |C j n| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (C j n)) hk
    dsimp [D]
    linarith [le_abs_self (C k n)]
  let δ : ℕ → ℝ := fun n => patchSeriesWeight ε n / D n
  have hδ (n : ℕ) : 0 < δ n := div_pos (patchSeriesWeight_pos hε n) (hD n)
  refine ⟨δ, hδ, ?_⟩
  intro n k hkn p
  have hfn : ContDiffAt ℝ k (f n) p :=
    (hf n).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDeriv_const_smul_apply' hfn,
    norm_smul, Real.norm_of_nonneg (hδ n).le]
  calc
    δ n * ‖iteratedFDeriv ℝ k (f n) p‖ ≤ δ n * D n :=
      mul_le_mul_of_nonneg_left ((hC k n p).trans (hCD n k hkn)) (hδ n).le
    _ = patchSeriesWeight ε n := div_mul_cancel₀ _ (hD n).ne'

omit [CompleteSpace V] in
theorem tsupport_const_smul_eq_of_pos (f : Coord → V) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (fun p => δ • f p) = tsupport f := by
  change closure (Function.support (δ • f)) = closure (Function.support f)
  rw [Function.support_const_smul_of_ne_zero δ f hδ.ne']

theorem exists_small_flat_accumulating_profile_sum (f : ℕ → Coord → V)
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hsupp : ∀ n, tsupport (f n) ⊆ enlargedAccumulatingDisk n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      (∀ n, tsupport (fun p => δ n • f n p) = tsupport (f n)) ∧
      (∀ p, Summable (fun n => δ n • f n p)) ∧
      ContDiff ℝ ∞ (flatPatchSum (fun n p => δ n • f n p)) ∧
      (∀ p, ‖flatPatchSum (fun n q => δ n • f n q) p‖ ≤ ε) ∧
      (∀ k : ℕ, iteratedFDeriv ℝ k
        (flatPatchSum (fun n p => δ n • f n p)) (0 : Coord) = 0) := by
  have hc := hasCompactSupport_of_accumulatingDisk_support f hsupp
  obtain ⟨δ, hδ, hb⟩ := exists_positive_diagonal_amplitudes f hf hc ε hε
  have hs (n : ℕ) : tsupport (fun p => δ n • f n p) = tsupport (f n) :=
    tsupport_const_smul_eq_of_pos (f n) (hδ n)
  have hsum := accumulatingDisk_flat_sum (fun n p => δ n • f n p) ε
    (fun n => (hf n).const_smul (δ n))
    (fun n => by rw [hs n]; exact hsupp n) hb
  exact ⟨δ, hδ, hs, hsum.1, hsum.2.1, hsum.2.2.1, hsum.2.2.2⟩

end SmoothLocal.Geometry

end

end OAI
