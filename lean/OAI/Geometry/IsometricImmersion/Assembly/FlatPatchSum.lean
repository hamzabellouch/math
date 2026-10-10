import OAI.Geometry.IsometricImmersion.Assembly.AccumulatingDisks
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set

namespace SmoothLocal.Geometry

def patchSeriesWeight (ε : ℝ) (n : ℕ) : ℝ := ε / 2 / (2 : ℝ) ^ n

theorem patchSeriesWeight_hasSum (ε : ℝ) : HasSum (patchSeriesWeight ε) ε :=
  hasSum_geometric_two' ε

theorem patchSeriesWeight_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < patchSeriesWeight ε n := by
  unfold patchSeriesWeight
  positivity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def flatPatchSum (f : ℕ → Coord → V) (p : Coord) : V := ∑' n, f n p

omit [CompleteSpace V] in
theorem compactSmooth_has_derivative_bounds (f : Coord → V)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ k f p‖ ≤ C :=
  (hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
    (hc.iteratedFDeriv k)

omit [CompleteSpace V] in
theorem exists_summable_derivative_majorant (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) :
    ∃ v : ℕ → ℕ → ℝ, (∀ k, Summable (v k)) ∧
      ∀ k n p, ‖iteratedFDeriv ℝ k (f n) p‖ ≤ v k n := by
  classical
  have hC (k n : ℕ) : ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ k (f n) p‖ ≤ C :=
    compactSmooth_has_derivative_bounds (f n) (hf n) (hc n) k
  choose C hC using hC
  let v : ℕ → ℕ → ℝ := fun k n => if k ≤ n then patchSeriesWeight ε n else C k n
  refine ⟨v, ?_, ?_⟩
  · intro k
    apply (patchSeriesWeight_hasSum ε).summable.congr_atTop
    filter_upwards [eventually_ge_atTop k] with n hn
    simp only [v, ite_eq_left hn]
  · intro k n p
    by_cases hkn : k ≤ n
    · simpa only [v, ite_eq_left hkn] using hbound n k hkn p
    · simpa only [v, ite_eq_right hkn] using hC k n p

theorem flatPatchSum_summable (f : ℕ → Coord → V) (ε : ℝ)
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) (p : Coord) :
    Summable (fun n => f n p) := by
  apply Summable.of_norm_bounded (patchSeriesWeight_hasSum ε).summable
  intro n
  simpa only [norm_iteratedFDeriv_zero] using hbound n 0 (Nat.zero_le n) p

omit [CompleteSpace V] in
theorem flatPatchSum_norm_le (f : ℕ → Coord → V) (ε : ℝ)
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) (p : Coord) :
    ‖flatPatchSum f p‖ ≤ ε := by
  apply tsum_of_norm_bounded (patchSeriesWeight_hasSum ε)
  intro n
  simpa only [norm_iteratedFDeriv_zero] using hbound n 0 (Nat.zero_le n) p

theorem flatPatchSum_contDiff (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) :
    ContDiff ℝ ∞ (flatPatchSum f) := by
  obtain ⟨v, hv, hfv⟩ := exists_summable_derivative_majorant f ε hf hc hbound
  exact contDiff_tsum (N := ⊤) hf (fun k _ => hv k) (fun k n p _ => hfv k n p)

theorem flatPatchSum_iteratedFDeriv (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n)
    (k : ℕ) (p : Coord) :
    iteratedFDeriv ℝ k (flatPatchSum f) p = ∑' n, iteratedFDeriv ℝ k (f n) p := by
  obtain ⟨v, hv, hfv⟩ := exists_summable_derivative_majorant f ε hf hc hbound
  exact iteratedFDeriv_tsum_apply (N := ⊤) hf (fun k _ => hv k)
    (fun k n p _ => hfv k n p) (by simp) p

theorem flatPatchSum_derivatives_tendstoUniformly (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) (k : ℕ) :
    TendstoUniformly (fun N : ℕ => fun p =>
      ∑ n ∈ Finset.range N, iteratedFDeriv ℝ k (f n) p)
      (iteratedFDeriv ℝ k (flatPatchSum f)) atTop := by
  obtain ⟨v, hv, hfv⟩ := exists_summable_derivative_majorant f ε hf hc hbound
  have heq : iteratedFDeriv ℝ k (flatPatchSum f) =
      (fun p => ∑' n, iteratedFDeriv ℝ k (f n) p) := by
    funext p
    exact flatPatchSum_iteratedFDeriv f ε hf hc hbound k p
  rw [heq]
  exact tendstoUniformly_tsum_nat (hv k) (fun n p => hfv k n p)

theorem flatPatchSum_all_jets_zero (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n)
    {p : Coord} (hp : ∀ n, p ∉ tsupport (f n)) (k : ℕ) :
    iteratedFDeriv ℝ k (flatPatchSum f) p = 0 := by
  rw [flatPatchSum_iteratedFDeriv f ε hf hc hbound k p]
  have hz (n : ℕ) : iteratedFDeriv ℝ k (f n) p = 0 := by
    by_contra hne
    exact hp n ((support_iteratedFDeriv_subset (𝕜 := ℝ) k) hne)
  simp only [hz, tsum_zero]

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem hasCompactSupport_of_accumulatingDisk_support (f : ℕ → Coord → V)
    (hsupp : ∀ n, tsupport (f n) ⊆ enlargedAccumulatingDisk n) (n : ℕ) :
    HasCompactSupport (f n) :=
  (enlargedAccumulatingDisk_isCompact n).of_isClosed_subset
    (isClosed_tsupport (f n)) (hsupp n)

theorem accumulatingDisk_flat_sum (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hsupp : ∀ n, tsupport (f n) ⊆ enlargedAccumulatingDisk n)
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) :
    (∀ p, Summable (fun n => f n p)) ∧ ContDiff ℝ ∞ (flatPatchSum f) ∧
      (∀ p, ‖flatPatchSum f p‖ ≤ ε) ∧
      (∀ k : ℕ, iteratedFDeriv ℝ k (flatPatchSum f) (0 : Coord) = 0) := by
  have hc := hasCompactSupport_of_accumulatingDisk_support f hsupp
  refine ⟨flatPatchSum_summable f ε hbound,
    flatPatchSum_contDiff f ε hf hc hbound,
    flatPatchSum_norm_le f ε hbound, ?_⟩
  intro k
  apply flatPatchSum_all_jets_zero f ε hf hc hbound _ k
  intro n hn
  exact zero_not_mem_enlargedAccumulatingDisk n (hsupp n hn)

end SmoothLocal.Geometry

end

end OAI
