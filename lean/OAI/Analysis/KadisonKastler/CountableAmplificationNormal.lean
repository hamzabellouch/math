import OAI.Analysis.KadisonKastler.CanonicalAmplification
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! # Normality and separating vectors for countable amplification

Bounded weak operator limits pass through the countable diagonal action.
A weighted dense sequence is a separating vector for that action. These
are the concrete ingredients for a faithful cyclic representation.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem l2Diagonal_tendsto_weak {ι : Type*} {l : Filter ι}
    (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hT : ∀ x y : H, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (S x))))
    (x y : CountableHilbertSum H) :
    Tendsto (fun i => inner ℂ y (l2Diagonal (T i) x)) l
      (𝓝 (inner ℂ y (l2Diagonal S x))) := by
  simp only [lp.inner_eq_tsum, l2Diagonal_apply]
  apply tendsto_tsum_of_dominated_convergence
    ((lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num) y x).mul_left C)
    (fun n => hT (x n) (y n))
  filter_upwards [hC] with i hi n
  calc
    ‖inner ℂ (y n) (T i (x n))‖ ≤ ‖y n‖ * ‖T i (x n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖y n‖ * (C * ‖x n‖) := mul_le_mul_of_nonneg_left
      ((T i).le_opNorm (x n) |>.trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _)))
      (norm_nonneg _)
    _ = C * (‖y n‖ * ‖x n‖) := by ring

instance countableHilbertSum_separable [SeparableSpace H] :
    SeparableSpace (CountableHilbertSum H) := by
  let s : Set (CountableHilbertSum H) :=
    ⋃ n : ℕ, Set.range (lp.single (E := fun _ : ℕ => H) 2 n)
  have hs : IsSeparable s := .iUnion fun n => isSeparable_range
    ((lp.isometry_single (E := fun _ : ℕ => H) (p := 2) n).continuous)
  have hd : Dense (Submodule.span ℂ s : Set (CountableHilbertSum H)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) x)
    apply Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro n _
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨n, ⟨x n, rfl⟩⟩)
  apply isSeparable_univ_iff.mp
  rw [← hd.closure_eq]
  exact hs.span.closure

variable [SeparableSpace H]

def denseSequenceWeight (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (1 + ‖denseSeq H n‖)

omit [InnerProductSpace ℂ H] in
theorem denseSequenceWeight_pos (n : ℕ) : 0 < denseSequenceWeight (H := H) n := by
  unfold denseSequenceWeight
  positivity

theorem norm_weighted_denseSeq_le (n : ℕ) :
    ‖(denseSequenceWeight (H := H) n : ℂ) • denseSeq H n‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (denseSequenceWeight_pos n)]
  unfold denseSequenceWeight
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

def weightedDenseVector : CountableHilbertSum H :=
  ⟨fun n => (denseSequenceWeight (H := H) n : ℂ) • denseSeq H n, by
    have hg : Memℓp (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
      apply memℓp_gen
      have h := summable_geometric_of_lt_one (r := (1 / 2 : ℝ) ^ 2)
        (by positivity) (by norm_num)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
        abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← pow_mul,
        Nat.mul_comm] using h
    exact hg.mono (norm_weighted_denseSeq_le (H := H))⟩

theorem weightedDenseVector_separating (T : H →L[ℂ] H)
    (hT : l2Diagonal T (weightedDenseVector (H := H)) = 0) : T = 0 := by
  apply DFunLike.ext'
  apply (denseRange_denseSeq H).equalizer T.continuous continuous_const
  funext n
  have h := congrArg (fun x : CountableHilbertSum H => x n) hT
  change T ((denseSequenceWeight (H := H) n : ℂ) • denseSeq H n) = 0 at h
  rw [map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left
    (by exact_mod_cast (denseSequenceWeight_pos (H := H) n).ne')

variable [Nontrivial H]

theorem weightedDenseVector_ne_zero : weightedDenseVector (H := H) ≠ 0 := by
  intro h
  have he : (1 : H →L[ℂ] H) = 0 := weightedDenseVector_separating _ (by
    rw [h, map_zero])
  exact one_ne_zero he

def denseSeparatingUnitVector : CountableHilbertSum H :=
  ((‖weightedDenseVector (H := H)‖⁻¹ : ℝ) : ℂ) • weightedDenseVector

theorem norm_denseSeparatingUnitVector : ‖denseSeparatingUnitVector (H := H)‖ = 1 := by
  rw [denseSeparatingUnitVector, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr weightedDenseVector_ne_zero)]

theorem denseSeparatingUnitVector_separating (T : H →L[ℂ] H)
    (hT : l2Diagonal T (denseSeparatingUnitVector (H := H)) = 0) : T = 0 := by
  apply weightedDenseVector_separating
  rw [denseSeparatingUnitVector, map_smul] at hT
  exact (smul_eq_zero.mp hT).resolve_left (by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr
      (weightedDenseVector_ne_zero (H := H))))

end

end KadisonKastler

end OAI
