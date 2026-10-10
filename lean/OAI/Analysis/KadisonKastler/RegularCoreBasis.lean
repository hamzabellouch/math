import OAI.Analysis.KadisonKastler.RegularCoreHilbertSum
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Basic.Denumerable
import Mathlib.Algebra.Order.Interval.Set.Group

namespace OAI

/-! # A countable scalar basis for the real regular space

Disjoint unit intervals supply an infinite orthonormal set. A maximal
orthonormal extension is countable by separability, hence can be indexed
by the natural numbers. No representation-theoretic input is used.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology InnerProductSpace ENNReal

noncomputable section

private def regularIntervalVector (n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (s := Set.Ioc (n : ℝ) ((n : ℝ) + 1)) measurableSet_Ioc
    (by simp [Real.volume_Ioc]) (1 : ℂ)

private theorem regularIntervalVector_orthonormal :
    Orthonormal ℂ regularIntervalVector := by
  constructor
  · intro n
    rw [regularIntervalVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [measureReal_def, Real.volume_Ioc]
  · intro i j hij
    have hd : Disjoint (Set.Ioc (i : ℝ) ((i : ℝ) + 1))
        (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) := by
      simpa only [zero_add] using Set.pairwise_disjoint_Ioc_add_intCast (0 : ℝ) hij
    rw [regularIntervalVector, regularIntervalVector,
      L2.inner_indicatorConstLp_one_indicatorConstLp_one measurableSet_Ioc measurableSet_Ioc
        (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioc])]
    simp [Set.disjoint_iff_inter_eq_empty.mp hd]

private theorem orthonormal_countable
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [TopologicalSpace.SeparableSpace E] {v : ι → E} (hv : Orthonormal ℂ v) :
    Countable ι := by
  have hsep (i j : ι) (hij : i ≠ j) : 1 ≤ dist (v i) (v j) := by
    have hs : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hv.norm_eq_one i, hv.norm_eq_one j,
        hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1 / 2 : ℝ))
      (Metric.ball (v j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using hsep i j hij
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- The scalar real-line `L²` space has an actual natural-number Hilbert basis. -/
theorem exists_regularScalarBasis :
    Nonempty (HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨w, b, hsub, _hb⟩ :=
    regularIntervalVector_orthonormal.toSubtypeRange.exists_hilbertBasis_extension
  let : Countable w := orthonormal_countable b.orthonormal
  have hw : w.Infinite :=
    (Set.infinite_range_of_injective
      regularIntervalVector_orthonormal.linearIndependent.injective).mono hsub
  let : Infinite w := hw.to_subtype
  let : Encodable w := Encodable.ofCountable w
  let : Denumerable w := Denumerable.ofEncodableOfInfinite w
  let e : ℕ ≃ w := (Denumerable.eqv w).symm
  have ho : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e e.injective
  refine ⟨HilbertBasis.mk ho ?_⟩
  have hr : Set.range (b ∘ e) = Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  rw [hr, b.dense_span]

/-- One fixed scalar basis; its only role is to select Hilbert coordinates. -/
def regularScalarBasis : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  Classical.choice exists_regularScalarBasis

end

end KadisonKastler

end OAI
