import OAI.Analysis.Pureness.Projections.QuotientSpectralBands

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientSpectralBand_telescope (x : selfAdjoint (T.CauchyQuotient hadd)) (t : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, T.quotientSpectralBand hadd hsqrt x (t i) (t (i+1))) =
      T.quotientSpectralCut hadd hsqrt x (t 0)-T.quotientSpectralCut hadd hsqrt x (t N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    dsimp [quotientSpectralBand]
    abel

lemma quotientSpectralBand_partition (x : selfAdjoint (T.CauchyQuotient hadd)) (t : ℕ → ℝ)
    (ht : Monotone t) (N : ℕ) (hl : t 0 < -‖x.1‖) (hu : ‖x.1‖ < t N) :
    (∀ i, 0 ≤ T.quotientSpectralBand hadd hsqrt x (t i) (t (i+1))) ∧
    (∀ i j, i ≠ j → T.quotientSpectralBand hadd hsqrt x (t i) (t (i+1))*
      T.quotientSpectralBand hadd hsqrt x (t j) (t (j+1))=0) ∧
    (∑ i ∈ Finset.range N, T.quotientSpectralBand hadd hsqrt x (t i) (t (i+1)))=1 := by
  refine ⟨fun i => (T.quotientSpectralBand_spec hadd hsqrt x (ht (Nat.le_succ i))).2.2.1, ?_, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact T.quotientSpectralBand_orthogonal hadd hsqrt x (ht (Nat.le_succ i))
        (ht h) (ht (Nat.le_succ j))
    · rw [(T.quotientSpectralBands_commute hadd hsqrt x x (Commute.refl _) _ _ _ _).eq]
      exact T.quotientSpectralBand_orthogonal hadd hsqrt x (ht (Nat.le_succ j))
        (ht h) (ht (Nat.le_succ i))
  · rw [T.quotientSpectralBand_telescope,T.quotientSpectralCut_below_neg_norm hadd hsqrt x hl,
      T.quotientSpectralCut_above_norm hadd hsqrt x hu,sub_zero]

lemma quotientSpectralBand_approximation (x : selfAdjoint (T.CauchyQuotient hadd))
    (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) (hl : t 0 < -‖x.1‖) (hu : ‖x.1‖ < t N)
    {δ : ℝ} (hδ : 0 ≤ δ) (hstep : ∀ i, t (i+1)-t i ≤ δ) :
    ‖x.1 - ∑ i ∈ Finset.range N, t i • T.quotientSpectralBand hadd hsqrt x (t i) (t (i+1))‖ ≤ δ := by
  let e := fun i => T.quotientSpectralBand hadd hsqrt x (t i) (t (i+1))
  have hp := T.quotientSpectralBand_partition hadd hsqrt x t ht N hl hu
  have he : (∑ i ∈ Finset.range N, e i)=1 := hp.2.2
  have hsum : (∑ i ∈ Finset.range N, e i*x.1)=x.1 := by
    rw [←Finset.sum_mul,hp.2.2,one_mul]
  have hb i : t i • e i ≤ e i*x.1 ∧ e i*x.1 ≤ t (i+1) • e i :=
    T.quotientSpectralBand_bounds hadd hsqrt x (ht (Nat.le_succ i))
  have hpos : 0 ≤ x.1-∑ i ∈ Finset.range N, t i • e i := by
    apply sub_nonneg.mpr
    rw [←hsum]
    exact Finset.sum_le_sum (fun i _ => (hb i).1)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hδ hpos).mpr
  rw [Algebra.algebraMap_eq_smul_one]
  have hi i : e i*x.1-t i • e i ≤ δ • e i := by
    calc
      e i*x.1-t i • e i ≤ t (i+1) • e i-t i • e i := sub_le_sub_right (hb i).2 _
      _ = (t (i+1)-t i) • e i := (sub_smul _ _ _).symm
      _ ≤ δ • e i := by
        have hn : 0 ≤ (δ - (t (i+1) - t i)) • e i :=
          (Positive.smul ⟨δ - (t (i+1) - t i), sub_nonneg.mpr (hstep i)⟩
            ⟨e i, hp.1 i⟩).2
        exact sub_nonneg.mp (hn.trans_eq (sub_smul δ (t (i+1) - t i) (e i)))
  have h := Finset.sum_le_sum (s := Finset.range N) (fun i _ => hi i)
  simp only [Finset.sum_sub_distrib,hsum,←Finset.smul_sum,he] at h
  exact h
end CuntzPureness.PositiveQuasitrace

end

end OAI
