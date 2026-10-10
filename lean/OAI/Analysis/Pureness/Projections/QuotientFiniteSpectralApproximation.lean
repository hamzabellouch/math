import OAI.Analysis.Pureness.Projections.QuotientSpectralPartition

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in

lemma exists_quotient_finite_spectral_approximation (x : selfAdjoint (T.CauchyQuotient hadd))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (e : ℕ → T.CauchyQuotient hadd) (r : ℕ → ℝ),
      (∀ i, IsSelfAdjoint (e i) ∧ e i*e i=e i ∧ 0 ≤ e i) ∧
      (∀ i j, i ≠ j → e i*e j=0) ∧
      (∑ i ∈ Finset.range N, e i)=1 ∧
      (∀ i y, Commute x.1 y → Commute (e i) y) ∧
      ‖x.1-∑ i ∈ Finset.range N, r i • e i‖ < ε := by
  let C := ‖x.1‖+1
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C/δ)
  let t : ℕ → ℝ := fun i => -C+(i:ℝ)*δ
  have ht : Monotone t := by
    intro i j hij
    dsimp [t]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hδ.le)
  have hl : t 0 < -‖x.1‖ := by dsimp [t,C]; norm_num
  have hu : ‖x.1‖ < t N := by
    have hn := (div_lt_iff₀ hδ).mp hN
    dsimp [t,C,δ] at *
    nlinarith [norm_nonneg x.1]
  let e := fun i => T.quotientSpectralBand hadd hsqrt x (t i) (t (i+1))
  have hp := T.quotientSpectralBand_partition hadd hsqrt x t ht N hl hu
  refine ⟨N,e,t,?_,hp.2.1,hp.2.2,?_,?_⟩
  · intro i
    have h := T.quotientSpectralBand_spec hadd hsqrt x (ht (Nat.le_succ i))
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · intro i y hy
    exact (T.quotientSpectralBand_spec hadd hsqrt x (ht (Nat.le_succ i))).2.2.2 y hy
  · have hb := T.quotientSpectralBand_approximation hadd hsqrt x t ht N hl hu hδ.le (by
      intro i
      dsimp [t]
      rw [Nat.cast_add,Nat.cast_one]
      linarith)
    exact hb.trans_lt (by dsimp [δ]; linarith)
end CuntzPureness.PositiveQuasitrace

end

end OAI
