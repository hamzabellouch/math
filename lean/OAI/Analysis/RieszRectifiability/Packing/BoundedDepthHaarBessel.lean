import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.CellHaarOrthogonality
import OAI.Analysis.RieszRectifiability.Packing.CoarseLevelPacking

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem finite_L2_bessel_of_orthogonal_unit_bounds {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (hdiag : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ 1)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∫ x, f i x * f j x ∂μ) = 0)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ ∫ x, u x ^ 2 ∂μ := by
  classical
  have hrow : ∀ i ∈ s, ∑ j ∈ s, |∫ x, f i x * f j x ∂μ| * (1 : ℝ) ≤ 1 * 1 := by
    intro i hi
    simp only [mul_one]
    rw [Finset.sum_eq_single i
      (fun j hj hne => by rw [horth i hi j hj hne.symm, abs_zero])
      (fun hnot => False.elim (hnot hi))]
    rw [abs_of_nonneg (integral_nonneg (fun x => mul_self_nonneg (f i x)))]
    simpa only [pow_two] using! hdiag i hi
  simpa only [one_mul] using! finite_L2_bessel_of_weighted_pairings μ s f hf
    (fun _ => 1) 1 (by norm_num) (fun _ _ => by norm_num) hrow u hu

theorem finite_L2_bessel_of_level_classes {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (level : ι → ℕ) (I : ℕ) (hI : 0 < I)
    (hdiag : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ 1)
    (horth : ∀ i ∈ s, ∀ j ∈ s, level i % I = level j % I → i ≠ j →
      (∫ x, f i x * f j x ∂μ) = 0)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ (I : ℝ) * ∫ x, u x ^ 2 ∂μ := by
  classical
  apply finite_sum_of_bounded_level_slices s (fun i => level i % I)
    (fun i => (∫ x, f i x * u x ∂μ) ^ 2) I (∫ x, u x ^ 2 ∂μ)
    (fun i _ => Nat.mod_lt (level i) hI)
  intro q _
  exact finite_L2_bessel_of_orthogonal_unit_bounds μ (s.filter (fun i => level i % I = q)) f hf
    (fun i hi => hdiag i (Finset.mem_filter.mp hi).1)
    (fun i hi j hj hne => horth i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hne) u hu

theorem bounded_depth_cell_haar_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z))
    (u : Ambient d → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, (P i).test x * u x ∂μ) ^ 2 ≤ (I : ℝ) * ∫ x, u x ^ 2 ∂μ := by
  have hp (i : SupportCellDescendant μ R hR k z) :=
    (P i).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  exact finite_L2_bessel_of_level_classes μ s (fun i => (P i).test) (fun i => (hp i).1)
    (fun i => i.depth) I hI (fun i _ => (hp i).2.2.1)
    (fun i _ j _ hmod hne => bounded_depth_cell_haar_orthogonal μ C G hC hG hg hlower
      R hR k I z hcore P i j hmod hne) u hu

end

end RieszRectifiability

end OAI
