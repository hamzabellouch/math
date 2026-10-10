import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.VectorBesselTransfer
import OAI.Analysis.RieszRectifiability.Packing.BoundedDepthHaarBessel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem bounded_depth_cell_haar_vector_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z))
    (u : Ambient d → Ambient d) (hu : MemLp u 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, (P i).test x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤
      (I : ℝ) * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hp (i : SupportCellDescendant μ R hR k z) :=
    (P i).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  exact finite_vector_bessel_of_scalar (EuclideanSpace.basisFun (Fin d) ℝ) μ s
    (fun i => (P i).test) (fun i => (hp i).1) (I : ℝ)
    (fun v hv => bounded_depth_cell_haar_bessel μ C G hC hG hg hlower R hR k I hI z hcore P s v hv)
    u hu e he

theorem bounded_depth_vector_average_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z))
    (u : Ambient d → Ambient d) (hu : MemLp u 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, μ.real (P i).innerCell *
      (cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (u x)) -
        cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (u x))) ^ 2 ≤
      (I : ℝ) * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hp (i : SupportCellDescendant μ R hR k z) :=
    (P i).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  have heq (i : SupportCellDescendant μ R hR k z) :
      (∫ x, (P i).test x * inner ℝ (e i) (u x) ∂μ) ^ 2 = μ.real (P i).innerCell *
        (cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (u x)) -
          cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (u x))) ^ 2 := by
    rw [(hp i).2.2.2 _ (memLp_inner_const_of_vector μ u hu (e i)), mul_pow,
      Real.sq_sqrt measureReal_nonneg]
  have hb := bounded_depth_cell_haar_vector_bessel μ C G hC hG hg hlower R hR k I hI z hcore P s u hu e he
  simpa only [heq] using! hb

theorem bounded_depth_riesz_average_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z)) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (ε : ℝ) (hε : 0 < ε) (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, μ.real (P i).innerCell *
      (cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x)) -
        cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x))) ^ 2 ≤
      ((I : ℝ) * (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ := by
  obtain ⟨hT, hN⟩ := hRiesz ε hε f hf
  have hb := bounded_depth_vector_average_bessel μ C G hC hG hg hlower R hR k I hI z hcore
    P s (truncated n μ ε f) hT e he
  have hn := mul_le_mul_of_nonneg_left
    (vector_sq_integral_of_native_norm_bound μ f _ hf hT D hN) (Nat.cast_nonneg I)
  exact hb.trans (by simpa only [mul_assoc] using! hn)

end

end RieszRectifiability

end OAI
