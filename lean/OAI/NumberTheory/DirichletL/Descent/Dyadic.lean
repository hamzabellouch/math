import OAI.NumberTheory.DirichletL.Descent.Reconstruction
import OAI.NumberTheory.DirichletL.Descent.SieveComposition

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def hybridSquarePool (S : Finset (Ideal Eis × Ideal Eis)) : Finset (Ideal Eis) :=
  (hybridColumnSupport S).image HybridColumnData.square

def hybridCommonBlock (S : Finset (Ideal Eis × Ideal Eis)) (N : ℝ)
    (i : Fin (columnDyadicLength N + 1)) (t : Ideal Eis) : Finset HybridColumnData :=
  (hybridColumnSupport S).filter fun d =>
    d.square = t ∧ divisorDyadicLabel N d.common = i

theorem hybrid_dyadic_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (f : HybridColumnData → A) :
    (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ j : Fin (columnDyadicLength B + 1),
        ∑ i : Fin (columnDyadicLength N + 1),
          ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
            ∑ d ∈ hybridCommonBlock S N i t, f d := by
  have ht : (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ t ∈ hybridSquarePool S, ∑ d ∈ hybridColumnSupport S with d.square = t, f d := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) f
  rw [ht, sum_divisorDyadicBins (hybridSquarePool S) B]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hi := Finset.sum_fiberwise
    ((hybridColumnSupport S).filter fun d => d.square = t)
    (fun d => divisorDyadicLabel N d.common) f
  simpa only [Finset.filter_filter, hybridCommonBlock] using hi.symm

theorem hybridSquarePool_bounds (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (t : Ideal Eis) (ht : t ∈ hybridSquarePool S) :
    1 ≤ (Ideal.absNorm t : ℝ) ∧ (Ideal.absNorm t : ℝ) ≤ B := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
  have hb0 : (d.common * d.residualB) * d.square ^ 2 ≠ 0 :=
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero _ d.square_ne_zero)
  refine ⟨QuadraticMainBoundary.norm_one_le d.square_ne_zero, ?_⟩
  apply (QuadraticMainBoundary.norm_le_of_dvd hb0 ?_).trans
    (hS d.reconstruct ((mem_hybridColumnSupport S d).mp hd))
  exact dvd_mul_of_dvd_right (dvd_pow_self d.square (by norm_num : 2 ≠ 0)) _

theorem hybridSquarePool_bin_count (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) :
    ((divisorDyadicBin (hybridSquarePool S) B j).card : ℝ) ≤
      256 * divisorDyadicScale j.val := by
  have hscale := divisorDyadicScale_ge_one j.val
  have hb := divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B hS) j
  have hc := DescentFiberCost.finite_ideal_count_real
    (divisorDyadicBin (hybridSquarePool S) B j) (2 * divisorDyadicScale j.val)
    (by linarith) (fun t ht hz => by
      have hp := (hb t ht).1
      simp [hz] at hp
      linarith) (fun t ht => (hb t ht).2)
  linarith

theorem hybridCommonBlock_bounds
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B)
    (i : Fin (columnDyadicLength N + 1)) (j : Fin (columnDyadicLength B + 1))
    (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j)
    (d : HybridColumnData) (hd : d ∈ hybridCommonBlock S N i t) :
    let C := divisorDyadicScale i.val
    let T := divisorDyadicScale j.val
    C ≤ (Ideal.absNorm d.common : ℝ) ∧ (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
  have hs := hS d.reconstruct ((mem_hybridColumnSupport S d).mp hdS)
  have hc1 := QuadraticMainBoundary.norm_one_le d.common_ne_zero
  have hcn : (Ideal.absNorm d.common : ℝ) ≤ N :=
    (QuadraticMainBoundary.norm_le_of_dvd d.n_squarefree.ne_zero (dvd_mul_right _ _)).trans hs.1
  have hcb := divisorDyadicLabel_bounds N d.common hc1 hcn
  rw [hdi] at hcb
  have hcLow : divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) :=
    max_le hc1 hcb.1.le
  have hcHigh : (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val := by
    have hh : (2 : ℝ) ^ i.val / 2 ≤ divisorDyadicScale i.val := le_max_right _ _
    linarith [hcb.2]
  have htLow := (divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B (fun p hp => (hS p hp).2)) j t ht).1
  rw [← hdt] at htLow
  refine ⟨hcLow, hcHigh, ?_⟩
  exact d.residual_norm_bounds N B (divisorDyadicScale i.val) (divisorDyadicScale j.val)
    hN hB (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val]) hs.1 hs.2 hcLow htLow

theorem hybrid_square_dyad_energy
    (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) (rows : Finset (Ideal Eis))
    (F : Ideal Eis → Ideal Eis → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      (∑ k ∈ rows, ‖F t k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j, F t k‖ ^ 2) ≤
      (256 * divisorDyadicScale j.val) ^ 2 * E := by
  let Tset := divisorDyadicBin (hybridSquarePool S) B j
  have hc := hybridSquarePool_bin_count S B hS j
  calc
    _ ≤ (Tset.card : ℝ) * ∑ t ∈ Tset, ∑ k ∈ rows, ‖F t k‖ ^ 2 := by
      calc
        _ ≤ ∑ k ∈ rows, (Tset.card : ℝ) * ∑ t ∈ Tset, ‖F t k‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          simpa using bounded_finset_coefficient_sum_sq Tset (fun _ => 1) (fun t => F t k)
            (by simp)
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Tset.card : ℝ) * ∑ _t ∈ Tset, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (Nat.cast_nonneg _)
    _ = (Tset.card : ℝ) ^ 2 * E := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) hE

end
end SevenEighths.InverseMoment

end OAI
