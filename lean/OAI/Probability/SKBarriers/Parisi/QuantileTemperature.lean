import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileClamp
import OAI.Probability.SKBarriers.Scalar.ScalarAtomic
import OAI.Probability.SKBarriers.Parisi.QuantileInterior

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem extendedQuantileParisi_hasDerivAt_temperature {k : ℕ} (β : ℝ)
    (Q : Fin (k+1) → ℝ) (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) :
    HasDerivAt (fun b => extendedQuantileParisi k b Q)
      ((β/2)*(1+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2-
        2*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*quantileOverlapMean k β Q j)) β := by
  let v := fun b j => b*Real.sqrt (cumulativeGapMap k Q j)
  let vp := fun j => Real.sqrt (cumulativeGapMap k Q j)
  let r := quantileOverlapMean k β Q
  have hv : HasDerivAt v vp β := by
    apply hasDerivAt_pi.mpr
    intro j
    convert (hasDerivAt_id β).mul_const (vp j) using 1 <;>
      first | rfl | simp only [one_mul]
  have hvp (j : Fin (k+1)) : vp j*v β j = β*cumulativeGapMap k Q j := by
    dsimp only [vp,v]
    calc
      _ = β*(Real.sqrt (cumulativeGapMap k Q j))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hQ j)]
  have H := skBlockPressure_hasDerivAt (N := 1) (by norm_num) (fun _ => 0) v
    (hasDerivAt_const β (0:ℝ)) hv
  dsimp only at H
  simp only [zero_mul,zero_div,zero_add,Nat.cast_one,div_one,
    skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),one_mul,hvp] at H
  change HasDerivAt (fun b => scalarHierarchy (k+1) (quantileMass k) (v b) scalarSpinTerminal 0)
    (∑ b, β*cumulativeGapMap k Q b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) β at H
  have he : (∑ b, β*cumulativeGapMap k Q b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) =
      β*(Q (Fin.last k)-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q l*r l) := by
    rw [← fixed_field_summation k Q r (fun _ => ((k+1:ℕ):ℝ)⁻¹),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he] at H
  have HC := (((hasDerivAt_id β).pow 2).div_const 4).mul_const
    (1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)
  have HA := H.add HC
  apply HA.congr_deriv
  change _ = (β/2)*(1+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2-
    2*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*r j)
  dsimp only [id_eq]
  ring

theorem atomicParisi_hasDerivAt_temperature {k : ℕ} (β : ℝ)
    (Q : Fin (k+1) → ℝ) (hQ : Q ∈ admissibleQuantiles k) :
    HasDerivAt (fun b => atomicParisi k b Q)
      ((β/2)*(1+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2-
        2*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*quantileOverlapMean k β Q j)) β := by
  have he : (fun b => atomicParisi k b Q) = fun b => extendedQuantileParisi k b Q := by
    funext b
    exact atomicParisi_eq_extended k b Q hQ.2
  rw [he]
  exact extendedQuantileParisi_hasDerivAt_temperature β Q
    ((cumulativeGapMap_nonneg_iff k Q).mpr ⟨(hQ.2 0).1,hQ.1⟩)

theorem finite_interior_minimizer_temperature {k : ℕ} {β : ℝ} (hβ : β ≠ 0)
    (A : Fin (k+1) → ℝ) (hord : StrictMono A) (hint : ∀ j, A j ∈ Set.Ioo 0 1)
    (hmin : ∀ B ∈ admissibleQuantiles k, extendedQuantileParisi k β A ≤ extendedQuantileParisi k β B) :
    HasDerivAt (fun b => atomicParisi k b A)
      ((β/2)*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(A j)^2)) β := by
  have hA : A ∈ admissibleQuantiles k := ⟨hord.monotone,fun j => ⟨(hint j).1.le,(hint j).2.le⟩⟩
  have H := atomicParisi_hasDerivAt_temperature β A hA
  simp_rw [finite_quantile_minimizer_interior_fixedPoint hβ A hord hint hmin] at H
  apply H.congr_deriv
  have he : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*A j*A j) =
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(A j)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

end SK.Analytic

end
end

end

end OAI
