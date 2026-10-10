import Mathlib
import OAI.Probability.SKBarriers.Interpolation.GuerraUpper

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def quantileOverlapMean (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ :=
  hierarchyMeanOverlap (blockDimension (Fintype.card (Edge 1)) 1 k)
    (blockMass (Fintype.card (Edge 1)) 1 k)
    (blockExponent (skInteraction 1) (fun _ => 0)
      (fun b => β*Real.sqrt (cumulativeGapMap k Q b)))
    (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge 1)) 1 k j)

theorem quantileOverlapMean_bounds (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) :
    quantileOverlapMean k β Q j ∈ Set.Icc 0 1 :=
  hierarchyMeanOverlap_bounds _ _ _ _ (fun i s => by cases s i <;> norm_num [spin]) _

theorem extendedQuantileParisi_continuous (k : ℕ) (β : ℝ) :
    Continuous (extendedQuantileParisi k β) := by
  have hv : Continuous (fun Q : Fin (k+1) → ℝ => fun b => β*Real.sqrt (cumulativeGapMap k Q b)) := by
    apply continuous_pi
    intro b
    exact continuous_const.mul (Real.continuous_sqrt.comp ((continuous_apply b).comp (cumulativeGapMap k).continuous))
  have H := (skBlockRoot_contDiff 1 k).continuous.comp ((continuous_const (y := (0:ℝ))).prodMk hv)
  change Continuous (fun Q : Fin (k+1) → ℝ => skBlockRoot 1 k 0 (fun b => β*Real.sqrt (cumulativeGapMap k Q b))) at H
  simp only [skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),Nat.cast_one,one_mul] at H
  apply H.add
  apply continuous_const.mul
  exact (continuous_const.sub (continuous_const.mul (continuous_apply (Fin.last k)))).add
    (continuous_finsetSum _ (fun j _ => continuous_const.mul ((continuous_apply j).pow 2)))

theorem extendedQuantileParisi_hasDerivAt {k : ℕ} (β : ℝ)
    (Q : ℝ → Fin (k+1) → ℝ) {t : ℝ} {V : Fin (k+1) → ℝ}
    (hQ : HasDerivAt Q V t) (hgap : ∀ j, 0 < cumulativeGapMap k (Q t) j) :
    HasDerivAt (fun u => extendedQuantileParisi k β (Q u))
      ((β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*
        (Q t j-quantileOverlapMean k β (Q t) j)) t := by
  let v := fun u j => β*Real.sqrt (cumulativeGapMap k (Q u) j)
  let vp := fun j => β*(cumulativeGapMap k V j/(2*Real.sqrt (cumulativeGapMap k (Q t) j)))
  let r := quantileOverlapMean k β (Q t)
  have hv : HasDerivAt v vp t := by
    apply hasDerivAt_pi.mpr
    intro j
    have H := hasDerivAt_pi.mp ((cumulativeGapMap k).hasFDerivAt.comp_hasDerivAt t hQ) j
    exact (H.sqrt (hgap j).ne').const_mul β
  have hvp (j : Fin (k+1)) : vp j*v t j = (β^2/2)*cumulativeGapMap k V j := by
    have hsqrt := (Real.sqrt_pos.mpr (hgap j)).ne'
    dsimp only [vp,v]
    field_simp [hsqrt]
  have H := skBlockPressure_hasDerivAt (N := 1) (by norm_num) (fun _ => 0) v
    (hasDerivAt_const t (0:ℝ)) hv
  dsimp only at H
  simp only [zero_mul,zero_div,zero_add,Nat.cast_one,div_one,
    skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),one_mul,hvp] at H
  have he : (∑ b, (β^2/2)*cumulativeGapMap k V b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) =
      (β^2/2)*(V (Fin.last k)-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V l*r l) := by
    rw [← fixed_field_summation k V r (fun _ => ((k+1:ℕ):ℝ)⁻¹),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change HasDerivAt (fun u => scalarHierarchy (k+1) (quantileMass k) (v u) scalarSpinTerminal 0)
    (∑ b, (β^2/2)*cumulativeGapMap k V b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) t at H
  rw [he] at H
  have HS : HasDerivAt (fun u => ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q u j)^2)
      (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q t j*V j)) t := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa using ((hasDerivAt_pi.mp hQ j).pow 2).const_mul (((k+1:ℕ):ℝ)⁻¹)
  have HC := (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_pi.mp hQ (Fin.last k)).const_mul 2)).add HS).const_mul (β^2/4)
  have HA := H.add HC
  apply HA.congr_deriv
  have he1 : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q t j*V j)) =
      2*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*Q t j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he2 : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*(Q t j-r j)) =
      (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*Q t j)-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*r j := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  change _ = (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*(Q t j-r j)
  rw [he1,he2]
  ring
end SK.Analytic

end
end

end

end OAI
