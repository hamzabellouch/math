import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileLipschitz
import OAI.Probability.SKBarriers.Parisi.QuantileMinimizer
import OAI.Probability.SKBarriers.Parisi.QuantileBoundary

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem finite_quantile_minimizer_stationary {k : ℕ} (β : ℝ)
    (A : Fin (k+1) → ℝ) (hA : A ∈ admissibleQuantiles k)
    (hmin : ∀ R ∈ admissibleQuantiles k, extendedQuantileParisi k β A ≤ extendedQuantileParisi k β R)
    (B : Fin (k+1) → ℝ) (hB : B ∈ admissibleQuantiles k) :
    0 ≤ (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
      (A j-quantileOverlapMean k β A j) := by
  have hgapA := (cumulativeGapMap_nonneg_iff k A).mpr ⟨(hA.2 0).1,hA.1⟩
  have strict (R : Fin (k+1) → ℝ) (hR : R ∈ admissibleQuantiles k)
      (hgapR : ∀ j, 0 < cumulativeGapMap k R j) :
      0 ≤ (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(R j-A j)*
        (A j-quantileOverlapMean k β A j) := by
    let Q := fun t : ℝ => (1-t) • A+t • R
    have hQ (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : Q t ∈ admissibleQuantiles k := by
      constructor
      · intro i j hij
        exact add_le_add (mul_le_mul_of_nonneg_left (hA.1 hij) (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left (hR.1 hij) ht.1)
      · intro j
        change (1-t)*A j+t*R j ∈ Set.Icc 0 1
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hA.2 j).1) (mul_nonneg ht.1 (hR.2 j).1)
        · have H₁ := mul_le_mul_of_nonneg_left (hA.2 j).2 (sub_nonneg.mpr ht.2)
          have H₂ := mul_le_mul_of_nonneg_left (hR.2 j).2 ht.1
          linarith
    have hm : IsMinOn (fun t => extendedQuantileParisi k β (Q t)) (Set.Icc (0:ℝ) 1) 0 := by
      intro t ht
      simpa only [Q,sub_zero,one_smul,zero_smul,add_zero,Set.mem_ofPred_eq] using hmin (Q t) (hQ t ht)
    have hd := (extendedQuantileParisi_hasDerivWithinAt_segment β A R hgapA hgapR).mono (show Set.Icc (0:ℝ) 1 ⊆ Set.Ici 0 from Set.Icc_subset_Ici_self)
    have ht : (1:ℝ)-0 ∈ posTangentConeAt (Set.Icc (0:ℝ) 1) 0 :=
      sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc (by norm_num : (0:ℝ) ≤ 1) ▸ Set.Subset.rfl)
    simpa only [sub_zero,ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.smulRight_apply,one_apply_eq_self,smul_eq_mul,one_mul]
       using hm.isLocalMinOn.hasFDerivWithinAt_nonneg hd ht
  let ε := fun n : ℕ => 1/((n:ℝ)+1)
  have hε (n : ℕ) : ε n ∈ Set.Ioc 0 1 := by
    dsimp only [ε]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hgapB := (cumulativeGapMap_nonneg_iff k B).mpr ⟨(hB.2 0).1,hB.1⟩
  have HR (n : ℕ) := regularizeQuantile_positive B hgapB (hε n)
  have H (n : ℕ) := strict (regularizeQuantile k B (ε n))
    ⟨((cumulativeGapMap_nonneg_iff k _).mp (fun j => (HR n j).le)).2,
      regularizeQuantile_mem B hB.2 ⟨(hε n).1.le,(hε n).2⟩⟩ (HR n)
  let F := fun R : Fin (k+1) → ℝ => (β^2/2)*∑ j : Fin (k+1),
    ((k+1:ℕ):ℝ)⁻¹*(R j-A j)*(A j-quantileOverlapMean k β A j)
  have hF : Continuous F := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro j _
    exact (continuous_const.mul ((continuous_apply j).sub continuous_const)).mul continuous_const
  exact ge_of_tendsto (hF.continuousAt.tendsto.comp (regularizeQuantile_tendsto k B)) (Eventually.of_forall H)

end SK.Analytic

end
end

end

end OAI
