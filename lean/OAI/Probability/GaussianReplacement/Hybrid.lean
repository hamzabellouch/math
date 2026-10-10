import OAI.Probability.GaussianReplacement.Telescopes

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma shannonEntropy_finite {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (π : Measure W) [IsProbabilityMeasure π] :
    shannonEntropy π ≠ ∞ := by
  rw [shannonEntropy,lintegral_fintype]
  apply ENNReal.sum_ne_top.mpr
  intro w hw
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top π _)

lemma freshInformation_finite {d k : ℕ} {W : Type*}
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] : freshInformation P k ≠ ∞ := by
  apply exposedInformation_finite
  rw [Measure.fst_prod]
  exact shannonEntropy_finite P.snd

lemma hybrid_block_bound {d m : ℕ} (hd : 256 ≤ d) (hm : m ≤ d/8)
    {U V : Type*} [Fintype U] [Fintype V]
    [MeasurableSpace U] [MeasurableSpace V]
    [MeasurableSingletonClass U] [MeasurableSingletonClass V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (hS : P.fst = uniformSphere d)
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ]
    {B : ℝ} (hB : 0 ≤ B)
    (hH : shannonEntropy (endingSignalLaw P κ).snd ≤ ENNReal.ofReal B) :
    averagedFreshInformation (endingSignalLaw P κ)-averagedFreshInformation P ≤
      hybridRowConstant*m+(m:ℝ)/hybridCount d*(16*hybridBaselineConstant+B/(d/8:ℕ))+B/(d/32:ℕ) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty U := nonempty_of_isProbabilityMeasure P.snd
  let : Nonempty V := nonempty_of_isProbabilityMeasure (endingSignalLaw P κ).snd
  have hi : ((endingRowLaw P κ).map swapLast).fst = (uniformSphere d).prod (gaussianRows m d) := by
    rw [endingRowLaw_independence,hS]
  have hh : shannonEntropy (endingRowLaw P κ).fst.snd ≤ ENNReal.ofReal B := by
    rwa [endingRowLaw_fst]
  have h := hybrid_average_ending (endingRowLaw P κ) hd hm hi hB hh
  simp_rw [exposedInformation_prefix_zero,endingRowLaw_fst] at h
  have hle : (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d),
      (exposedInformation (alignedExperiment (r:=k-m) (endingRowLaw P κ))).toReal) / hybridCount d ≤
      averagedFreshInformation P := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro k hk
    have hkm : m ≤ k := by
      obtain ⟨hk,_⟩ := Finset.mem_Icc.mp hk
      unfold hybridFirst at hk
      omega
    have hl := block_exposed_le_fresh (r:=k-m) P κ
    have hfresh : freshInformation P (m+(k-m)) = freshInformation P k :=
      congrArg (freshInformation P) (Nat.add_sub_of_le hkm)
    rw [hfresh] at hl
    exact ENNReal.toReal_mono (freshInformation_finite P) hl
  change averagedFreshInformation (endingSignalLaw P κ) - _ ≤ _ at h
  linarith

lemma hybrid_block_numeric {d m : ℕ} {B C : ℝ}
    (hd : 256 ≤ d) (hm : m ≤ d/8) (hB : 0 ≤ B) (hBd : B ≤ (d:ℝ)^2)
    (hC : 0 ≤ C) :
    C*m+(m:ℝ)/hybridCount d*(C+B/(d/8:ℕ))+B/(d/32:ℕ) ≤ (100*C+100)*d := by
  have hh0 : (0:ℝ)<(d/8:ℕ) := by exact_mod_cast (show 0<d/8 by omega)
  have hq0 : (0:ℝ)<(d/32:ℕ) := by exact_mod_cast (show 0<d/32 by omega)
  have hN0 : (0:ℝ)<hybridCount d := by unfold hybridCount; positivity
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hmd : (m:ℝ) ≤ d := by exact_mod_cast (show m≤d by omega)
  have hdh : (d:ℝ) ≤ 16*(d/8:ℕ) := by exact_mod_cast (show d≤16*(d/8) by omega)
  have hdq : (d:ℝ) ≤ 64*(d/32:ℕ) := by exact_mod_cast (show d≤64*(d/32) by omega)
  have hmN : (m:ℝ) ≤ hybridCount d := by
    exact_mod_cast (show m≤hybridCount d by unfold hybridCount hybridFirst hybridLast; omega)
  have hmN' : (m:ℝ)/hybridCount d ≤ 1 := (div_le_one hN0).mpr hmN
  have hBh : B/(d/8:ℕ) ≤ 16*d := by
    apply (div_le_iff₀ hh0).mpr
    nlinarith
  have hBq : B/(d/32:ℕ) ≤ 64*d := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith
  have hmul : (m:ℝ)/hybridCount d*(C+B/(d/8:ℕ)) ≤ C+16*d := by
    calc
      _ ≤ 1*(C+B/(d/8:ℕ)) := mul_le_mul_of_nonneg_right hmN' (add_nonneg hC (div_nonneg hB hh0.le))
      _ ≤ C+16*d := by linarith
  have hCm := mul_le_mul_of_nonneg_left hmd hC
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  nlinarith

theorem hybridBlockMain : HybridBlockMain := by
  let C := 1+|hybridRowConstant|+16*hybridBaselineConstant
  have hbase := hybridBaselineConstant_pos
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,100*C+100,256,hC,by positivity,?_⟩
  intro d hd m hm1 hm U V _ _ _ _ _ _ P _ hS κ _ B hB hH
  have h := hybrid_block_bound hd hm P hS κ hB hH
  have hrow : hybridRowConstant ≤ C := by
    have h := le_abs_self hybridRowConstant
    dsimp [C]
    linarith
  have hbaseline : 16*hybridBaselineConstant ≤ C := by
    dsimp [C]
    linarith [abs_nonneg hybridRowConstant]
  have hbound : averagedFreshInformation (endingSignalLaw P κ)-averagedFreshInformation P ≤
    C*m+(m:ℝ)/hybridCount d*(C+B/(d/8:ℕ))+B/(d/32:ℕ) := by
    apply h.trans
    apply add_le_add _ le_rfl
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hrow (Nat.cast_nonneg _)
    · exact mul_le_mul_of_nonneg_left (add_le_add hbaseline le_rfl) (by positivity)
  refine ⟨hbound,fun hBd => hbound.trans (hybrid_block_numeric hd hm hB hBd hC.le)⟩



end CurrentProjection

end

end OAI
