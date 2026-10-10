import OAI.Probability.GaussianReplacement.Hybrid

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



lemma shannonEntropy_le_log_card {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (π : Measure W) [IsProbabilityMeasure π] :
    (shannonEntropy π).toReal ≤ Real.log (Fintype.card W) := by
  let : Nonempty W := nonempty_of_isProbabilityMeasure π
  let Q := (PMF.uniformOfFintype W).toMeasure
  have hQ : ∀ w, Q {w} = (Fintype.card W:ℝ≥0∞)⁻¹ := by
    intro w
    change (PMF.uniformOfFintype W).toMeasure {w} = _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w),PMF.uniformOfFintype_apply]
  have hq0 : (Fintype.card W:ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hPQ : π ≪ Q := countable_ac_of_atom π Q (by intro w hw; exact (hq0 ((hQ w).symm.trans hw)).elim)
  obtain ⟨_,hb⟩ := countable_entropy_le_crossEntropy π Q hPQ (Integrable.of_finite)
  have he : (fun w => -Real.log (Q {w}).toReal) = fun _ : W => Real.log (Fintype.card W) := by
    funext w
    rw [hQ w,ENNReal.toReal_inv,ENNReal.toReal_natCast,Real.log_inv,neg_neg]
  simpa [he] using hb

lemma fiber_comparison {d : ℕ} (hd : 100 ≤ d) {W : Type*} [Fintype W]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows (d/10) d)) [IsProbabilityMeasure P]
    (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/10) d))
    (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal ((d:ℝ)^2)) :
    freshInformation P.fst (d/3) ≤ exposedInformation (alignedExperiment (r:=d/3-d/10) P) +
      ENNReal.ofReal (1000*d) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty W := nonempty_of_isProbabilityMeasure P.fst.snd
  have hHfin : shannonEntropy P.fst.snd ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hHr : (shannonEntropy P.fst.snd).toReal ≤ (d:ℝ)^2 :=
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hH
  have hdim : AdmissibleDimensions d (d/10) (d/3-d/10) (d/10) := by
    unfold AdmissibleDimensions
    omega
  obtain ⟨hJ0,hJ1,hcomp⟩ := critical_unrefined_comparison hdim P hInd hHfin
  have hσ := signal_marginal_of_independence P (uniformSphere d) (gaussianRows (d/10) d) hInd
  obtain ⟨hE,hEb,hF,hFb⟩ := criticalSignal_entropy P.fst hσ hdim.2.2.2.1 hHfin
  obtain ⟨he,hl⟩ := critical_entropy_scalars (show 1 ≤ d by omega) ENNReal.toReal_nonneg hHr
    hEb ENNReal.toReal_nonneg hFb
  obtain ⟨hRow,hRowB⟩ := rowInformation_le_entropy P (uniformSphere d) (gaussianRows (d/10) d)
    hInd (by rwa [swapLast_snd])
  rw [swapLast_snd] at hRowB
  have hqr : (0:ℝ) < (d/10:ℕ) := by exact_mod_cast (show 0<d/10 by omega)
  have hqrB : (d:ℝ) ≤ 20*(d/10:ℕ) := by exact_mod_cast (show d≤20*(d/10) by omega)
  have hℓr : ((d/10+(d/3-d/10):ℕ):ℝ) ≤ d := by exact_mod_cast (show d/10+(d/3-d/10)≤d by omega)
  simp only [Nat.cast_add] at hℓr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1≤d by omega)
  have hRowr : (rowInformation P (gaussianRows (d/10) d)).toReal/(d/10:ℕ) ≤ 20*(d:ℝ) := by
    apply (div_le_iff₀ hqr).mpr
    nlinarith [hRowB.trans hHr]
  have hbound : exposedInformation (P.fst.prod (gaussianRows (d/10+(d/3-d/10)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/3-d/10) P) + ENNReal.ofReal (1000*d) := by
    apply (ENNReal.toReal_le_toReal hJ0 (ENNReal.add_ne_top.mpr ⟨hJ1,ENNReal.ofReal_ne_top⟩)).mp
    rw [ENNReal.toReal_add hJ1 ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by positivity)]
    nlinarith
  have hdimEq : d/10+(d/3-d/10) = d/3 := by omega
  change freshInformation P.fst (d/10+(d/3-d/10)) ≤ _ at hbound
  have hfresh : freshInformation P.fst (d/10+(d/3-d/10)) = freshInformation P.fst (d/3) :=
    congrArg (freshInformation P.fst) hdimEq
  rwa [hfresh] at hbound

theorem fiberBlockMain : FiberBlockMain := by
  refine ⟨1000,100,by norm_num,?_⟩
  intro d hd U V _ _ _ _ _ _ P _ hS κ _ N hN hcard hNlog
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty U := nonempty_of_isProbabilityMeasure P.snd
  let : Nonempty V := nonempty_of_isProbabilityMeasure (endingSignalLaw P κ).snd
  have hEnt : shannonEntropy (endingSignalLaw P κ).snd ≤ ENNReal.ofReal ((d:ℝ)^2) := by
    apply (ENNReal.toReal_le_toReal (shannonEntropy_finite _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    apply (shannonEntropy_le_log_card _).trans
    exact (Real.log_le_log (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hcard)).trans hNlog
  have hInd : ((endingRowLaw P κ).map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/10) d) := by
    rw [endingRowLaw_independence,hS]
  have h := fiber_comparison hd (endingRowLaw P κ) hInd (by rwa [endingRowLaw_fst])
  simp only [endingRowLaw_fst] at h
  have hproc := block_exposed_le_fresh (r:=d/3-d/10) P κ
  have he : freshInformation P (d/10+(d/3-d/10)) = freshInformation P (d/3) :=
    congrArg (freshInformation P) (by omega)
  rw [he] at hproc
  exact h.trans (add_le_add hproc le_rfl)



end CurrentProjection

end

end OAI
