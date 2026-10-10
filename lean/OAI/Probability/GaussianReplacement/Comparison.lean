import OAI.Probability.GaussianReplacement.Posterior

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma criticalFamily_projection_ac {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d) :
    ∀ᵐ v ∂(criticalSignal P (m+r)).snd, ∀ᵐ G ∂gaussianRows (m+r) d,
      labelLaw (messagePosterior (criticalSignal P (m+r)) v) G ≪ volume := by
  filter_upwards [ae_positive_atom (criticalSignal P (m+r)).snd] with v hv
  obtain ⟨hB,hD,_,_⟩ := criticalFamily_growth P hσ hdim.2.2.2.1 hv
  apply ae_labelLaw_ac_of_growth hdim _ (criticalB P (m+r) v) (criticalD P (m+r) v)
    (Real.exp_pos _) _ hB hD
  dsimp only [criticalD]
  positivity

lemma criticalFamily_actual_log_bound {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    [IsProbabilityMeasure (uniformSphere d)] (hdim : AdmissibleDimensions d m r q)
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hH : shannonEntropy P.snd ≠ ∞)
    (R : Measure ((Sphere d×(W×(ℕ×ℤ)))×Rows m d)) [IsProbabilityMeasure R]
    (hRF : R.fst = criticalSignal P (m+r))
    (hInd : (R.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d)) :
    Integrable (fun z => Real.log (1+(exactDensity
      (messagePosterior (criticalSignal P (m+r)) z.2) z.1.1 z.1.2).toReal))
      (observedMessage (alignedExperiment (r:=r) R)) ∧
    Integrable (fun z => logPositive (exactDensity
      (messagePosterior (criticalSignal P (m+r)) z.2) z.1.1 z.1.2))
      (observedMessage (alignedExperiment (r:=r) R)) ∧
    (∫ z, Real.log (1+(exactDensity (messagePosterior (criticalSignal P (m+r)) z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage (alignedExperiment (r:=r) R)) ≤
      (rowInformation R (gaussianRows m d)).toReal/q +
      (∫ v : W×(ℕ×ℤ), (v.2.2:ℝ) ∂(criticalSignal P (m+r)).snd) +
      (shannonEntropy (P.map (criticalRefinement P (m+r)))).toReal + 18*d +
      Real.log (1+(shannonEntropy (criticalSignal P (m+r)).snd).toReal) := by
  have hℓ := hdim.2.2.2.1
  have hEnt := criticalSignal_entropy P hσ hℓ hH
  obtain ⟨hCI,hmean⟩ := criticalFamily_moment_mean P hσ hℓ hH
  have hmain := actual_posterior_log_bound hdim R (uniformSphere d) hInd 1
    (by simp) (by simpa only [hRF] using hEnt.2.2.1)
    (criticalB P (m+r)) (criticalD P (m+r))
    (fun v _ => Real.exp_pos _)
    (fun v _ => by dsimp only [criticalD]; positivity)
    (by intro v hv; simp only [hRF] at hv ⊢; exact (criticalFamily_growth P hσ hℓ hv).2.2.2)
    (by intro v hv; simp only [hRF] at hv ⊢; exact (criticalFamily_growth P hσ hℓ hv).1)
    (by intro v hv; simp only [hRF] at hv ⊢; exact (criticalFamily_growth P hσ hℓ hv).2.1)
    (by simpa only [hRF] using hCI)
  simp only [hRF] at hmain
  refine ⟨hmain.1,hmain.2.1,?_⟩
  linarith [hmain.2.2]

lemma critical_refined_comparison {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    [IsProbabilityMeasure (uniformSphere d)] (hdim : AdmissibleDimensions d m r q)
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hH : shannonEntropy P.snd ≠ ∞)
    (R : Measure ((Sphere d×(W×(ℕ×ℤ)))×Rows m d)) [IsProbabilityMeasure R]
    (hRF : R.fst = criticalSignal P (m+r))
    (hInd : (R.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d)) :
    exposedInformation ((criticalSignal P (m+r)).prod (gaussianRows (m+r) d)) ≠ ∞ ∧
    exposedInformation (alignedExperiment (r:=r) R) ≠ ∞ ∧
    (exposedInformation ((criticalSignal P (m+r)).prod (gaussianRows (m+r) d))).toReal ≤
      (exposedInformation (alignedExperiment (r:=r) R)).toReal +
      (rowInformation R (gaussianRows m d)).toReal/q +
      (shannonEntropy (P.map (criticalRefinement P (m+r)))).toReal +
      (1+18*(d:ℝ)+5*(m+r)) + Real.log (1+(shannonEntropy (criticalSignal P (m+r)).snd).toReal) := by
  let F := criticalSignal P (m+r)
  let A := alignedExperiment (r:=r) R
  let Q := F.prod (gaussianRows m d)
  have hAF : A.fst = F := (alignedExperiment_fst R).trans hRF
  have hA := criticalFamily_actual_log_bound hdim P hσ hH R hRF hInd
  have hQInd : (Q.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d) := by
    rw [independent_rows_signal,criticalSignal_fst,hσ]
  have hQ := criticalFamily_actual_log_bound hdim P hσ hH Q Measure.fst_prod hQInd
  rw [alignedExperiment_independent] at hQ
  have hEnt := (criticalSignal_entropy P hσ hdim.2.2.2.1 hH).2.2.1
  have hAc := criticalFamily_projection_ac hdim P hσ
  have hsignal := alignedExperiment_independence (r:=r) R (uniformSphere d) hInd
  obtain ⟨hlogA,hlogQ,hJA,hJQ,hcompare⟩ := exposedInformation_density_comparison A
    (uniformSphere d) hsignal (by simpa only [hAF] using hEnt) (by simpa only [hAF] using hAc)
    (by simpa only [hAF] using hA.2.1) (by simpa only [hAF] using hQ.2.1)
  simp only [hAF] at hlogA hlogQ hJQ hcompare
  have hCover := criticalFamily_cover_mean P hσ hdim.2.2.2.1 hH hAc hQ.2.1 hlogQ
  have hLogLe : (∫ z, Real.log (exactDensity (messagePosterior F z.2) z.1.1 z.1.2).toReal
      ∂observedMessage A) ≤
      ∫ z, Real.log (1+(exactDensity (messagePosterior F z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage A := by
    apply integral_mono_ae hlogA hA.1
    filter_upwards [] with z
    exact (le_max_left _ _).trans (logPositive_le_log_one_add _)
  refine ⟨hJQ,hJA,?_⟩
  simp only [Nat.cast_add] at hCover
  dsimp only [A,F] at hLogLe hcompare
  linarith [hA.2.2]

lemma critical_unrefined_comparison {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    [IsProbabilityMeasure (uniformSphere d)] (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    (hH : shannonEntropy P.fst.snd ≠ ∞) :
    exposedInformation (P.fst.prod (gaussianRows (m+r) d)) ≠ ∞ ∧
    exposedInformation (alignedExperiment (r:=r) P) ≠ ∞ ∧
    (exposedInformation (P.fst.prod (gaussianRows (m+r) d))).toReal ≤
      (exposedInformation (alignedExperiment (r:=r) P)).toReal +
      (rowInformation P (gaussianRows m d)).toReal/q +
      2*(shannonEntropy (P.fst.map (criticalRefinement P.fst (m+r)))).toReal +
      (1+18*(d:ℝ)+5*(m+r)) + Real.log (1+(shannonEntropy (criticalSignal P.fst (m+r)).snd).toReal) := by
  let e := criticalRefinement P.fst (m+r)
  have he := measurable_criticalRefinement P.fst (m+r)
  let R := refineRows P e
  let : IsProbabilityMeasure R := refineRows_probability P e he
  have hRF : R.fst = criticalSignal P.fst (m+r) := refineRows_fst P e he
  have hRI : (R.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d) :=
    (refineRows_signal_rows P e he).trans hInd
  have hσ := signal_marginal_of_independence P (uniformSphere d) (gaussianRows m d) hInd
  obtain ⟨hE,hEb,hF,hFb⟩ := criticalSignal_entropy P.fst hσ hdim.2.2.2.1 hH
  have hRIeq : rowInformation R (gaussianRows m d) = rowInformation P (gaussianRows m d) :=
    rowInformation_refinement P (gaussianRows m d) e he
  obtain ⟨hJ0R,hJ1R,hcmp⟩ := critical_refined_comparison hdim P.fst hσ hH R hRF hRI
  rw [hRIeq] at hcmp
  have hJ0 : exposedInformation (P.fst.prod (gaussianRows (m+r) d)) ≠ ∞ :=
    (exposedInformation_le_entropy _ (by simpa only [Measure.fst_prod] using hH)).1
  have hJ1 : exposedInformation (alignedExperiment (r:=r) P) ≠ ∞ :=
    (exposedInformation_le_entropy _ (by simpa only [alignedExperiment_fst] using hH)).1
  have hDrop := exposedInformation_dropMessage ((criticalSignal P.fst (m+r)).prod (gaussianRows (m+r) d))
  change exposedInformation (((refineSignal P.fst e).prod (gaussianRows (m+r) d)).map
    (fun p => ((p.1.1,p.1.2.1),p.2))) ≤ _ at hDrop
  simp only [independent_refineSignal_drop P.fst e he] at hDrop
  have hAF : (alignedExperiment (r:=r) R).fst = criticalSignal P.fst (m+r) :=
    (alignedExperiment_fst R).trans hRF
  have hAE : (alignedExperiment (r:=r) R).fst.snd.snd = P.fst.map e := by
    rw [hAF]
    exact refineSignal_snd_snd P.fst e he
  have hCost := exposedInformation_refinement_cost (alignedExperiment (r:=r) R)
    (by rwa [hAF]) (by rwa [hAE])
  simp only [hAE,alignedExperiment_drop,R,refineRows_drop P e he] at hCost
  have hh0 := ENNReal.toReal_mono hJ0R hDrop
  have hh1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hJ1,hE⟩) hCost
  rw [ENNReal.toReal_add hJ1 hE] at hh1
  refine ⟨hJ0,hJ1,?_⟩
  linarith



lemma critical_entropy_scalars {d : ℕ} (hd : 1 ≤ d) {H E F : ℝ}
    (hH0 : 0 ≤ H) (hH : H ≤ (d:ℝ)^2)
    (hE : E ≤ 1+2*Real.log (20*((d:ℝ)+1+H)+1)) (hF0 : 0 ≤ F) (hF : F ≤ H+E) :
    E ≤ 127*(d:ℝ) ∧ Real.log (1+F) ≤ 131*(d:ℝ) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have hd2 : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hd21 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have harg : 20*((d:ℝ)+1+H)+1 ≤ 61*(d:ℝ)^2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0<20*((d:ℝ)+1+H)+1) harg
  rw [Real.log_mul (by norm_num : (61:ℝ) ≠ 0) (by positivity),Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hl61 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 61)
  have hld := Real.log_le_self hd0.le
  have hEb : E ≤ 127*(d:ℝ) := by nlinarith
  refine ⟨hEb,?_⟩
  have harg2 : 1+F ≤ 129*(d:ℝ)^2 := by nlinarith
  have hlog2 := Real.log_le_log (by positivity : 0<1+F) harg2
  rw [Real.log_mul (by norm_num : (129:ℝ) ≠ 0) (by positivity),Real.log_pow] at hlog2
  norm_num only [Nat.cast_ofNat] at hlog2
  have hl129 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 129)
  nlinarith

lemma critical_dimensions {d : ℕ} (hd : 100 ≤ d) :
    AdmissibleDimensions d (d/10) (d/2-d/10) (d/10) ∧ d/10+(d/2-d/10) ≤ d ∧
    d ≤ 20*(d/10) := by
  unfold AdmissibleDimensions
  omega

lemma uniformSphere_probability_of_pos {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (uniformSphere d) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  constructor
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero
    (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := Vector d)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'


theorem criticalComparisonMain : CriticalComparisonMain := by
  refine ⟨1000,100,by norm_num,?_⟩
  intro d hd W _ _ _ P _ hInd hH
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty W := nonempty_of_isProbabilityMeasure P.fst.snd
  rw [swapLast_snd] at hH
  have hHfin : shannonEntropy P.fst.snd ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hHr : (shannonEntropy P.fst.snd).toReal ≤ (d:ℝ)^2 :=
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hH
  obtain ⟨hdim,hℓ,hq⟩ := critical_dimensions hd
  obtain ⟨hJ0,hJ1,hcomp⟩ := critical_unrefined_comparison hdim P hInd hHfin
  have hσ := signal_marginal_of_independence P (uniformSphere d) (gaussianRows (d/10) d) hInd
  obtain ⟨hE,hEb,hF,hFb⟩ := criticalSignal_entropy P.fst hσ hdim.2.2.2.1 hHfin
  obtain ⟨he,hl⟩ := critical_entropy_scalars (show 1 ≤ d by omega) ENNReal.toReal_nonneg hHr
    hEb ENNReal.toReal_nonneg hFb
  obtain ⟨hRow,hRowB⟩ := rowInformation_le_entropy P (uniformSphere d) (gaussianRows (d/10) d)
    hInd (by rwa [swapLast_snd])
  rw [swapLast_snd] at hRowB
  have hqr : (0:ℝ) < (d/10:ℕ) := by exact_mod_cast (show 0<d/10 by have := hdim.2.2.1; omega)
  have hqrB : (d:ℝ) ≤ 20*(d/10:ℕ) := by exact_mod_cast hq
  have hℓr : ((d/10+(d/2-d/10):ℕ):ℝ) ≤ d := by exact_mod_cast hℓ
  simp only [Nat.cast_add] at hℓr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hRowr : (rowInformation P (gaussianRows (d/10) d)).toReal/(d/10:ℕ) ≤ 20*(d:ℝ) := by
    apply (div_le_iff₀ hqr).mpr
    nlinarith [hRowB.trans hHr]
  apply (ENNReal.toReal_le_toReal hJ0 (ENNReal.add_ne_top.mpr ⟨hJ1,ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add hJ1 ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by positivity)]
  nlinarith






def OneLevelComparisonMain : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ ∀ d, d₀ ≤ d →
    ∀ (U : Type) [MeasurableSpace U] [Finite U] [MeasurableSingletonClass U],
    ∀ (P : Measure ((Sphere d×U)×Rows (d/32) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/32) d) →
    exposedInformation (P.fst.prod (gaussianRows (d/32+(d/4-d/32)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/4-d/32) P) +
      ENNReal.ofReal (C*((d:ℝ)+Real.log (1+(d:ℝ)+(shannonEntropy P.fst.snd).toReal)+
        (shannonEntropy P.fst.snd).toReal/(d:ℝ)))

def TwoLabelComparisonMain : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ ∀ d, d₀ ≤ d →
    ∀ (V : Type) [MeasurableSpace V] [Finite V] [MeasurableSingletonClass V],
    ∀ (P : Measure ((Sphere d×V)×Rows (d/8) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/8) d) →
    shannonEntropy P.fst.snd ≤ ENNReal.ofReal ((d:ℝ)^2) →
    exposedInformation (P.fst.prod (gaussianRows (d/8+(d/2-d/8)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/2-d/8) P) + ENNReal.ofReal (C*d)

lemma level_entropy_scalars {d : ℕ} (hd : 1 ≤ d) {H E F : ℝ}
    (hH0 : 0 ≤ H) (hE : E ≤ 1+2*Real.log (20*((d:ℝ)+1+H)+1))
    (hF0 : 0 ≤ F) (hF : F ≤ H+E) :
    E ≤ 43+2*Real.log (1+(d:ℝ)+H) ∧ Real.log (1+F) ≤ 47+Real.log (1+(d:ℝ)+H) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have ht : (1:ℝ) ≤ 1+(d:ℝ)+H := by linarith
  have ht0 : (0:ℝ) < 1+(d:ℝ)+H := by linarith
  have harg : 20*((d:ℝ)+1+H)+1 ≤ 21*(1+(d:ℝ)+H) := by linarith
  have hl := Real.log_le_log (by positivity : 0<20*((d:ℝ)+1+H)+1) harg
  rw [Real.log_mul (by norm_num : (21:ℝ) ≠ 0) ht0.ne'] at hl
  have hl21 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 21)
  have he : E ≤ 43+2*Real.log (1+(d:ℝ)+H) := by linarith
  refine ⟨he,?_⟩
  have hlt := Real.log_le_self ht0.le
  have harg2 : 1+F ≤ 47*(1+(d:ℝ)+H) := by linarith
  have hl2 := Real.log_le_log (by positivity : 0<1+F) harg2
  rw [Real.log_mul (by norm_num : (47:ℝ) ≠ 0) ht0.ne'] at hl2
  linarith [Real.log_le_self (by norm_num : (0:ℝ) ≤ 47)]

lemma oneLevel_dimensions {d : ℕ} (hd : 100 ≤ d) :
    AdmissibleDimensions d (d/32) (d/4-d/32) (d/16) ∧
      d/32+(d/4-d/32) ≤ d ∧ d ≤ 32*(d/16) := by
  unfold AdmissibleDimensions
  omega

lemma twoLabel_dimensions {d : ℕ} (hd : 100 ≤ d) :
    AdmissibleDimensions d (d/8) (d/2-d/8) (d/8) ∧
      d/8+(d/2-d/8) ≤ d ∧ d ≤ 20*(d/8) := by
  unfold AdmissibleDimensions
  omega




theorem oneLevelComparisonMain : OneLevelComparisonMain := by
  refine ⟨1000,100,by norm_num,?_⟩
  intro d hd U _ _ _ P _ hInd
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty U := nonempty_of_isProbabilityMeasure P.fst.snd
  have hH : shannonEntropy P.fst.snd ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_of_countable
      (fun u : U => -Real.log (P.fst.snd {u}).toReal)).aestronglyMeasurable
      (Eventually.of_forall (atom_surprisal_nonneg P.fst.snd))).mpr Integrable.of_finite
  obtain ⟨hdim,hℓ,hq⟩ := oneLevel_dimensions hd
  obtain ⟨hJ0,hJ1,hcmp⟩ := critical_unrefined_comparison hdim P hInd hH
  have hσ := signal_marginal_of_independence P (uniformSphere d) (gaussianRows (d/32) d) hInd
  obtain ⟨hE,hEb,hF,hFb⟩ := criticalSignal_entropy P.fst hσ hdim.2.2.2.1 hH
  obtain ⟨he,hl⟩ := level_entropy_scalars (show 1 ≤ d by omega) ENNReal.toReal_nonneg
    hEb ENNReal.toReal_nonneg hFb
  obtain ⟨hRow,hRowB⟩ := rowInformation_le_entropy P (uniformSphere d) (gaussianRows (d/32) d)
    hInd (by rwa [swapLast_snd])
  rw [swapLast_snd] at hRowB
  have hqr : (0:ℝ) < (d/16:ℕ) := by exact_mod_cast (show 0<d/16 by omega)
  have hqrB : (d:ℝ) ≤ 32*(d/16:ℕ) := by exact_mod_cast hq
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd0 : (0:ℝ) < d := by linarith
  have hℓr : ((d/32+(d/4-d/32):ℕ):ℝ) ≤ d := by exact_mod_cast hℓ
  simp only [Nat.cast_add] at hℓr
  have hH0 : 0 ≤ (shannonEntropy P.fst.snd).toReal := ENNReal.toReal_nonneg
  have hL0 : 0 ≤ Real.log (1+(d:ℝ)+(shannonEntropy P.fst.snd).toReal) :=
    Real.log_nonneg (by linarith)
  have hRowr : (rowInformation P (gaussianRows (d/32) d)).toReal/(d/16:ℕ) ≤
      32*((shannonEntropy P.fst.snd).toReal/(d:ℝ)) := by
    apply (div_le_iff₀ hqr).mpr
    have hp := mul_le_mul_of_nonneg_left hqrB (div_nonneg hH0 hd0.le)
    rw [div_mul_cancel₀ _ hd0.ne'] at hp
    nlinarith
  apply (ENNReal.toReal_le_toReal hJ0 (ENNReal.add_ne_top.mpr ⟨hJ1,ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add hJ1 ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by positivity)]
  nlinarith [div_nonneg hH0 hd0.le]


theorem twoLabelComparisonMain : TwoLabelComparisonMain := by
  refine ⟨1000,100,by norm_num,?_⟩
  intro d hd V _ _ _ P _ hInd hH
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let : Nonempty V := nonempty_of_isProbabilityMeasure P.fst.snd
  have hHfin : shannonEntropy P.fst.snd ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hHr : (shannonEntropy P.fst.snd).toReal ≤ (d:ℝ)^2 :=
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hH
  obtain ⟨hdim,hℓ,hq⟩ := twoLabel_dimensions hd
  obtain ⟨hJ0,hJ1,hcomp⟩ := critical_unrefined_comparison hdim P hInd hHfin
  have hσ := signal_marginal_of_independence P (uniformSphere d) (gaussianRows (d/8) d) hInd
  obtain ⟨hE,hEb,hF,hFb⟩ := criticalSignal_entropy P.fst hσ hdim.2.2.2.1 hHfin
  obtain ⟨he,hl⟩ := critical_entropy_scalars (show 1 ≤ d by omega) ENNReal.toReal_nonneg hHr
    hEb ENNReal.toReal_nonneg hFb
  obtain ⟨hRow,hRowB⟩ := rowInformation_le_entropy P (uniformSphere d) (gaussianRows (d/8) d)
    hInd (by rwa [swapLast_snd])
  rw [swapLast_snd] at hRowB
  have hqr : (0:ℝ) < (d/8:ℕ) := by exact_mod_cast (show 0<d/8 by omega)
  have hqrB : (d:ℝ) ≤ 20*(d/8:ℕ) := by exact_mod_cast hq
  have hℓr : ((d/8+(d/2-d/8):ℕ):ℝ) ≤ d := by exact_mod_cast hℓ
  simp only [Nat.cast_add] at hℓr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hRowr : (rowInformation P (gaussianRows (d/8) d)).toReal/(d/8:ℕ) ≤ 20*(d:ℝ) := by
    apply (div_le_iff₀ hqr).mpr
    nlinarith [hRowB.trans hHr]
  apply (ENNReal.toReal_le_toReal hJ0 (ENNReal.add_ne_top.mpr ⟨hJ1,ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add hJ1 ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by positivity)]
  nlinarith




end CurrentProjection

end

end OAI
