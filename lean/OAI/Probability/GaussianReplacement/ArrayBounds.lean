import OAI.Probability.GaussianReplacement.RowOrder

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def arrayReference {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : ℝ≥0∞ :=
  conditionalReferenceKL (observationSignalLaw P).fst (gaussianObservations k d)

lemma observationSignalLaw_fst_as_observed {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) :
    (observationSignalLaw P).fst = (observedMessage P).map
      (MeasurableEquiv.prodComm.trans ((MeasurableEquiv.refl W).prodCongr (observationEquiv k d))) := by
  rw [observationSignalLaw,Measure.fst,Measure.map_map measurable_fst measurable_observationSignalMap,
    observedMessage,Measure.map_map (MeasurableEquiv.measurable _) measurable_observedMessageMap]
  rfl

lemma arrayReference_eq {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    arrayReference P = observationReferenceKL P := by
  let e := MeasurableEquiv.prodComm.trans ((MeasurableEquiv.refl W).prodCongr (observationEquiv k d))
  have href : (((gaussianRows k d).prod (gaussianLabels k)).prod P.fst.snd).map e =
      P.fst.snd.prod (gaussianObservations k d) := by
    change ((((gaussianRows k d).prod (gaussianLabels k)).prod P.fst.snd)).map
      ((Prod.map id (observationEquiv k d)) ∘ Prod.swap) = _
    rw [←Measure.map_map (measurable_id.prodMap (observationEquiv k d).measurable) measurable_swap,
      Measure.prod_swap,←Measure.map_prod_map _ _ measurable_id (observationEquiv k d).measurable,
      Measure.map_id,←gaussianObservations_eq]
  rw [arrayReference,conditionalReferenceKL,observationSignalLaw_context,
    observationSignalLaw_fst_as_observed,←href]
  exact klDiv_map_equiv _ _ e

lemma freshArrayLaw_assoc_first {d k r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    ((freshArrayLaw (observationSignalLaw P) r).map MeasurableEquiv.prodAssoc).map
      (Prod.map id Prod.fst) = (observationSignalLaw P).fst := by
  rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
  change (freshArrayLaw (observationSignalLaw P) r).fst = _
  rw [freshArrayLaw_fst]

lemma freshArrayLaw_aligned {d k r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    ((freshArrayLaw (observationSignalLaw P) r).map MeasurableEquiv.prodAssoc).map
      (Prod.map id (appendEquiv (Vector d×ℝ) k r)) =
      (observationSignalLaw (alignedExperiment (r:=r) P)).fst := by
  rw [freshArrayLaw_eq,observationSignalLaw,
    show (P.map observationSignalMap).prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map observationSignalMap id) by
        rw [←Measure.map_prod_map _ _ measurable_observationSignalMap measurable_id,Measure.map_id],
    Measure.map_map (by fun_prop) (measurable_observationSignalMap.prodMap measurable_id),
    Measure.map_map MeasurableEquiv.prodAssoc.measurable (by fun_prop),
    Measure.map_map (measurable_id.prodMap (appendEquiv _ _ _).measurable) (by fun_prop),
    observationSignalLaw,alignedExperiment,Measure.fst,
    Measure.map_map measurable_fst measurable_observationSignalMap,
    Measure.map_map (measurable_fst.comp measurable_observationSignalMap) measurable_alignedMap]
  congr 1
  funext z
  dsimp [actualExperiment,observationSignalMap]
  rw [ownObservations_append]
  rfl

lemma arrayReference_aligned {d k r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    arrayReference (alignedExperiment (r:=r) P) =
      arrayReference P + freshReference (observationSignalLaw P) r := by
  let Q := (freshArrayLaw (observationSignalLaw P) r).map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := inferInstance
  have he := conditionalReferenceKL_outcome_equiv Q
    ((gaussianObservations k d).prod (gaussianObservations r d)) (appendEquiv (Vector d×ℝ) k r)
  rw [gaussianObservations_append] at he
  dsimp only [Q] at he
  rw [freshArrayLaw_aligned,conditionalReferenceKL_chain,freshArrayLaw_assoc_first,
    MeasurableEquiv.map_symm_map] at he
  exact he

lemma arrayReference_prefix_step {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    arrayReference (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)) =
      arrayReference (prefixLaw P i (Nat.le_of_lt hi)) + singleReference (nextActualRowLaw P i hi) := by
  let Q := (singleObservationLaw (nextActualRowLaw P i hi)).map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := inferInstance
  have hfirst : Q.map (Prod.map id Prod.fst) = (observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi))).fst := by
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
    change (singleObservationLaw (nextActualRowLaw P i hi)).fst = _
    rw [singleObservationLaw_fst,nextActualRowLaw_fst]
  have htotal : Q.map (Prod.map id (snocEquiv (Vector d×ℝ) i)) =
      (observationSignalLaw (prefixLaw P (i+1) (Nat.succ_le_of_lt hi))).fst := by
    have he := congrArg (fun μ : Measure ((W×Observations (i+1) d)×Sphere d) => μ.fst)
      (nextActualRowLaw_single P i hi)
    rw [Measure.fst,Measure.map_map measurable_fst ((MeasurableEquiv.measurable _).prodMap measurable_id)] at he
    dsimp only [Q,singleObservationLaw]
    rw [Measure.map_map (measurable_id.prodMap (snocEquiv _ _).measurable) MeasurableEquiv.prodAssoc.measurable,
      Measure.fst,Measure.map_map (by fun_prop) measurable_fst]
    exact he
  have he := conditionalReferenceKL_outcome_equiv Q
    ((gaussianObservations i d).prod (gaussianObservation d)) (snocEquiv (Vector d×ℝ) i)
  rw [show (((gaussianObservations i d).prod (gaussianObservation d)).map (snocEquiv (Vector d×ℝ) i)) =
      gaussianObservations (i+1) d from snocEquiv_map (gaussianObservation d) i,htotal,
    conditionalReferenceKL_chain,hfirst] at he
  dsimp only [Q] at he
  rw [MeasurableEquiv.map_symm_map] at he
  exact he



def baselineCost (d k : ℕ) : ℝ≥0∞ :=
  klDiv (projectionJoint (uniformSphere d) (gaussianRows k d))
    ((gaussianRows k d).prod (gaussianLabels k))

def hybridBaselineConstant : ℝ := 20 + |Real.log (normalizer 1)+1/2|

lemma hybridBaselineConstant_pos : 0 < hybridBaselineConstant := by
  unfold hybridBaselineConstant
  positivity

lemma baselineCost_finite {d k : ℕ} (hk : 2 ≤ k) (hkd : k < d-1) :
    baselineCost d k ≠ ∞ ∧ (baselineCost d k).toReal ≤ hybridBaselineConstant*d := by
  have hd : 2 ≤ d := by omega
  have hdim : AdmissibleDimensions d 1 (k-1) 1 := by
    unfold AdmissibleDimensions
    omega
  have he : 1+(k-1) = k := by omega
  have h := sphere_projection_reference_finite hdim hd
  rw [he] at h
  refine ⟨h.1,h.2.trans ?_⟩
  have hcast : (k:ℝ) ≤ d := by exact_mod_cast (show k ≤ d by omega)
  have hg := le_abs_self (Real.log (normalizer 1)+1/2)
  have hg0 := abs_nonneg (Real.log (normalizer 1)+1/2)
  dsimp [hybridBaselineConstant]
  nlinarith

lemma arrayReference_finite_bound {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows k d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hk : 2 ≤ k) (hkd : k < d-1) :
    arrayReference P ≠ ∞ ∧ (arrayReference P).toReal ≤ hybridBaselineConstant*d+B := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  have hHf : shannonEntropy (observedMessage P).snd ≠ ∞ := by
    rw [observedMessage_snd]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  have hI := countable_information_le_entropy (observedMessage P) hHf
  have hbase := baselineCost_finite hk hkd
  rw [arrayReference_eq,observationReferenceKL_decomposition P (uniformSphere d) hInd]
  change baselineCost d k + mutualInformation (observedMessage P) ≠ ∞ ∧
    (baselineCost d k + mutualInformation (observedMessage P)).toReal ≤ hybridBaselineConstant*d+B
  have hIf : mutualInformation (observedMessage P) ≠ ∞ := hI.1
  refine ⟨ENNReal.add_ne_top.mpr ⟨hbase.1,hI.1⟩,?_⟩
  rw [ENNReal.toReal_add hbase.1 hIf]
  have hHb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hH
  rw [ENNReal.toReal_ofReal hB] at hHb
  apply add_le_add hbase.2
  apply hI.2.trans
  simpa only [observedMessage_snd] using hHb

lemma arrayReference_exposed_chain {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows k d)) :
    arrayReference P + exposedInformation P =
      baselineCost d k + mutualInformation P.fst + rowInformation P (gaussianRows k d) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  rw [arrayReference_eq]
  exact observationReferenceKL_chain_exposed P (uniformSphere d) hInd

lemma exposedInformation_finite {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hH : shannonEntropy P.fst.snd ≠ ∞) : exposedInformation P ≠ ∞ := by
  have he := exposedInformation_chain P
  let : IsProbabilityMeasure (P.map swapLast) := inferInstance
  have hi := countable_information_le_entropy (P.map swapLast) (by rwa [swapLast_snd])
  exact ne_top_of_le_ne_top hi.1 (by change exposedInformation P ≤ mutualInformation (P.map swapLast); rw [he]; exact le_add_left le_rfl)

lemma rowInformation_finite_bound {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows k d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B) :
    rowInformation P (gaussianRows k d) ≠ ∞ ∧ (rowInformation P (gaussianRows k d)).toReal ≤ B := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  have h := rowInformation_le_entropy P (uniformSphere d) (gaussianRows k d) hInd
    (by rw [swapLast_snd]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH)
  rw [swapLast_snd] at h
  have hHb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hH
  rw [ENNReal.toReal_ofReal hB] at hHb
  exact ⟨h.1,h.2.trans hHb⟩

lemma freshReference_from_array_bound {d i r : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows i d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows i d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hk : 2 ≤ i+r) (hkd : i+r < d-1) :
    freshReference (observationSignalLaw P) r ≠ ∞ ∧
      (freshReference (observationSignalLaw P) r).toReal ≤ hybridBaselineConstant*d+B := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  have h := arrayReference_finite_bound (alignedExperiment (r:=r) P) hd
    (alignedExperiment_independence P (uniformSphere d) hInd) hB
    (by rwa [alignedExperiment_fst]) hk hkd
  have hl : freshReference (observationSignalLaw P) r ≤ arrayReference (alignedExperiment (r:=r) P) := by
    rw [arrayReference_aligned]
    exact le_add_left le_rfl
  exact ⟨ne_top_of_le_ne_top h.1 hl,(ENNReal.toReal_mono h.1 hl).trans h.2⟩

lemma freshSlope_from_array_bound {d i r : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows i d)) [IsProbabilityMeasure P]
    (hd : 16 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows i d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hk : 2 ≤ i+r+d/8) (hkd : i+r+d/8 < d-1) :
    freshSlope (observationSignalLaw P) r ≠ ∞ ∧
      (freshSlope (observationSignalLaw P) r).toReal ≤ 16*hybridBaselineConstant+B/(d/8:ℕ) := by
  have h := freshReference_from_array_bound (r:=r+d/8) P (by omega) hInd hB hH (by omega) (by omega)
  have ha := freshSlope_average (observationSignalLaw P) r (d/8) (by omega) h.1
  refine ⟨ha.1,ha.2.trans ?_⟩
  have hp : (0:ℝ)<(d/8:ℕ) := by exact_mod_cast (show 0<d/8 by omega)
  have hratio : (d:ℝ) ≤ 16*(d/8:ℕ) := by exact_mod_cast (show d ≤ 16*(d/8) by omega)
  have hbpos := hybridBaselineConstant_pos
  apply (div_le_iff₀ hp).mpr
  calc
    (freshReference (observationSignalLaw P) (r+d/8)).toReal ≤ hybridBaselineConstant*d+B := h.2
    _ ≤ (16*hybridBaselineConstant+B/(d/8:ℕ))*(d/8:ℕ) := by
      rw [add_mul,div_mul_cancel₀ _ hp.ne']
      nlinarith


lemma arrayReference_actual_step {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) (r : ℕ) :
    arrayReference (alignedExperiment (r:=r) (prefixLaw P (i+1) (Nat.succ_le_of_lt hi))) =
      arrayReference (alignedExperiment (r:=r) (prefixLaw P i (Nat.le_of_lt hi))) +
      singleReference (liftActualLaw (nextActualRowLaw P i hi) r) := by
  have hc : freshReference (observationSignalLaw (prefixLaw P (i+1) (Nat.succ_le_of_lt hi))) r =
      freshReference (singleSignalLaw (nextActualRowLaw P i hi)) r := by
    rw [←nextActualRowLaw_single P i hi]
    exact freshReference_context _ _ _
  rw [arrayReference_aligned,arrayReference_aligned,arrayReference_prefix_step,hc,add_assoc,
    actual_fresh_diamond,nextActualRowLaw_fst,←add_assoc]

lemma nextActualRowLaw_signal_row {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i < m) :
    (nextActualRowLaw P i hi).map (fun z => (z.1.2,z.2)) = ν.prod (stdGaussian (Vector d)) := by
  have he := congrArg (fun μ : Measure (Sphere d×Rows m d) => μ.map (Prod.map id (fun X => X ⟨i,hi⟩))) hInd
  rw [←Measure.map_prod_map _ _ measurable_id (measurable_pi_apply _),Measure.map_id] at he
  have hev : (gaussianRows m d).map (fun X => X ⟨i,hi⟩) = stdGaussian (Vector d) :=
    (measurePreserving_eval (fun _ : Fin m => stdGaussian (Vector d)) ⟨i,hi⟩).map_eq
  rw [hev] at he
  rw [nextActualRowLaw,Measure.map_map (measurable_fst.snd.prodMk measurable_snd) (measurable_nextActualRow hi)]
  rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_id.prodMap (measurable_pi_apply _)) (measurable_fst.comp swapLast.measurable)] at he
  exact he

lemma gaussian_sphere_inner_mixture {d : ℕ} (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] :
    (ν.prod (stdGaussian (Vector d))).map (fun z => ⟪(z.1:Vector d),z.2⟫) = gaussianReal 0 1 := by
  ext t ht
  rw [Measure.map_apply (by fun_prop) ht,Measure.prod_apply (ht.preimage (by fun_prop))]
  have he (s : Sphere d) : stdGaussian (Vector d) {x | ⟪(s:Vector d),x⟫ ∈ t} = gaussianReal 0 1 t := by
    have h := congrArg (fun μ : Measure ℝ => μ t) (gaussian_inner_map_sphere s)
    rwa [Measure.map_apply (by fun_prop) ht] at h
  change (∫⁻ s : Sphere d, stdGaussian (Vector d) {x | ⟪(s:Vector d),x⟫ ∈ t} ∂ν) = _
  simp_rw [he]
  simp

lemma nextActualRowLaw_label {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i < m) (r : ℕ) :
    (residualLabelLaw (nextActualRowLaw P i hi) r).snd = gaussianReal 0 1 := by
  rw [residualLabelLaw,Measure.snd,Measure.map_map measurable_snd measurable_residualLabelObservation]
  have hel : Measurable (fun z : ((W×Observations i d)×Sphere d)×Vector d => ⟪(z.1.2:Vector d),z.2⟫) := by fun_prop
  change ((nextActualRowLaw P i hi).prod (gaussianRows r d)).map ((fun z => ⟪(z.1.2:Vector d),z.2⟫) ∘ Prod.fst) = _
  rw [←Measure.map_map hel measurable_fst,←Measure.fst,Measure.fst_prod]
  have he := congrArg (fun μ : Measure (Sphere d×Vector d) => μ.map (fun z => ⟪(z.1:Vector d),z.2⟫))
    (nextActualRowLaw_signal_row P ν hInd i hi)
  rw [Measure.map_map (by fun_prop) (measurable_fst.snd.prodMk measurable_snd),gaussian_sphere_inner_mixture] at he
  exact he

lemma hybrid_one_step {d m i r q : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hd : 16 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B)
    (hi : i < m) (hr : r ≤ d) (hd8 : d ≤ 8*r) (hq : 1 ≤ q)
    (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q) (htotal : i+r+2 < d-1) :
    (exposedInformation (alignedExperiment (r:=r+1) (prefixLaw P i (Nat.le_of_lt hi)))).toReal -
      (exposedInformation (alignedExperiment (r:=r) (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)))).toReal ≤
        hybridRowConstant +
        (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal/q +
        (freshSlope (observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi))) (r+1)).toReal -
        (freshSlope (observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi))) r).toReal := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let P0 := prefixLaw P i (Nat.le_of_lt hi)
  let P1 := prefixLaw P (i+1) (Nat.succ_le_of_lt hi)
  have hI0 : (P0.map swapLast).fst = (uniformSphere d).prod (gaussianRows i d) :=
    prefixLaw_independence P (uniformSphere d) hInd _ _
  have hI1 : (P1.map swapLast).fst = (uniformSphere d).prod (gaussianRows (i+1) d) :=
    prefixLaw_independence P (uniformSphere d) hInd _ _
  have hH0 : shannonEntropy P0.fst.snd ≤ ENNReal.ofReal B := by rwa [prefixLaw_fst]
  have hH1 : shannonEntropy P1.fst.snd ≤ ENNReal.ofReal B := by rwa [prefixLaw_fst]
  have hR0 := rowInformation_finite_bound P0 (by omega) hI0 hB hH0
  have hR1 := rowInformation_finite_bound P1 (by omega) hI1 hB hH1
  have hKchain := prefix_rowInformation_step P i hi
  change rowInformation P1 _ = rowInformation P0 _ + _ at hKchain
  have hK : klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) ≠ ∞ :=
    ne_top_of_le_ne_top hR1.1 (by rw [hKchain]; exact le_add_left le_rfl)
  have hF0 := freshReference_from_array_bound (r:=r+1) P0 (by omega) hI0 hB hH0 (by omega) (by omega)
  have hF1 := freshReference_from_array_bound (r:=r+1+1) P0 (by omega) hI0 hB hH0 (by omega) (by omega)
  have hT0 := (freshSlope_average (observationSignalLaw P0) r 1 (by omega) hF0.1).1
  have hT1 := (freshSlope_average (observationSignalLaw P0) (r+1) 1 (by omega) hF1.1).1
  have hcross := actual_fresh_row_bound (nextActualRowLaw P i hi) hK hr hd8 hq hqr hmargin
    (by rwa [nextActualRowLaw_fst]) (by rwa [nextActualRowLaw_fst])
    (nextActualRowLaw_label P (uniformSphere d) hInd i hi r)
  rw [nextActualRowLaw_fst] at hcross
  have hA0 := arrayReference_finite_bound (alignedExperiment (r:=r) P0) (by omega)
    (alignedExperiment_independence P0 (uniformSphere d) hI0) hB (by rwa [alignedExperiment_fst]) (by omega) (by omega)
  have hAl := arrayReference_finite_bound (alignedExperiment (r:=r+1) P0) (by omega)
    (alignedExperiment_independence P0 (uniformSphere d) hI0) hB (by rwa [alignedExperiment_fst]) (by omega) (by omega)
  have hAr := arrayReference_finite_bound (alignedExperiment (r:=r) P1) (by omega)
    (alignedExperiment_independence P1 (uniformSphere d) hI1) hB (by rwa [alignedExperiment_fst]) (by omega) (by omega)
  have hJ0 := exposedInformation_finite (alignedExperiment (r:=r+1) P0)
    (by rw [alignedExperiment_fst]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH0)
  have hJ1 := exposedInformation_finite (alignedExperiment (r:=r) P1)
    (by rw [alignedExperiment_fst]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH1)
  have hMI : mutualInformation P.fst ≠ ∞ := (countable_information_le_entropy P.fst (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH)).1
  have hbase := (baselineCost_finite (d:=d) (k:=i+(r+1)) (by omega) (by omega)).1
  have hc0 := arrayReference_exposed_chain (alignedExperiment (r:=r+1) P0) (by omega)
    (alignedExperiment_independence P0 (uniformSphere d) hI0)
  have hc1 := arrayReference_exposed_chain (alignedExperiment (r:=r) P1) (by omega)
    (alignedExperiment_independence P1 (uniformSphere d) hI1)
  rw [alignedExperiment_fst,rowInformation_alignedExperiment] at hc0 hc1
  change _ = baselineCost d (i+(r+1)) + mutualInformation P0.fst + _ at hc0
  change _ = baselineCost d (i+1+r) + mutualInformation P1.fst + _ at hc1
  have hPf0 : P0.fst = P.fst := prefixLaw_fst _ _ _
  have hPf1 : P1.fst = P.fst := prefixLaw_fst _ _ _
  rw [hPf0] at hc0
  have hbe : baselineCost d (i+1+r) = baselineCost d (i+(r+1)) := congrArg (baselineCost d) (by omega)
  rw [hPf1,hbe] at hc1
  have hc0r := congrArg ENNReal.toReal hc0
  have hc1r := congrArg ENNReal.toReal hc1
  rw [ENNReal.toReal_add hAl.1 hJ0,ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hbase,hMI⟩) hR0.1,
    ENNReal.toReal_add hbase hMI] at hc0r
  rw [ENNReal.toReal_add hAr.1 hJ1,ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hbase,hMI⟩) hR1.1,
    ENNReal.toReal_add hbase hMI] at hc1r
  have hKreal := congrArg ENNReal.toReal hKchain
  rw [ENNReal.toReal_add hR0.1 hK] at hKreal
  have har := arrayReference_actual_step P i hi r
  have harr := congrArg ENNReal.toReal har
  rw [ENNReal.toReal_add hA0.1 hcross.1] at harr
  have hal : arrayReference (alignedExperiment (r:=r+1) P0) =
      arrayReference (alignedExperiment (r:=r) P0) + freshSlope (observationSignalLaw P0) r := by
    rw [arrayReference_aligned,arrayReference_aligned,freshReference_succ,add_assoc]
  have halr := congrArg ENNReal.toReal hal
  rw [ENNReal.toReal_add hA0.1 hT0] at halr
  change _ ≤ hybridRowConstant + _ + (freshSlope (observationSignalLaw P0) (r+1)).toReal -
    (freshSlope (observationSignalLaw P0) r).toReal
  rw [nextActualRowLaw_fst] at hKreal ⊢
  linarith [hcross.2]



end CurrentProjection

end

end OAI
