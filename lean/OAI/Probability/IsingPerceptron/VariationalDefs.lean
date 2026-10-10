import Mathlib
import OAI.Probability.IsingPerceptron.EnrichedCGF

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

 

def gaussianTransform (s d : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  if d = 0 then ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1
  else (Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
    ∂gaussianReal 0 1)) / d

structure Partition where
  levels : ℕ
  positive : 0 < levels
  cut : Fin (levels + 1) → ℝ
  ordered : StrictMono cut
  first : cut ⟨0, Nat.zero_lt_succ levels⟩ = 0
  last : cut ⟨levels, Nat.lt_succ_self levels⟩ = 1

structure FieldStep where
  partition : Partition
  value : Fin partition.levels → ℝ
  nonneg : ∀ i, 0 ≤ value i
  ordered : Monotone value

 
def stepAt (h : FieldStep) (i : ℕ) : ℝ :=
  if hi : i < h.partition.levels then h.value ⟨i, hi⟩ else 0

 

def stepFunction (h : FieldStep) (u : ℝ) : ℝ :=
  ∑ i : Fin h.partition.levels,
    if h.partition.cut i.castSucc < u ∧ u < h.partition.cut i.succ then h.value i else 0

 
def fieldRecursion (h : FieldStep) : ℝ :=
  let k := h.partition.levels
  let increments := List.ofFn (fun i : Fin k =>
    (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
      h.partition.cut i.castSucc))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U)
    (fun x => Real.log (Real.cosh x) - stepAt h (k - 1) / 2) 0

structure OverlapStep extends FieldStep where
  le_one : ∀ i, value i ≤ 1

 
def patternRecursion (f : ℝ → ℝ) (q : OverlapStep) : ℝ :=
  let k := q.partition.levels
  let levelVal := fun i => if i < k then stepAt q.toFieldStep i else 1
  let increments := List.ofFn (fun i : Fin (k + 1) =>
    (levelVal i - (if i.val = 0 then 0 else levelVal (i.val - 1)), q.partition.cut i))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f 0

def pathMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

 
structure OverlapPath where
  val : ℝ →ₘ[pathMeasure] ℝ
  admissible : ∃ q : ℝ → ℝ,
    (q =ᵐ[pathMeasure] val) ∧ MonotoneOn q (Set.Ioo 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, q u ∈ Set.Icc (0 : ℝ) 1

 
def cellAverage (q : OverlapPath) (k i : ℕ) : ℝ :=
  (k : ℝ) * ∫ u in Set.Ioo ((i : ℝ) / k) (((i : ℝ) + 1) / k),
    q.val u ∂pathMeasure

 

def uniformPattern (f : ℝ → ℝ) (q : OverlapPath) (n : ℕ) : ℝ :=
  let k := n + 1
  let levelVal := fun i => if i < k then cellAverage q k i else 1
  let increments := List.ofFn (fun i : Fin (k + 1) =>
    (levelVal i - (if i.val = 0 then 0 else levelVal (i.val - 1)), (i : ℝ) / k))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f 0

 

def patternFunctional (f : ℝ → ℝ) (q : OverlapPath) : ℝ :=
  Filter.limUnder atTop (uniformPattern f q)

 

def isingEntropy (q : OverlapPath) : EReal :=
  ⨆ h : FieldStep,
    ((fieldRecursion h + (∫ u, stepFunction h u * q.val u ∂pathMeasure) / 2 : ℝ) : EReal)

def variationalValue (α : ℝ) (f : ℝ → ℝ) : EReal :=
  ⨅ q : OverlapPath, (α * patternFunctional f q : ℝ) + isingEntropy q

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def unitMonotoneExtension (q : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if 1 ≤ u then 1 else q u

lemma unitMonotoneExtension_eq {q : ℝ → ℝ} {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    unitMonotoneExtension q u = q u := by
  simp only [unitMonotoneExtension,not_le.mpr hu.1,not_le.mpr hu.2,ite_false]

lemma unitMonotoneExtension_mem {q : ℝ → ℝ}
    (hb : ∀ u ∈ Ioo (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1) (u : ℝ) :
    unitMonotoneExtension q u ∈ Icc (0:ℝ) 1 := by
  unfold unitMonotoneExtension
  split_ifs with h0 h1
  · exact ⟨le_rfl,zero_le_one⟩
  · exact ⟨zero_le_one,le_rfl⟩
  · exact hb u ⟨lt_of_not_ge h0,lt_of_not_ge h1⟩

lemma unitMonotoneExtension_monotone {q : ℝ → ℝ}
    (hq : MonotoneOn q (Ioo (0:ℝ) 1)) (hb : ∀ u ∈ Ioo (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1) :
    Monotone (unitMonotoneExtension q) := by
  intro u v huv
  by_cases hu0 : u ≤ 0
  · simpa only [unitMonotoneExtension,hu0,ite_true] using (unitMonotoneExtension_mem hb v).1
  by_cases hv1 : 1 ≤ v
  · simpa only [unitMonotoneExtension,hv1,ite_true,show ¬v ≤ 0 by linarith,ite_false] using (unitMonotoneExtension_mem hb u).2
  have hu : u ∈ Ioo (0:ℝ) 1 := ⟨lt_of_not_ge hu0,huv.trans_lt (lt_of_not_ge hv1)⟩
  have hv : v ∈ Ioo (0:ℝ) 1 := ⟨hu.1.trans_le huv,lt_of_not_ge hv1⟩
  rw [unitMonotoneExtension_eq hu,unitMonotoneExtension_eq hv]
  exact hq hu hv huv

lemma overlapPath_representative (q : OverlapPath) :
    ∃ p : ℝ → ℝ, (p =ᵐ[pathMeasure] q.val) ∧ Monotone p ∧ ∀ u, p u ∈ Icc (0:ℝ) 1 := by
  obtain ⟨p,hp,hm,hb⟩ := q.admissible
  refine ⟨unitMonotoneExtension p,?_,unitMonotoneExtension_monotone hm hb,unitMonotoneExtension_mem hb⟩
  filter_upwards [hp,ae_restrict_mem measurableSet_Ioo] with u hu huI
  exact (unitMonotoneExtension_eq huI).trans hu

def overlapPathOfMonotone (p : ℝ → ℝ) (hp : Monotone p) (hb : ∀ u, p u ∈ Icc (0:ℝ) 1) : OverlapPath where
  val := AEEqFun.mk p hp.measurable.aestronglyMeasurable
  admissible := ⟨p,(AEEqFun.coeFn_mk p _).symm,hp.monotoneOn _,fun u _ => hb u⟩

lemma overlapPathOfMonotone_ae (p : ℝ → ℝ) (hp : Monotone p) (hb : ∀ u, p u ∈ Icc (0:ℝ) 1) :
    p =ᵐ[pathMeasure] (overlapPathOfMonotone p hp hb).val := (AEEqFun.coeFn_mk p _).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

theorem enrichedMeanPressure_recursion {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b h u ν φ =
      ((∫ p, energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
          (enrichedPoissonBase n h u φ p)
        ∂(poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
          (Measure.infinitePi (fun _ : ℕ => P)))) - N*h n/2)/N := by
  let μ := fun i => enrichedIncrementLaw N n h u (i+1)
  let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
    (Measure.infinitePi (fun _ : ℕ => P)))
  let R := Q.prod (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
  have hL := (enriched_poisson_variance hN n b hb hh h0 u hu ν P hm hK hφ r).1
  have hLd : MemLp (fun p => enrichedPoissonLog n b h u ν φ p / N) 2 R := by
    simpa only [div_eq_mul_inv] using hL.mul_const (N:ℝ)⁻¹
  have hco := hLd.comp_measurePreserving (enrichedToNoise_preserving P r n b h u)
  have hco' := MemLp.ae_eq (enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm).symm hco
  unfold enrichedMeanPressure
  simp_rw [enrichedCylinderPressure_eq_coordinates]
  rw [integral_comp_preserving_ae (enrichedCylinderToCoordinates_preserving P r N n b)
    hco'.aestronglyMeasurable]
  rw [integral_congr_ae (enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm)]
  rw [integral_comp_preserving_ae (enrichedToNoise_preserving P r n b h u) hLd.aestronglyMeasurable]
  rw [integral_div]
  change (∫ p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n,
    (cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2-(N:ℝ)*h n/2) ∂ R)/(N:ℝ) = _
  rw [integral_sub ((enriched_poisson_unshifted hN n b hb hh h0 u hu ν P hm hK hφ r).1.integrable (by norm_num))
    (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  congr 1
  congr 1
  exact cascadeEnergyLog_total_mean Q n b hb μ ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (measurable_enrichedPoissonBase n h u hm)
    (enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1) hh h0 u hu ν P hm hK hφ r).1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def spinLaw (N : ℕ) : Measure (Spin N) :=
  Measure.pi (fun _ : Fin N => (PMF.uniformOfFintype (Fin 2)).toMeasure)
instance spinLaw_probability (N : ℕ) : IsProbabilityMeasure (spinLaw N) := by
  unfold spinLaw
  infer_instance

def magneticEnergy {N : ℕ} (z : Fin N → ℝ) (x : Spin N) : ℝ :=
  ∑ i, z i*spinValue (x i)

lemma measurable_magneticEnergy (N : ℕ) : Measurable (magneticEnergy (N := N)) := by
  unfold magneticEnergy
  fun_prop

lemma spinSign_integral (z : ℝ) :
    (∫ x : Fin 2, Real.exp (z*spinValue x) ∂(PMF.uniformOfFintype (Fin 2)).toMeasure) = Real.cosh z := by
  rw [integral_fintype (Integrable.of_finite),Fin.sum_univ_two]
  simp only [measureReal_def,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,spinValue]
  norm_num
  rw [Real.cosh_eq]
  ring

lemma finiteLogIntegral_magnetic {N : ℕ} (z : Fin N → ℝ) :
    finiteLogIntegral (spinLaw N) (magneticEnergy z) = ∑ i, Real.log (Real.cosh (z i)) := by
  unfold finiteLogIntegral magneticEnergy spinLaw
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (z i*spinValue x))]
  simp only [spinSign_integral]
  rw [Real.log_prod (fun i _ => (Real.cosh_pos _).ne')]

lemma logMean_independent_sum {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (F : ι → ℝ → ℝ)
    {b : ℝ} (_hb : b ≠ 0)
    (_hF : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (fun x => Real.exp (b*F i x)) (μ i)) :
    logMean b (Measure.pi μ) (fun z => ∑ i, F i (z i)) = ∑ i, logMean b (μ i) (F i) := by
  have hp (i : ι) : 0 < ∫ x, Real.exp (b*F i x) ∂μ i :=
    integral_exp_pos (μ i) (F i) (hi i)
  unfold logMean
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (b*F i x)),Real.log_prod (fun i _ => (hp i).ne'),Finset.sum_div]

lemma HasLinearGrowth.scale_argument {F : ℝ → ℝ} (h : HasLinearGrowth F) (a : ℝ) :
    HasLinearGrowth (fun x => F (a*x)) := by
  obtain ⟨C,L,hC,hL,h⟩ := h
  refine ⟨C,L*|a|,hC,mul_nonneg hL (abs_nonneg a),fun x => ?_⟩
  simpa only [Real.norm_eq_abs,abs_mul,mul_assoc] using h (a*x)

lemma gaussianTransform_positive_linearGrowth {U : ℝ → ℝ} (hU : Measurable U)
    (hG : HasLinearGrowth U) (s : ℝ) {d : ℝ} (hd : 0 < d) :
    HasLinearGrowth (gaussianTransform s d U) := by
  let μ : Measure ℝ := gaussianReal 0 (NNReal.mk ((Real.sqrt s)^2) (sq_nonneg _))
  have hm : (gaussianReal 0 1).map (fun z => Real.sqrt s*z) = μ := by
    simpa only [zero_mul,NNReal.coe_mk,mul_zero,mul_one] using
      gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt s)
  have he (x : ℝ) : gaussianTransform s d U x=logMean d μ (fun z => U (x+z)) := by
    simp only [gaussianTransform,hd.ne',ite_false,logMean]
    rw [← hm]
    have hg : Measurable (fun a : ℝ => Real.exp (d*U (x+a))) :=
      ((hU.comp (measurable_const.add measurable_id)).const_mul d).exp
    rw [integral_map (show AEMeasurable (fun z : ℝ => Real.sqrt s*z) (gaussianReal 0 1) from
      (measurable_id.const_mul _).aemeasurable) hg.aestronglyMeasurable]
  change HasLinearGrowth (fun x => gaussianTransform s d U x)
  simp_rw [he]
  exact logMean_hasLinearGrowth μ (gaussianReal_exponentialNormMoments _ _) hU hG hd

lemma measurable_gaussianTransform {U : ℝ → ℝ} (hU : Measurable U) (s d : ℝ) :
    Measurable (gaussianTransform s d U) := by
  unfold gaussianTransform
  split
  · exact (hU.comp (measurable_fst.add (measurable_snd.const_mul _))).stronglyMeasurable.integral_prod_right'.measurable
  · exact Real.measurable_log.comp (((hU.comp
      (measurable_fst.add (measurable_snd.const_mul _))).const_mul d).exp.stronglyMeasurable.integral_prod_right'.measurable) |>.div_const d

lemma gaussianFold_linearGrowth (L : List (ℝ × ℝ))
    (hd : ∀ sd ∈ L, 0 < sd.2) {F : ℝ → ℝ} (hm : Measurable F) (hG : HasLinearGrowth F) :
    Measurable (L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) F) ∧
      HasLinearGrowth (L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) F) := by
  induction L with
  | nil => exact ⟨hm,hG⟩
  | cons sd L ih =>
    have hh := ih (fun sd h => hd sd (List.mem_cons_of_mem _ h))
    exact ⟨measurable_gaussianTransform hh.1 _ _,
      gaussianTransform_positive_linearGrowth hh.1 hh.2 _ (hd sd (List.mem_cons_self))⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticEnergy_add {N : ℕ} (z w : Fin N → ℝ) :
    magneticEnergy (z+w) = magneticEnergy z+magneticEnergy w := by
  ext x
  simp [magneticEnergy,add_mul,Finset.sum_add_distrib]

lemma enrichedIncrement_zero {N n : ℕ} (h : ℕ → ℝ) (i : ℕ)
    (g : Fin (Fintype.card (EnrichedBlock N)) → ℝ) :
    enrichedIncrement N n h 0 i g =
      magneticEnergy (fun j => pathAmplitude h i*g ((Fintype.equivFin (EnrichedBlock N)) (.inl j))) := by
  ext x
  unfold enrichedIncrement enrichedCoefficientsFin
  have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
    (fun j => enrichedLevelCoefficient n h 0 i x j*g ((Fintype.equivFin (EnrichedBlock N)) j))
  simp only [Equiv.apply_symm_apply] at he
  rw [he]
  simp only [Fintype.sum_sum_type,enrichedLevelCoefficient,Pi.zero_apply,mul_zero,
    zero_mul,Finset.sum_const_zero,add_zero, magneticEnergy]
  apply Finset.sum_congr rfl
  intro j _
  ring

def magneticIncrementLaw (N : ℕ) (a : ℝ) : ProbabilityMeasure (Spin N → ℝ) :=
  ⟨(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
    (fun z => magneticEnergy (fun i => a*z i)),
    by infer_instance⟩

lemma enrichedIncrementLaw_zero (N n : ℕ) (h : ℕ → ℝ) (i : ℕ) :
    enrichedIncrementLaw N n h 0 i = magneticIncrementLaw N (pathAmplitude h i) := by
  let e := Fintype.equivFin (EnrichedBlock N)
  let tag : Fin N → ℕ := fun j => (e (.inl j)).val
  have ht : Function.Injective tag := fun j k hjk => Sum.inl_injective (e.injective (Fin.ext hjk))
  have hf := gaussian_pullback_measurePreserving (fun j : Fin (Fintype.card (EnrichedBlock N)) => j.val)
    Fin.val_injective
  have hg := gaussian_pullback_measurePreserving tag ht
  rw [Measure.infinitePi_eq_pi] at hf hg
  apply Subtype.ext
  change (Measure.pi _).map (enrichedIncrement N n h 0 i) = (Measure.pi _).map _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun j => pathAmplitude h i*z j)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [← hf.map_eq,← hg.map_eq,Measure.map_map (measurable_enrichedIncrement N n h 0 i)
     hf.measurable,Measure.map_map hm hg.measurable]
  congr 1
  ext g x
  rw [Function.comp_apply,Function.comp_apply,enrichedIncrement_zero]

lemma logMean_magneticIncrement {N : ℕ} (a b : ℝ) (F : (Spin N → ℝ) → ℝ)
    (hF : Measurable F) :
    logMean b (magneticIncrementLaw N a : Measure (Spin N → ℝ)) F =
      logMean b (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
        (fun z => F (magneticEnergy (fun i => a*z i))) := by
  unfold logMean
  change Real.log (∫ H, Real.exp (b*F H) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
    (fun z => magneticEnergy (fun i => a*z i)))/b = _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => a*z i)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [integral_map hm.aemeasurable
    ((hF.const_mul b).exp.aestronglyMeasurable)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def magneticRecursion : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ
  | 0, _, _ => fun x => Real.log (Real.cosh x)
  | n+1, a, b => gaussianTransform ((a 0)^2) (b 0)
      (magneticRecursion n (fun i => a (i+1)) (fun i => b (i+1)))

lemma magneticRecursion_growth (n : ℕ) (a b : ℕ → ℝ) (hb : ∀ i < n, 0 < b i) :
    Measurable (magneticRecursion n a b) ∧ HasLinearGrowth (magneticRecursion n a b) := by
  induction n generalizing a b with
  | zero => exact ⟨measurable_logCosh,logCosh_linearGrowth⟩
  | succ n ih =>
    have H := ih (fun i => a (i+1)) (fun i => b (i+1)) (fun i hi => hb (i+1) (by omega))
    exact ⟨measurable_gaussianTransform H.1 _ _,gaussianTransform_positive_linearGrowth H.1 H.2 _ (hb 0 (by omega))⟩

lemma magneticRecursion_eq_fold (n : ℕ) (a b : ℕ → ℝ) :
    magneticRecursion n a b =
      (List.ofFn (fun i : Fin n => ((a i)^2,b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) := by
  induction n generalizing a b with
  | zero => simp [magneticRecursion]
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    simp only [magneticRecursion,ih,Fin.val_zero,Fin.val_succ]

lemma energyRecursion_magnetic (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N) (magneticEnergy z) =
      ∑ i, magneticRecursion n a b (z i) := by
  induction n generalizing a b z with
  | zero => exact finiteLogIntegral_magnetic z
  | succ n ih =>
    let U := magneticRecursion n (fun i => a (i+1)) (fun i => b (i+1))
    have hU := magneticRecursion_growth n (fun i => a (i+1)) (fun i => b (i+1))
      (fun i hi => hb (i+1) (by omega))
    change logMean (b 0) (magneticIncrementLaw N (a 0) : Measure (Spin N → ℝ))
      (fun H => energyRecursion n (fun i => b (i+1)) (fun i => magneticIncrementLaw N (a (i+1)))
        (spinLaw N) (magneticEnergy z+H)) = _
    have hm : Measurable (fun H : Spin N → ℝ => energyRecursion n (fun i => b (i+1))
        (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N) (magneticEnergy z+H)) :=
      (measurable_energyRecursion _ _ _ _).comp (measurable_const.add measurable_id)
    rw [logMean_magneticIncrement _ _ _ hm]
    have H (g : Fin N → ℝ) : energyRecursion n (fun i => b (i+1))
      (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N)
        (magneticEnergy z+magneticEnergy (fun i => a 0*g i)) = ∑ i, U (z i+a 0*g i) := by
      rw [← magneticEnergy_add]
      exact ih _ _ (fun i hi => ha (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) _
    simp_rw [H]
    rw [logMean_independent_sum (fun _ : Fin N => gaussianReal 0 1)
      (fun i t => U (z i+a 0*t)) (hb 0 (by omega)).ne']
    · apply Finset.sum_congr rfl
      intro i _
      simp only [magneticRecursion,gaussianTransform,(hb 0 (by omega)).ne',ite_false,
        Real.sqrt_sq (ha 0 (by omega)),logMean,U]
    · intro i
      exact hU.1.comp (measurable_const.add (measurable_id.const_mul _))
    · intro i
      exact integrable_exp_of_linearGrowth (gaussianReal 0 1)
        (gaussianReal_exponentialNormMoments _ _)
        (hU.1.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hU.2.add_left (z i)).scale_argument (a 0)) _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_linearGrowth_integrable {F : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (m : ℝ) (v : ℝ≥0) : Integrable F (gaussianReal m v) := by
  obtain ⟨C,L,hC,hL,h⟩ := hG
  have hi : Integrable (fun x : ℝ => C+L*‖x‖) (gaussianReal m v) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl).norm.const_mul L)
  exact hi.mono' hF.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using h x))

lemma gaussianTransform_const_add {U : ℝ → ℝ} (hU : Measurable U) (hG : HasLinearGrowth U)
    (s d c : ℝ) :
    gaussianTransform s d (fun x => c+U x) = fun x => c+gaussianTransform s d U x := by
  ext x
  by_cases hd : d=0
  · simp only [gaussianTransform,hd,ite_true]
    have hi : Integrable (fun z : ℝ => U (x+Real.sqrt s*z)) (gaussianReal 0 1) :=
      gaussian_linearGrowth_integrable
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) _ _
    rw [integral_add (integrable_const c) hi]
    simp only [integral_const,probReal_univ,one_smul]
  · simp only [gaussianTransform,hd,ite_false]
    exact logMean_const_add (gaussianReal 0 1) hd
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) d) c

lemma gaussianFold_const_add (L : List (ℝ × ℝ)) (hd : ∀ sd ∈ L, 0 < sd.2)
    {F : ℝ → ℝ} (hm : Measurable F) (hG : HasLinearGrowth F) (c : ℝ) :
    L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => c+F x) =
      fun x => c+L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) F x := by
  induction L with
  | nil => rfl
  | cons sd L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun sd h => hd sd (List.mem_cons_of_mem _ h))]
    have hh := gaussianFold_linearGrowth L (fun sd h => hd sd (List.mem_cons_of_mem _ h)) hm hG
    exact gaussianTransform_const_add hh.1 hh.2 _ _ _

lemma poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n with
  | zero => simp
  | succ n => simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

def magneticFieldValue (n : ℕ) (b h : ℕ → ℝ) : ℝ :=
  (∫ z, magneticRecursion n (fun i => pathAmplitude h (i+1)) b (pathAmplitude h 0*z)
    ∂gaussianReal 0 1) - h n/2

lemma integral_magnetic_energyRecursion (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (a₀ : ℝ) :
    (∫ z, energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N)
       (magneticEnergy (fun i => a₀*z i)) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (N:ℝ)*(∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) := by
  have hU := magneticRecursion_growth n a b hb
  have hm : Measurable (fun z : ℝ => magneticRecursion n a b (a₀*z)) :=
    hU.1.comp (measurable_id.const_mul _)
  have hi := gaussian_linearGrowth_integrable hm (hU.2.scale_argument a₀) 0 1
  have hpi (i : Fin N) : Integrable (fun z : Fin N → ℝ => magneticRecursion n a b (a₀*z i))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
      (g := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable).mpr hi
  simp_rw [energyRecursion_magnetic N n a b ha hb]
  rw [integral_finsetSum _ (fun i _ => hpi i)]
  have he (i : Fin N) :
    (∫ z : Fin N → ℝ, magneticRecursion n a b (a₀*z i) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) :=
    integral_comp_preserving_ae (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)
      (F := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

 

theorem enrichedMeanPressure_initial_zero {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) :
    enrichedMeanPressure P 0 n b h 0 (spinLaw N) φ = magneticFieldValue n b h := by
  have hu : ∀ j : Fin N, |(0 : Fin N → ℝ) j| ≤ 2 := by intro j; norm_num
  let μ := fun i => enrichedIncrementLaw N n h 0 (i+1)
  let γ := Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)
  let ρ := Measure.infinitePi (fun _ : ℕ => P)
  have hL := (enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1)
    hh h0 0 hu (spinLaw N) P hm hK hφ 0).1
  have hi : Integrable (fun p => energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p))
      ((poissonMeasure 0).prod (γ.prod ρ)) := hL.integrable (by norm_num)
  rw [enrichedMeanPressure_recursion hN n b hb hh h0 0 hu (spinLaw N) P hm hK hφ 0]
  change ((∫ p, energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p)
    ∂(poissonMeasure 0).prod (γ.prod ρ))-(N:ℝ)*h n/2)/(N:ℝ) = _
  rw [integral_prod _ hi,poissonMeasure_zero_eq_dirac,integral_dirac]
  have hbase (p : (Fin (EnrichedRootSize N) → ℝ) × (ℕ → A)) :
      enrichedPoissonBase n h 0 φ (0,p) = enrichedIncrement N n h 0 0 p.1 := by
    ext x
    simp [enrichedPoissonBase,enrichedBaseEnergy,rootPrefix,patternBase]
  simp_rw [hbase]
  rw [integral_fun_fst (fun z => energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z))]
  simp only [probReal_univ,one_smul]
  have hmap : (∫ z, energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z) ∂γ) =
      ∫ H, energyRecursion n b μ (spinLaw N) H ∂(enrichedIncrementLaw N n h 0 0 : Measure (Spin N → ℝ)) := by
    symm
    exact integral_map (measurable_enrichedIncrement N n h 0 0).aemeasurable
      (measurable_energyRecursion _ _ _ _).aestronglyMeasurable
  rw [hmap]
  dsimp only [μ]
  simp_rw [enrichedIncrementLaw_zero]
  have hmag : (∫ H, energyRecursion n b
        (fun i => magneticIncrementLaw N (pathAmplitude h (i+1))) (spinLaw N) H
      ∂(magneticIncrementLaw N (pathAmplitude h 0) : Measure (Spin N → ℝ))) =
      (N:ℝ)*(∫ z, magneticRecursion n (fun i => pathAmplitude h (i+1)) b (pathAmplitude h 0*z)
        ∂gaussianReal 0 1) := by
    change (∫ H, energyRecursion n b (fun i => magneticIncrementLaw N (pathAmplitude h (i+1)))
      (spinLaw N) H ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
        (fun z => magneticEnergy (fun i => pathAmplitude h 0*z i))) = _
    have hme : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => pathAmplitude h 0*z i)) :=
      (measurable_magneticEnergy N).comp (by fun_prop)
    rw [integral_map hme.aemeasurable (measurable_energyRecursion _ _ _ _).aestronglyMeasurable]
    exact integral_magnetic_energyRecursion N n _ b (fun i _ => Real.sqrt_nonneg _)
      (fun i hi => (hb.1 i hi).1) _
  rw [hmag]
  unfold magneticFieldValue
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

end IsingPerceptron

end

end OAI
