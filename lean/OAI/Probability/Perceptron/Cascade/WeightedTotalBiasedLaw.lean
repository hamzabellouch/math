import Mathlib
import OAI.Probability.Perceptron.Variational.MarkedTotalBiasedLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff
attribute [fun_prop] stablePoissonTotal_measurable
section MarkedStable
variable {S : Type*} [MeasurableSpace S]
variable [Nonempty S]

def weightedTotalBiasedLaw (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) (F : S → ℝ) :
    Measure (Measure (ℝ × S)) :=
  normalizedMeasure ((poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).withDensity
    (fun η => ENNReal.ofReal (poissonWeightedTotal F η^a)))

lemma weightedTotalBiasedLaw_shift (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 ≤ b) {F : S → ℝ} (hF : Measurable F)
    [IsProbabilityMeasure (ν.withDensity (fun c => ENNReal.ofReal (Real.exp (b*F c))))] :
    (weightedTotalBiasedLaw ν a b F).map (Measure.map (logMarkShift F)) =
      markedTotalBiasedLaw (ν.withDensity (fun c => ENNReal.ofReal (Real.exp (b*F c)))) a b := by
  let Φ := Measure.map (logMarkShift F)
  have hΦ : Measurable Φ := Measure.measurable_map _ (logMarkShift_measurable hF)
  have hpow : Measurable (fun η : Measure (ℝ × S) => ENNReal.ofReal (markedStableTotal η^a)) := by fun_prop
  unfold weightedTotalBiasedLaw markedTotalBiasedLaw
  rw [normalizedMeasure_map _ hΦ]
  congr 1
  have hd := map_withDensity_comp (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) hΦ hpow
  dsimp [Function.comp_def,Φ] at hd
  simp_rw [markedStableTotal_map_shift _ hF] at hd
  rw [stablePoisson_mark_shift ν hb hF] at hd
  exact hd.symm

lemma weightedTotalBiasedLaw_add_const (ν : Measure S) [IsProbabilityMeasure ν]
    (a b : ℝ) {F : S → ℝ} (hF : Measurable F) (c : ℝ) :
    weightedTotalBiasedLaw ν a b (fun x => F x+c) = weightedTotalBiasedLaw ν a b F := by
  have hpw (η : Measure (ℝ × S)) : poissonWeightedTotal (fun x => F x+c) η^a =
      (Real.exp c)^a*(poissonWeightedTotal F η)^a := by
    rw [poissonWeightedTotal_add_const hF c η]
    exact Real.mul_rpow (Real.exp_pos c).le (show 0 ≤ poissonWeightedTotal F η from ENNReal.toReal_nonneg)
  unfold weightedTotalBiasedLaw
  simp_rw [hpw,ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos c).le a)]
  have he := withDensity_smul' (μ := poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
    (ENNReal.ofReal ((Real.exp c)^a)) (fun η => ENNReal.ofReal (poissonWeightedTotal F η^a)) ENNReal.ofReal_ne_top
  simp only [Pi.smul_def,smul_eq_mul] at he
  rw [he,normalizedMeasure_smul _
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos (Real.exp_pos c) a)) ENNReal.ofReal_ne_top]

omit [Nonempty S] in

lemma weightedBranchMass_map (η : Measure (ℝ × S)) {F : S → ℝ} (hF : Measurable F) :
    (normalizedMeasure (η.withDensity (fun p : ℝ × S => ENNReal.ofReal (Real.exp (p.1+F p.2))))).map (logMarkShift F) =
      markedStableMassKernel (η.map (logMarkShift F)) := by
  rw [normalizedMeasure_map _ (logMarkShift_measurable hF)]
  change normalizedMeasure _ = normalizedMeasure ((η.map (logMarkShift F)).withDensity
    (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1)))
  rw [map_withDensity_comp η (logMarkShift_measurable hF) (by fun_prop)]
  rfl

def exponentialMarkTilt (ν : Measure S) (b : ℝ) (X : S → ℝ) : Measure S :=
  normalizedMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*X x))))

def centeredLogMark (ν : Measure S) (b : ℝ) (X : S → ℝ) : S → ℝ :=
  fun x => X x-Real.log (∫ y, Real.exp (b*X y) ∂ν)/b

omit [Nonempty S] in
lemma centeredLogMark_measurable (ν : Measure S) (b : ℝ) {X : S → ℝ} (hX : Measurable X) :
    Measurable (centeredLogMark ν b X) := hX.sub_const _

omit [Nonempty S] in
lemma exponentialMarkTilt_probability (ν : Measure S) [IsProbabilityMeasure ν]
    {b : ℝ} {X : S → ℝ} (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    IsProbabilityMeasure (exponentialMarkTilt ν b X) := by
  have hMpos := integral_exp_pos hI
  apply normalizedMeasure_probability
  all_goals rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => (Real.exp_pos _).le)]
  · exact ENNReal.ofReal_ne_zero_iff.mpr hMpos
  · exact ENNReal.ofReal_ne_top

omit [Nonempty S] in
lemma centeredLogMark_density (ν : Measure S) [IsProbabilityMeasure ν]
    {b : ℝ} (hb : b ≠ 0) {X : S → ℝ} (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*centeredLogMark ν b X x))) =
      exponentialMarkTilt ν b X := by
  let M := ∫ y, Real.exp (b*X y) ∂ν
  have hMpos : 0 < M := integral_exp_pos hI
  have hd (x : S) : ENNReal.ofReal (Real.exp (b*centeredLogMark ν b X x)) =
      (ENNReal.ofReal M)⁻¹*ENNReal.ofReal (Real.exp (b*X x)) := by
    unfold centeredLogMark
    rw [mul_sub,show b*(Real.log (∫ y, Real.exp (b*X y) ∂ν)/b) = Real.log M by dsimp [M]; field_simp,
      Real.exp_sub,Real.exp_log hMpos,ENNReal.ofReal_div_of_pos hMpos,div_eq_mul_inv,mul_comm]
  simp_rw [hd]
  have he := withDensity_smul' (μ := ν) (ENNReal.ofReal M)⁻¹
    (fun x => ENNReal.ofReal (Real.exp (b*X x)))
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hMpos))
  simp only [Pi.smul_def,smul_eq_mul] at he
  rw [he]
  unfold exponentialMarkTilt normalizedMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma weightedTotalBiasedLaw_centered (ν : Measure S) [IsProbabilityMeasure ν]
    (a b : ℝ) {X : S → ℝ} (hX : Measurable X) :
    weightedTotalBiasedLaw ν a b (centeredLogMark ν b X) = weightedTotalBiasedLaw ν a b X := by
  change weightedTotalBiasedLaw ν a b (fun x => X x-Real.log (∫ y, Real.exp (b*X y) ∂ν)/b) = _
  simpa only [sub_eq_add_neg] using
    weightedTotalBiasedLaw_add_const ν a b hX (-(Real.log (∫ y, Real.exp (b*X y) ∂ν)/b))

lemma weightedRootBlock_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    {X : S → ℝ} (hX : Measurable X) (hI : Integrable (fun x => Real.exp (b*X x)) ν)
    (ns : List (ℕ × (S → ℝ≥0∞))) (hne : ns ≠ []) (hn : ∀ nf ∈ ns, 1 ≤ nf.1)
    (hm : ∀ nf ∈ ns, Measurable nf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedBlockProbability ns (η.map (logMarkShift (centeredLogMark ν b X))) z
      ∂weightedTotalBiasedLaw ν a b X) =
      (ns.map (fun nf => ∫⁻ c, nf.2 c ∂exponentialMarkTilt ν b X)).prod*
        (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η z ∂stableTotalBiasedLaw a b) := by
  let F := centeredLogMark ν b X
  have hF : Measurable F := centeredLogMark_measurable ν b hX
  have : IsProbabilityMeasure (exponentialMarkTilt ν b X) := exponentialMarkTilt_probability ν hI
  have hd := centeredLogMark_density ν hb.ne' hI
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) := by
    simpa only [F,hd] using (exponentialMarkTilt_probability ν hI)
  have he := weightedTotalBiasedLaw_shift (a := a) ν hb.le hF
  rw [weightedTotalBiasedLaw_centered ν a b hX] at he
  have hD : Measurable (fun η : Measure (ℝ × S) => markedBlockProbability ns η z) :=
    (markedBlockProbability_measurable ns hm m).comp (measurable_id.prodMk measurable_const)
  rw [← lintegral_map hD (Measure.measurable_map _ (logMarkShift_measurable hF)),he,
    markedBlockProbability_factor _ hb hb1 ha ns hne hn hm]
  simp only [F,hd]

end MarkedStable

def cascadeBiasedLaw (n : ℕ) (z : Fin n → ℝ) (a : ℝ) : Measure (StableCascade n) :=
  normalizedMeasure ((cascadeLaw n z : Measure (StableCascade n)).withDensity
    (fun η => ENNReal.ofReal (cascadeTotal n η^a)))

lemma cascadeLogTotalMoment_integrable (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : ∀ i, a < z i) :
    Integrable (fun η => Real.exp (a*Real.log (cascadeTotal n η)))
      (cascadeLaw n z : Measure (StableCascade n)) := by
  obtain ⟨hp,hi⟩ := cascadeTotal_regular n z hz hz0 hz1
  apply (hi a ha).congr
  filter_upwards [hp] with η hη
  rw [Real.rpow_def_of_pos hη,mul_comm]

lemma cascadeBiasedLaw_eq_exponentialTilt (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) :
    cascadeBiasedLaw n z a = exponentialMarkTilt (cascadeLaw n z) a
      (fun C => Real.log (cascadeTotal n C)) := by
  unfold cascadeBiasedLaw exponentialMarkTilt
  congr 1
  apply withDensity_congr_ae
  filter_upwards [(cascadeTotal_regular n z hz hz0 hz1).1] with C hC
  rw [Real.rpow_def_of_pos hC,mul_comm]

lemma cascadeBiasedLaw_probability (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : ∀ i, a < z i) :
    IsProbabilityMeasure (cascadeBiasedLaw n z a) := by
  rw [cascadeBiasedLaw_eq_exponentialTilt n z hz hz0 hz1 a]
  exact exponentialMarkTilt_probability _ (cascadeLogTotalMoment_integrable n z hz hz0 hz1 a ha)

lemma cascadeBiasedLaw_succ_eq_weighted {n : ℕ} (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) :
    cascadeBiasedLaw (n+1) z a = weightedTotalBiasedLaw
      (cascadeLaw n (fun i => z i.succ)) a (z 0) (fun C => Real.log (cascadeTotal n C)) := by
  have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
  have hp := (cascadeTotal_regular n (fun i => z i.succ) htail
    (fun i => hz0 i.succ) (fun i => hz1 i.succ)).1
  unfold cascadeBiasedLaw weightedTotalBiasedLaw
  congr 1
  apply withDensity_congr_ae
  filter_upwards [cascadeTotal_succ_eq z hp] with C hC
  rw [hC]

lemma cascadeRootBlock_factor {n : ℕ} (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) {a : ℝ} (ha : a < z 0)
    (ns : List (ℕ × (StableCascade n → ℝ≥0∞))) (hne : ns ≠ [])
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) :
    (∫⁻ η, markedBlockProbability ns
      (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
        (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)
      ∂cascadeBiasedLaw (n+1) z a) =
      (ns.map (fun nf => ∫⁻ C, nf.2 C ∂cascadeBiasedLaw n (fun i => z i.succ) (z 0))).prod *
      (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η (Fin.elim0 : Fin 0 → ℝ)
        ∂stableTotalBiasedLaw a (z 0)) := by
  have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
  have hM := cascadeLogTotalMoment_integrable n (fun i => z i.succ) htail
    (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) (fun i => hz (by simp))
  have he := weightedRootBlock_factor _ (hz0 0) (hz1 0) ha (cascadeTotal_measurable n).log hM ns hne hn hm (z := (Fin.elim0 : Fin 0 → ℝ))
  rw [← cascadeBiasedLaw_eq_exponentialTilt n (fun i => z i.succ) htail
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0)] at he
  rw [cascadeBiasedLaw_succ_eq_weighted z hz hz0 hz1 a]
  exact he

@[reducible] def CascadeVisitShape : ℕ → Type
  | 0 => ℕ
  | n+1 => List (CascadeVisitShape n)

def cascadeVisitCount : (n : ℕ) → CascadeVisitShape n → ℕ
  | 0, r => r
  | n+1, ss => (ss.map (cascadeVisitCount n)).sum

def CascadeVisitShape.Valid : (n : ℕ) → CascadeVisitShape n → Prop
  | 0, r => 1 ≤ r
  | n+1, ss => ss ≠ [] ∧ ∀ s ∈ ss, CascadeVisitShape.Valid n s

lemma cascadeVisitCount_pos (n : ℕ) (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    1 ≤ cascadeVisitCount n s := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    obtain ⟨hne,hs⟩ := hs
    change (s.map (cascadeVisitCount n)).sum ≥ 1
    cases s with
    | nil => exact (hne rfl).elim
    | cons h t =>
      simp only [List.map_cons,List.sum_cons]
      have := ih h (hs h (by simp))
      omega

def cascadeShapeProbability : (n : ℕ) → (Fin n → ℝ) → CascadeVisitShape n → StableCascade n → ℝ≥0∞
  | 0, _, _, _ => 1
  | n+1, z, ss, η => markedBlockProbability
      (ss.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)))
      (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
        (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)

lemma cascadeShapeProbability_measurable (n : ℕ) (z : Fin n → ℝ) (s : CascadeVisitShape n) :
    Measurable (cascadeShapeProbability n z s) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : ∀ nf ∈ s.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)),
        Measurable nf.2 := by
      intro nf hnf
      obtain ⟨s',_,rfl⟩ := List.mem_map.mp hnf
      exact ih (fun i => z i.succ) s'
    have hF := logMarkShift_measurable (centeredLogMark_measurable
      (cascadeLaw n (fun i => z i.succ)) (z 0) (cascadeTotal_measurable n).log)
    exact (markedBlockProbability_measurable _ hm 0).comp
      ((Measure.measurable_map _ hF).prodMk measurable_const)

def cascadeShapeLikelihood : (n : ℕ) → (Fin n → ℝ) → ℝ → CascadeVisitShape n → ℝ≥0∞
  | 0, _, _, _ => 1
  | n+1, z, a, ss =>
      (ss.map (cascadeShapeLikelihood n (fun i => z i.succ) (z 0))).prod *
      ENNReal.ofReal (stableEppfValue a (z 0) (ss.map (fun s => (cascadeVisitCount n s : ℝ))))

theorem cascadeShapeProbability_integral (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : ∀ i, a < z i)
    (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    (∫⁻ η, cascadeShapeProbability n z s η ∂cascadeBiasedLaw n z a) =
      cascadeShapeLikelihood n z a s := by
  induction n generalizing a with
  | zero =>
    have := cascadeBiasedLaw_probability 0 z hz hz0 hz1 a ha
    simp only [cascadeShapeProbability,cascadeShapeLikelihood,lintegral_const,measure_univ,mul_one]
  | succ n ih =>
    obtain ⟨hne,hs⟩ := hs
    let ns := s.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s))
    have hns : ns ≠ [] := by
      intro he
      apply hne
      exact List.map_eq_nil_iff.mp he
    have hn : ∀ nf ∈ ns, 1 ≤ nf.1 := by
      intro nf hnf; obtain ⟨s',hmem,rfl⟩ := List.mem_map.mp hnf
      exact cascadeVisitCount_pos n s' (hs s' hmem)
    have hm : ∀ nf ∈ ns, Measurable nf.2 := by
      intro nf hnf; obtain ⟨s',_,rfl⟩ := List.mem_map.mp hnf
      exact cascadeShapeProbability_measurable n (fun i => z i.succ) s'
    change (∫⁻ η, markedBlockProbability ns _ _ ∂cascadeBiasedLaw (n+1) z a) = _
    rw [cascadeRootBlock_factor z hz hz0 hz1 (ha 0) ns hns hn hm,
      stableBlockProbability_eppf (hz0 0) (hz1 0) (ha 0) (ns.map Prod.fst)
        (by simpa using hns) (by intro r hr; obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hr; exact hn nf hmem)]
    simp only [ns,List.map_map,Function.comp_def,cascadeShapeLikelihood,stableEppfValue,List.length_map]
    congr 2
    apply List.map_congr_left
    intro s' hmem
    exact ih (fun i => z i.succ) (fun i j h => hz (Fin.succ_lt_succ_iff.mpr h))
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) (fun i => hz (by simp)) s' (hs s' hmem)

end SphericalPerceptronFreeEnergy

end

end OAI
