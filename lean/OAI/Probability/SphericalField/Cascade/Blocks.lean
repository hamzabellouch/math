import Mathlib
import OAI.Probability.SphericalField.Poisson.WeightedTotal
import OAI.Probability.SphericalField.Cascade.MarkedMass

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable
section MarkedStable
variable {S : Type*} [MeasurableSpace S]
variable [Nonempty S]
def markedBlockProbability : List (ℕ × (S → ℝ≥0∞)) → {m : ℕ} → Measure (ℝ × S) → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | nf::ns, _, η, z => ∫⁻ p, if ∃ i, z i = p.1 then 0 else
      (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*
        markedBlockProbability ns η (Fin.cons p.1 z) ∂markedStableMassKernel η

omit [Nonempty S] in
lemma markedBlockProbability_measurable (ns : List (ℕ × (S → ℝ≥0∞)))
    (hm : ∀ nf ∈ ns, Measurable nf.2) (m : ℕ) :
    Measurable (fun p : Measure (ℝ × S) × (Fin m → ℝ) => markedBlockProbability ns p.1 p.2) := by
  induction ns generalizing m with
  | nil => exact measurable_const
  | cons nf ns ih =>
    let κ : Kernel (Measure (ℝ × S) × (Fin m → ℝ)) (ℝ × S) := markedStableMassKernel.comap
      (Prod.fst : Measure (ℝ × S) × (Fin m → ℝ) → Measure (ℝ × S)) measurable_fst
    have hD : Measurable (fun p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) =>
        markedBlockProbability ns p.1.1 (Fin.cons p.2.1 p.1.2)) := by
      exact (ih (fun r hr' => hm r (List.mem_cons_of_mem nf hr')) (m+1)).comp
        (measurable_fst.fst.prodMk (measurable_fin_cons measurable_snd.fst measurable_fst.snd))
    have ha : Measurable (fun p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) =>
        stableMassKernel (p.1.1.map Prod.fst) {p.2.1}) :=
      stableMassAtom_measurable_comp ((Measure.measurable_map _ measurable_fst).comp measurable_fst.fst) measurable_snd.fst
    have hset : MeasurableSet {p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) | ∃ i, p.1.2 i = p.2.1} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd.fst
    exact (measurable_const.ite hset (((ha.pow_const _).mul ((hm nf (by simp)).comp measurable_snd.snd)).mul hD)).lintegral_kernel_prod_right' (κ := κ)

omit [Nonempty S] in
lemma markedBlockProbability_moment (ns : List (ℕ × (S → ℝ≥0∞)))
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η)
    (hs : ∀ᵐ x ∂η.map Prod.fst, (η.map Prod.fst) {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    markedBlockProbability ns η z = markedDistinctMoment (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η z*
      ((ENNReal.ofReal (markedStableTotal η))⁻¹)^(ns.map Prod.fst).sum := by
  induction ns generalizing m with
  | nil => simp [markedBlockProbability,markedDistinctMoment]
  | cons nf ns ih =>
    have hn0 : 1 ≤ nf.1 := hn nf (by simp)
    have hn' : nf.1-1+1 = nf.1 := Nat.sub_add_cancel hn0
    have hns : ∀ k ∈ ns, 1 ≤ k.1 := fun k hk => hn k (by simp [hk])
    have hmt : ∀ k ∈ ns, Measurable k.2 := fun k hk => hm k (by simp [hk])
    have ha : Measurable (fun p : ℝ × S => stableMassKernel (η.map Prod.fst) {p.1}) :=
      stableMassAtom_measurable_comp measurable_const measurable_fst
    have hmeas : Measurable (fun p : ℝ × S => if ∃ i, z i = p.1 then (0:ℝ≥0∞) else
        (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*
          markedBlockProbability ns η (Fin.cons p.1 z)) := by
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_fst)
        (((ha.pow_const _).mul ((hm nf (by simp)).comp measurable_snd)).mul
          ((markedBlockProbability_measurable ns hmt (m+1)).comp
            (measurable_const.prodMk (measurable_fin_cons measurable_fst measurable_const))))
    have htotal : (η.withDensity (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1))) univ =
        ENNReal.ofReal (markedStableTotal η) := by
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      exact (ENNReal.ofReal_toReal hf).symm
    unfold markedBlockProbability
    change (∫⁻ p, (if ∃ i, z i = p.1 then 0 else (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*
      markedBlockProbability ns η (Fin.cons p.1 z)) ∂normalizedMeasure
        (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)))) = _
    rw [normalizedMeasure,lintegral_smul_measure,htotal,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hmeas]
    simp only [smul_eq_mul,Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp))]
    have hpoint : (fun p : ℝ × S => (ENNReal.ofReal (markedStableTotal η))⁻¹ *
        (ENNReal.ofReal (Real.exp p.1)*(if ∃ i, z i = p.1 then 0 else
          (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*markedBlockProbability ns η (Fin.cons p.1 z)))) =ᵐ[η]
        (fun p : ℝ × S => (if ∃ i, z i = p.1 then 0 else ENNReal.ofReal (Real.exp ((nf.1:ℝ)*p.1))*nf.2 p.2*
          markedDistinctMoment (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η (Fin.cons p.1 z))*
          ((ENNReal.ofReal (markedStableTotal η))⁻¹)^(nf.1+(ns.map Prod.fst).sum)) := by
      filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hs] with p hx
      split_ifs
      · simp
      · rw [stableMassKernel_atom_eq (η.map Prod.fst) (by simpa [← markedStableTotalE_projection] using hf)
          (by simpa [← markedStableTotal_projection] using hp) hx,← markedStableTotal_projection,
          ENNReal.ofReal_div_of_pos hp,ih hns hmt (Fin.cons p.1 z),div_eq_mul_inv,mul_pow,
          Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_pos _).le,pow_add,← hn',pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
    rw [lintegral_congr_ae hpoint,lintegral_mul_const' _ _ (ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp)))]
    simp only [List.map_cons,List.sum_cons]
    rw [markedDistinctMoment,markedStableCountKernel_eq η hf hp]

omit [Nonempty S] in
lemma markedBlockProbability_ordered (ns : List (ℕ × (S → ℝ≥0∞)))
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η)
    (hs : ∀ᵐ x ∂η.map Prod.fst, (η.map Prod.fst) {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    markedBlockProbability ns η z = markedOrderedDistinctMass (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η z := by
  rw [markedBlockProbability_moment ns hn hm η hf hp hs]
  unfold markedOrderedDistinctMass
  congr 1
  rw [Real.rpow_neg hp.le,ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hp _)]
  have hsum : ((ns.map (fun nf => ((nf.1:ℝ),nf.2))).map Prod.fst).sum = ((ns.map Prod.fst).sum:ℝ) := by
    simpa only [List.map_map,Function.comp_def] using
      (Nat.cast_list_sum (R := ℝ) (ns.map Prod.fst)).symm
  rw [hsum,Real.rpow_natCast,ENNReal.ofReal_pow hp.le,ENNReal.inv_pow]

lemma markedTotalBiasedLaw_absolutelyContinuous (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) :
    markedTotalBiasedLaw ν a b ≪ poissonRandomMeasureLaw ((stableLogIntensity b).prod ν) := by
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

lemma markedBlockProbability_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (ns : List (ℕ × (S → ℝ≥0∞))) (hne : ns ≠ []) (hn : ∀ nf ∈ ns, 1 ≤ nf.1)
    (hm : ∀ nf ∈ ns, Measurable nf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedBlockProbability ns η z ∂markedTotalBiasedLaw ν a b) =
      (ns.map (fun nf => ∫⁻ c, nf.2 c ∂ν)).prod*
        (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η z ∂stableTotalBiasedLaw a b) := by
  have hr : ∀ rf ∈ ns.map (fun nf => ((nf.1:ℝ),nf.2)), b < rf.1 := by
    intro rf hr
    obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hr
    exact hb1.trans_le (by change (1:ℝ) ≤ (nf.1:ℝ); exact_mod_cast hn nf hmem)
  have hm' : ∀ rf ∈ ns.map (fun nf => ((nf.1:ℝ),nf.2)), Measurable rf.2 := by
    intro rf hr
    obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hr
    exact hm nf hmem
  have he := markedOrderedDistinctMass_eppf ν hb hb1 ha (ns.map (fun nf => ((nf.1:ℝ),nf.2)))
    (by simpa using hne) hr hm' z
  have hpres : MeasurePreserving (Measure.map (Prod.fst : ℝ × S → ℝ))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ measurable_fst,markedStable_project_law ν b⟩
  have hs := hpres.quasiMeasurePreserving.ae (stablePoissonCount_simple hb hb1)
  have hae : (fun η => markedBlockProbability ns η z) =ᵐ[markedTotalBiasedLaw ν a b]
      (fun η => markedOrderedDistinctMass (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η z) := by
    apply (markedTotalBiasedLaw_absolutelyContinuous ν a b).ae_eq
    filter_upwards [markedStable_regular ν hb hb1,hs] with η hf hs
    exact markedBlockProbability_ordered ns hn hm η hf.1 hf.2 hs z
  rw [lintegral_congr_ae hae,he,stableBlockProbability_eppf hb hb1 ha (ns.map Prod.fst)
    (by simpa using hne) (by intro n hn'; obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hn'; exact hn nf hmem)]
  simp only [List.map_map,Function.comp_def,List.length_map]

omit [Nonempty S] in
lemma markedStableTotal_map_shift (η : Measure (ℝ × S)) {F : S → ℝ} (hF : Measurable F) :
    markedStableTotal (η.map (logMarkShift F)) = poissonWeightedTotal F η := by
  unfold markedStableTotal markedStableTotalE poissonWeightedTotal
  rw [lintegral_map (by fun_prop) (logMarkShift_measurable hF)]
  rfl

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
    rw [mul_sub,show b*(Real.log (∫ y, Real.exp (b*X y) ∂ν)/b) = Real.log M by dsimp [M]; field_simp [hb],
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

end SphericalPerceptron
end
end
end

end OAI
