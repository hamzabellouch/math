import Mathlib
import OAI.Probability.SphericalField.Poisson.BiasedLaw
import OAI.Probability.SphericalField.Cascade.MarkedStable

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
lemma markedDistinctMoment_laplace_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {b t : ℝ} (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*markedStableTotal η))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      (rs.map (fun rf => ∫⁻ c, rf.2 c ∂ν)).prod*
        (∫⁻ η, stableDistinctMoment (rs.map Prod.fst) η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
          ∂poissonRandomMeasureLaw (stableLogIntensity b)) := by
  rw [markedDistinctMoment_palm_laplace ν hb hb1 ht rs hr hm,
    stableDistinctMoment_palm_laplace hb hb1 ht (rs.map Prod.fst)
      (by intro r hr'; obtain ⟨rf,hmem,rfl⟩ := List.mem_map.mp hr'; exact hr rf hmem)]
  simp only [List.prod_map_mul,List.map_map,Function.comp_def]
  ring

omit [Nonempty S] in
lemma mellin_weighted_identity (μ : Measure S) [SFinite μ] {D : S → ℝ≥0∞} {T : S → ℝ}
    (hD : Measurable D) (hT : Measurable T) (hpos : ∀ᵐ x ∂μ, 0 < T x) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, D x*ENNReal.ofReal (T x^(-q)) ∂μ)*ENNReal.ofReal (Real.Gamma q) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^(q-1))*
        (∫⁻ x, D x*ENNReal.ofReal (Real.exp (-t*T x)) ∂μ) := by
  have hm : Measurable (fun p : S × ℝ => D p.1*ENNReal.ofReal (p.2^(q-1)*Real.exp (-p.2*T p.1))) :=
    (hD.comp measurable_fst).mul (by fun_prop)
  calc
    _ = ∫⁻ x, D x*ENNReal.ofReal (T x^(-q))*ENNReal.ofReal (Real.Gamma q) ∂μ :=
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x, (∫⁻ t : ℝ in Ioi 0, D x*ENNReal.ofReal (t^(q-1)*Real.exp (-t*T x))) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with x hx
      rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_positive_scale hq hx,
        ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),mul_assoc]
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ x, D x*ENNReal.ofReal (t^(q-1)*Real.exp (-t*T x)) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),show ∀ x,
        D x*(ENNReal.ofReal (t^(q-1))*ENNReal.ofReal (Real.exp (-t*T x))) =
        ENNReal.ofReal (t^(q-1))*(D x*ENNReal.ofReal (Real.exp (-t*T x))) from fun x => by ring]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma markedDistinctMoment_mellin_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hne : rs ≠ []) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (markedStableTotal η^(a-(rs.map Prod.fst).sum))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      (rs.map (fun rf => ∫⁻ c, rf.2 c ∂ν)).prod*
        (∫⁻ η, stableDistinctMoment (rs.map Prod.fst) η z*ENNReal.ofReal (stablePoissonTotal η^(a-(rs.map Prod.fst).sum))
          ∂poissonRandomMeasureLaw (stableLogIntensity b)) := by
  let q := (rs.map Prod.fst).sum-a
  have hrr : ∀ r ∈ rs.map Prod.fst, b < r := by
    intro r hr'; obtain ⟨rf,hmem,rfl⟩ := List.mem_map.mp hr'; exact hr rf hmem
  have hj : (1:ℝ) ≤ rs.length := by
    have hj : 1 ≤ rs.length := by cases rs <;> simp_all
    exact_mod_cast hj
  have hq : 0 < q := by
    have hs := list_length_mul_le_sum (fun r hr' => (hrr r hr').le)
    simp only [List.length_map] at hs
    dsimp [q]; nlinarith
  have hG0 : ENNReal.ofReal (Real.Gamma q) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.Gamma_pos_of_pos hq)
  have hDm : Measurable (fun η => markedDistinctMoment rs η z) :=
    (markedDistinctMoment_measurable rs hm m).comp (measurable_id.prodMk measurable_const)
  have hDu : Measurable (fun η => stableDistinctMoment (rs.map Prod.fst) η z) :=
    (stableDistinctMoment_measurable (rs.map Prod.fst) m).comp (measurable_id.prodMk measurable_const)
  have h1 := mellin_weighted_identity _ hDm markedStableTotal_measurable
    ((markedStable_regular ν hb hb1).mono fun _ h => h.2) hq
  have h2 := mellin_weighted_identity _ hDu stablePoissonTotal_measurable (stablePoissonTotal_pos hb hb1) hq
  have hneg : -q = a-(rs.map Prod.fst).sum := by dsimp [q]; ring
  rw [hneg] at h1 h2
  apply (ENNReal.mul_left_inj hG0 ENNReal.ofReal_ne_top).mp
  rw [h1,mul_assoc,h2]
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal (t^(q-1))*
      (∫⁻ η, stableDistinctMoment (rs.map Prod.fst) η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
        ∂poissonRandomMeasureLaw (stableLogIntensity b))) := by
    apply (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t^(q-1)))).mul
    have hM : Measurable (fun p : ℝ × Measure ℝ => stableDistinctMoment (rs.map Prod.fst) p.2 z*
        ENNReal.ofReal (Real.exp (-p.1*stablePoissonTotal p.2))) := (hDu.comp measurable_snd).mul (by fun_prop)
    exact hM.lintegral_prod_right
  rw [← lintegral_const_mul _ hmeas]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [markedDistinctMoment_laplace_factor ν hb hb1 ht rs hr hm]
  ring

def markedTotalBiasedLaw (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) : Measure (Measure (ℝ × S)) :=
  normalizedMeasure ((poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).withDensity
    (fun η => ENNReal.ofReal (markedStableTotal η^a)))

lemma markedStableTotal_momentE (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) :
    (∫⁻ η, ENNReal.ofReal (markedStableTotal η^a) ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      ∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a) ∂poissonRandomMeasureLaw (stableLogIntensity b) := by
  rw [← markedStable_project_law ν b,
    lintegral_map (by fun_prop) (Measure.measurable_map _ measurable_fst)]
  simp only [markedStableTotal_projection]

lemma markedTotalBiasedLaw_probability (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b) :
    IsProbabilityMeasure (markedTotalBiasedLaw ν a b) := by
  have hmass : ((poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).withDensity
      (fun η => ENNReal.ofReal (markedStableTotal η^a))) univ =
        ((poissonRandomMeasureLaw (stableLogIntensity b)).withDensity
          (fun η => ENNReal.ofReal (stablePoissonTotal η^a))) univ := by
    simp only [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact markedStableTotal_momentE ν a b
  have hp : 0 < Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)/Real.Gamma (1-a) := by
    apply div_pos (mul_pos (Real.Gamma_pos_of_pos ?_) (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)) _))
      (Real.Gamma_pos_of_pos (by linarith))
    have := (div_lt_one hb).mpr ha
    linarith
  apply normalizedMeasure_probability
  · rw [hmass,stableTotalBias_mass hb hb1 ha]; exact ENNReal.ofReal_ne_zero_iff.mpr hp
  · rw [hmass,stableTotalBias_mass hb hb1 ha]; exact ENNReal.ofReal_ne_top

def markedOrderedDistinctMass (rs : List (ℝ × (S → ℝ≥0∞))) (η : Measure (ℝ × S)) {m : ℕ} (z : Fin m → ℝ) : ℝ≥0∞ :=
  markedDistinctMoment rs η z*ENNReal.ofReal (markedStableTotal η^(-(rs.map Prod.fst).sum))

omit [Nonempty S] in
lemma markedOrderedDistinctMass_measurable (rs : List (ℝ × (S → ℝ≥0∞)))
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    Measurable (fun η => markedOrderedDistinctMass rs η z) :=
  ((markedDistinctMoment_measurable rs hm m).comp (measurable_id.prodMk measurable_const)).mul (by fun_prop)

lemma markedOrderedDistinctMass_biased (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (rs : List (ℝ × (S → ℝ≥0∞)))
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedOrderedDistinctMass rs η z ∂markedTotalBiasedLaw ν a b) =
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (markedStableTotal η^(a-(rs.map Prod.fst).sum))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))/
      (∫⁻ η, ENNReal.ofReal (markedStableTotal η^a)
        ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) := by
  unfold markedTotalBiasedLaw normalizedMeasure
  rw [lintegral_smul_measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (markedOrderedDistinctMass_measurable rs hm z)]
  simp only [smul_eq_mul,Pi.mul_apply]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [markedStable_regular ν hb hb1] with η hη
  unfold markedOrderedDistinctMass
  calc
    _ = markedDistinctMoment rs η z*(ENNReal.ofReal (markedStableTotal η^a)*
      ENNReal.ofReal (markedStableTotal η^(-(rs.map Prod.fst).sum))) := by ring
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hη.2.le _),← Real.rpow_add hη.2,sub_eq_add_neg]

lemma markedOrderedDistinctMass_eppf (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hne : rs ≠ []) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedOrderedDistinctMass rs η z ∂markedTotalBiasedLaw ν a b) =
      (rs.map (fun rf => ∫⁻ c, rf.2 c ∂ν)).prod*
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma ((rs.map Prod.fst).sum-a)*
        (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
        (rs.map (fun rf => Real.Gamma (rf.1-b)/Real.Gamma (1-b))).prod) := by
  rw [markedOrderedDistinctMass_biased ν hb hb1 rs hm z,
    markedDistinctMoment_mellin_factor ν hb hb1 ha rs hne hr hm,
    markedStableTotal_momentE ν a b,mul_div_assoc,stableDistinctMoment_eppf hb hb1 ha (rs.map Prod.fst)
      (by simpa using hne) (by intro r hr'; obtain ⟨rf,hmem,rfl⟩ := List.mem_map.mp hr'; exact hr rf hmem)]
  simp only [List.length_map,List.map_map,Function.comp_def]

omit [Nonempty S] in
lemma normalizedMeasure_map {A : Type*} [MeasurableSpace A] (μ : Measure S)
    {f : S → A} (hf : Measurable f) :
    (normalizedMeasure μ).map f = normalizedMeasure (μ.map f) := by
  simp only [normalizedMeasure, Measure.map_smul _ hf.aemeasurable,
    Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

omit [Nonempty S] in
lemma markedStableMassKernel_projection (η : Measure (ℝ × S)) :
    (markedStableMassKernel η).map Prod.fst = stableMassKernel (η.map Prod.fst) := by
  change (normalizedMeasure (η.withDensity (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1)))).map Prod.fst =
    normalizedMeasure ((η.map Prod.fst).withDensity (fun x => ENNReal.ofReal (Real.exp x)))
  rw [normalizedMeasure_map _ measurable_fst,map_withDensity_comp η measurable_fst (by fun_prop)]
  rfl

end MarkedStable
end SphericalPerceptron
end
end
end

end OAI
