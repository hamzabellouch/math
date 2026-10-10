import Mathlib
import OAI.Probability.Ballisticity.Walk.UpperKernel
import OAI.Probability.Ballisticity.Estimates.LocalStoppedSplice
import OAI.Probability.Ballisticity.Estimates.BoundedAnchorAverage

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DirectionalTransience

lemma independent_dyadic_centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ a, Measurable (X a)) (hB : ∀ a ω, |X a ω|≤1) (hi : iIndepFun X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun r : ℕ => sampleAverage X (2^r) ω-
      ∫ z, sampleAverage X (2^r) z ∂μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
      μ {ω | ε≤|sampleAverage X n ω-∫ z, sampleAverage X n z ∂μ|} ≤
        ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) :=
    (meas_ge_le_variance_div_sq (sampleAverage_memLp μ X hX hB n) hε).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (sampleAverage_variance_le μ X hX hB hi n hn) (sq_nonneg _)))
  have hbc (k : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ r : ℕ in atTop,
      ¬ 1/(k+1:ℝ)≤|sampleAverage X (2^r) ω-∫ z, sampleAverage X (2^r) z ∂μ| := by
    apply ae_eventually_notMem
    have hs : Summable (fun r : ℕ => ((2^r:ℕ):ℝ)⁻¹/(1/(k+1:ℝ))^2) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat,←inv_pow] using
        (summable_geometric_of_norm_lt_one (show ‖(2:ℝ)⁻¹‖<1 by norm_num)).div_const ((1/(k+1:ℝ))^2)
    exact ne_top_of_le_ne_top hs.tsum_ofReal_lt_top.ne
      (ENNReal.tsum_le_tsum (fun r => hbound (2^r) (by positivity) _ (by positivity)))
  filter_upwards [ae_all_iff.mpr hbc] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hω k)
  refine ⟨N,fun r hr => ?_⟩
  simpa only [Real.dist_eq,sub_zero] using (lt_of_not_ge (hN r hr)).trans hk

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience.ReferenceClasses
variable {H R : Type*} [AddCommGroup H]

lemma representative_singleton (O : Data H) (a : ℕ)
    (ha : ∀ b, related O a b → a=b) : representative O a=a :=
  (ha _ (related_symm (representative_related O a))).symm

lemma displacement_singleton (O : Data H) (a : ℕ)
    (ha : ∀ b, related O a b → a=b) : displacement O a=0 := by
  have h := displacement_spec O a
  rw [representative_singleton O a ha,O.2.self] at h
  exact (OnePoint.coe_injective h).symm

noncomputable def dustFrequency (dust : ℕ → Prop) (n : ℕ) : ℝ :=
  (n:ℝ)⁻¹*∑ a∈Finset.range n, if dust a then (1:ℝ) else 0

noncomputable def dustWeight (dust : ℕ → Prop) (q : UpperField H R → ℝ)
    (n : ℕ) (φ : AllFields H R) : ℝ :=
  sampleAverage (fun a φ => if dust a then q (fun p => φ (a,p)) else 0) n φ

variable [MeasurableSpace R]

omit [AddCommGroup H] in
lemma dustWeight_measurable (dust : ℕ → Prop) (q : UpperField H R → ℝ)
    (hq : Measurable q) (n : ℕ) : Measurable (dustWeight dust q n) := by
  unfold dustWeight sampleAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  split_ifs
  · exact hq.comp (Measurable.of_eval fun p => measurable_pi_apply (a,p))
  · exact measurable_const

variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]

lemma reference_dust_dyadic (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) (dust : ℕ → Prop)
    (hd : ∀ a, dust a → ∀ b, related O a b → a=b)
    (q : UpperField H R → ℝ) (hq : Measurable q) (hb : ∀ ξ, |q ξ|≤1) :
    ∀ᵐ φ ∂reference ν O, Tendsto (fun r : ℕ => dustWeight dust q (2^r) φ-
      (∫ ξ, q ξ ∂Measure.infinitePi (fun _ : ℕ×H => ν))*dustFrequency dust (2^r)) atTop (𝓝 0) := by
  let P := Measure.infinitePi (fun _ : ℕ×H => ν)
  let M := Measure.infinitePi (fun _ : ℕ => P)
  let X : ℕ → (ℕ → UpperField H R) → ℝ := fun a ξ => if dust a then q (ξ a) else 0
  have hXm (a : ℕ) : Measurable (X a) := by
    dsimp only [X]
    split_ifs
    · exact hq.comp (measurable_pi_apply a)
    · exact measurable_const
  have hXb (a : ℕ) (ξ : ℕ → UpperField H R) : |X a ξ|≤1 := by
    dsimp only [X]
    split_ifs
    · exact hb _
    · norm_num
  have hind : iIndepFun X M := iIndepFun_infinitePi
    (X:=fun a ξ => if dust a then q ξ else 0) (fun a => by split_ifs; exact hq; exact measurable_const)
  have hmean (a : ℕ) : (∫ ξ, X a ξ ∂M)=(∫ ξ, q ξ ∂P)*(if dust a then 1 else 0) := by
    dsimp only [X]
    split_ifs with ha
    · rw [mul_one]
      have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => P) a
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable hq.aestronglyMeasurable]
    · simp
  have hav (n : ℕ) : (∫ ξ, sampleAverage X n ξ ∂M)=(∫ ξ, q ξ ∂P)*dustFrequency dust n := by
    simp only [sampleAverage]
    rw [integral_const_mul,integral_finsetSum _ (fun a _ =>
      (integrable_const (1:ℝ)).mono' (hXm a).aestronglyMeasurable (Eventually.of_forall (hXb a)))]
    simp only [hmean,←Finset.mul_sum,dustFrequency]
    ring
  have hLL := independent_dyadic_centered M X hXm hXb hind
  simp only [hav] at hLL
  rw [reference_apply,←Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (_ : ℕ×H) => ν)]
  rw [Measure.map_map (show Measurable (fields O : AllFields H R → _) from measurable_fields.comp measurable_prodMk_left) (MeasurableEquiv.curry ℕ (ℕ×H) R).symm.measurable]
  apply (ae_map_iff (((show Measurable (fields O : AllFields H R → _) from measurable_fields.comp measurable_prodMk_left).comp (MeasurableEquiv.curry ℕ (ℕ×H) R).symm.measurable).aemeasurable) (measurableSet_tendsto (𝓝 (0:ℝ)) (fun r =>
    (dustWeight_measurable dust q hq (2^r)).sub_const _))).mpr
  filter_upwards [hLL] with ξ hξ
  convert hξ using 1
  funext r
  congr 1
  unfold dustWeight sampleAverage
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [X]
  split_ifs with ha
  · congr 1
    funext p
    simp only [Function.comp_def,fields,inputSite,representative_singleton O a (hd a ha),
      displacement_singleton O a (hd a ha),zero_add]
    rfl
  · rfl

end DirectionalTransience.ReferenceClasses

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def upperNoDrop {d : ℕ} (e : Direction d) (ξ : UpperRows e) : ℝ≥0∞ :=
  noDropQuenched (realPosition (step e)) 0 (upperEnvironment e ξ)

lemma upperNoDrop_measurable {d : ℕ} (e : Direction d) : Measurable (upperNoDrop e) :=
  (measurable_noDropQuenched _ _).comp (upperEnvironment_continuous e).measurable

lemma upperNoDrop_le_one {d : ℕ} (e : Direction d) (ξ : UpperRows e) : upperNoDrop e ξ≤1 := prob_le_one

lemma upperEnvironment_restrict_eq {d : ℕ} (e : Direction d) (ω : Environment d)
    (x : Lattice d) (hx : 0≤dot (realPosition x) (realPosition (step e))) :
    upperEnvironment e (upperField e 0 ω) x=ω x := by
  have hh : 0 ≤ signedHeight e x := by rw [signedHeight_projection] at hx; exact_mod_cast hx
  simp only [upperEnvironment,upperField,Nat.cast_zero,zero_add,Int.toNat_of_nonneg hh,horizontalLift_projection]

lemma upperNoDrop_restrict {d : ℕ} (e : Direction d) (ω : Environment d) :
    upperNoDrop e (upperField e 0 ω)=noDropQuenched (realPosition (step e)) 0 ω := by
  apply quenched_stay_congr {x | dot (realPosition (0:Lattice d)) (realPosition (step e))≤
      dot (realPosition x) (realPosition (step e))}
  intro x hx
  apply upperEnvironment_restrict_eq e ω x
  simpa only [realPosition,Int.cast_zero,Pi.zero_apply,dot,zero_mul,Finset.sum_const_zero] using (show dot (realPosition (0:Lattice d)) (realPosition (step e)) ≤ dot (realPosition x) (realPosition (step e)) from hx)

lemma upperKernel_restrict {d : ℕ} (e : Direction d) (ω : Environment d) (H : ℕ) :
    upperHorizontalKernel e H (upperField e 0 ω) 0 Set.univ=
      crossingQuenched (realPosition (step e)) 0 H ω := by
  rw [upperHorizontalKernel_apply,Set.preimage_univ,crossingQuenched_eq_hitKernel]
  have hz : horizontalLift e 0 0=0 := by simp [horizontalLift]
  rw [hz]
  apply congrArg (fun μ : Measure (Lattice d) => μ Set.univ)
  apply hitKernel_congr
  intro x hx
  apply upperEnvironment_restrict_eq e ω x
  have hh := hx.1
  simpa only [realPosition,Int.cast_zero,Pi.zero_apply,dot,zero_mul,Finset.sum_const_zero] using hh

lemma upperNoDrop_le_kernel_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∀ᵐ ξ ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν),
      ∀ H : ℕ, upperNoDrop e ξ ≤ upperHorizontalKernel e H ξ 0 Set.univ := by
  rw [←upperField_map e ν 0]
  apply (ae_map_iff ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl).aemeasurable
    (by
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro H
      exact measurableSet_le (upperNoDrop_measurable e)
        (upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).measurable)).mpr
  filter_upwards [crossingQuenched_tendsto_ae ν _ htrans] with ω hω H
  rw [upperNoDrop_restrict,upperKernel_restrict]
  apply le_of_tendsto (hω 0)
  filter_upwards [eventually_ge_atTop H] with n hn
  exact crossingQuenched_antitone _ _ _ (by exact_mod_cast hn)

lemma upperNoDrop_positive_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∀ᵐ ξ ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν), 0<upperNoDrop e ξ := by
  rw [←upperField_map e ν 0]
  apply (ae_map_iff ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl).aemeasurable
    (measurableSet_lt measurable_const (upperNoDrop_measurable e))).mpr
  filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue _ (signed_direction_unit e) htrans] with ω hω
  rw [upperNoDrop_restrict]
  exact hω 0

lemma upperNoDrop_inverse_moment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam : ℝ, 0<lam ∧ (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi
      (fun _ : ℕ×HorizontalSpace e => ν))<⊤ := by
  obtain ⟨lam,hlam,hlamfin⟩ := noDrop_inverse_moment ν hue _ (signed_direction_unit e) htrans
  refine ⟨lam,hlam,?_⟩
  rw [←upperField_map e ν 0,lintegral_map ((upperNoDrop_measurable e).pow_const (-lam))
    ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl)]
  simpa only [upperNoDrop_restrict] using hlamfin

end DirectionalTransience

end

end OAI
