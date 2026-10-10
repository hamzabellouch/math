import Mathlib
import OAI.Probability.Perceptron.Variational.StableTotalBiasedLaw

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
variable {S : Type*} [MeasurableSpace S]
variable [Nonempty S]
omit [Nonempty S] in
lemma markedDistinctMoment_add_dirac (rs : List (ℝ × (S → ℝ≥0∞)))
    (hr : ∀ rf ∈ rs, Measurable rf.2) (η : Measure (ℝ × S)) (p : ℝ × S)
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η)
    {m : ℕ} (z : Fin m → ℝ) (hz : ∃ i, z i = p.1) :
    markedDistinctMoment rs (Measure.dirac p+η) z = markedDistinctMoment rs η z := by
  induction rs generalizing m with
  | nil => rfl
  | cons rf rs ih =>
    have ht : ∀ r ∈ rs, Measurable r.2 := fun r hr' => hr r (List.mem_cons_of_mem rf hr')
    have hm : Measurable (fun q : ℝ × S => if ∃ i, z i = q.1 then (0:ℝ≥0∞) else
        ENNReal.ofReal (Real.exp (rf.1*q.1))*rf.2 q.2*
          markedDistinctMoment rs (Measure.dirac p+η) (Fin.cons q.1 z)) := by
      have hF : Measurable (fun q : ℝ × S => ENNReal.ofReal (Real.exp (rf.1*q.1))*rf.2 q.2) :=
        (by fun_prop : Measurable (fun q : ℝ × S => ENNReal.ofReal (Real.exp (rf.1*q.1)))).mul
          ((hr rf (by simp)).comp measurable_snd)
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_fst)
        (hF.mul ((markedDistinctMoment_measurable rs ht (m+1)).comp
            (measurable_const.prodMk (measurable_fin_cons measurable_fst measurable_const))))
    rw [markedDistinctMoment,markedStableCountKernel_add_dirac η p hf hp,
      lintegral_add_measure,lintegral_dirac' _ hm,ite_eq_left hz,zero_add,
      markedDistinctMoment,markedStableCountKernel_eq η hf hp]
    apply lintegral_congr
    intro q
    split_ifs
    · rfl
    · rw [ih ht (Fin.cons q.1 z) (by obtain ⟨i,hi⟩ := hz; exact ⟨i.succ,hi⟩)]

lemma markedDistinctMoment_palm_laplace (ν : Measure S) [IsProbabilityMeasure ν]
    {b t : ℝ} (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*markedStableTotal η))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      ((rs.map (fun rf => ENNReal.ofReal (b*t^(b-rf.1)*Real.Gamma (rf.1-b))*(∫⁻ c, rf.2 c ∂ν))).prod)*
        ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  induction rs generalizing m with
  | nil => simpa [markedDistinctMoment] using markedStable_laplace ν hb hb1 ht
  | cons rf rs ih =>
    have hmt : ∀ r ∈ rs, Measurable r.2 := fun r hr' => hm r (List.mem_cons_of_mem rf hr')
    let P := poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)
    let L := ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b))
    let C := (rs.map (fun r => ENNReal.ofReal (b*t^(b-r.1)*Real.Gamma (r.1-b))*(∫⁻ c, r.2 c ∂ν))).prod
    let H : Measure (ℝ × S) × (ℝ × S) → ℝ≥0∞ := fun p => if ∃ i, z i = p.2.1 then 0 else
      ENNReal.ofReal (Real.exp (rf.1*p.2.1))*rf.2 p.2.2*
        markedDistinctMoment rs p.1 (Fin.cons p.2.1 z)*
        ENNReal.ofReal (Real.exp (-t*markedStableTotal p.1))
    have hH : Measurable H := by
      have hD : Measurable (fun p : Measure (ℝ × S) × (ℝ × S) =>
          markedDistinctMoment rs p.1 (Fin.cons p.2.1 z)) :=
        (markedDistinctMoment_measurable rs hmt (m+1)).comp (measurable_fst.prodMk
          (measurable_fin_cons measurable_snd.fst measurable_const))
      have hF : Measurable (fun p : Measure (ℝ × S) × (ℝ × S) =>
          ENNReal.ofReal (Real.exp (rf.1*p.2.1))*rf.2 p.2.2) :=
        (by fun_prop : Measurable (fun p : Measure (ℝ × S) × (ℝ × S) => ENNReal.ofReal (Real.exp (rf.1*p.2.1)))).mul
          ((hm rf (by simp)).comp measurable_snd.snd)
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_snd.fst) ((hF.mul hD).mul (by fun_prop))
    have hstart : (∫⁻ η, markedDistinctMoment (rf::rs) η z*
        ENNReal.ofReal (Real.exp (-t*markedStableTotal η)) ∂P) =
        ∫⁻ η, ∫⁻ p, H (η,p) ∂η ∂P := by
      apply lintegral_congr_ae
      filter_upwards [markedStable_regular ν hb hb1] with η hη
      rw [markedDistinctMoment,markedStableCountKernel_eq η hη.1 hη.2,
        ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro p
      dsimp [H]
      split_ifs <;> simp
    have hinner (p : ℝ × S) : (∫⁻ η, H (Measure.dirac p+η,p) ∂P) =
        (if ∃ i, z i = p.1 then 0 else ENNReal.ofReal (Real.exp (rf.1*p.1)*Real.exp (-t*Real.exp p.1))*rf.2 p.2)*(C*L) := by
      by_cases hx : ∃ i, z i = p.1
      · simp [H,hx]
      have he : (fun η => H (Measure.dirac p+η,p)) =ᵐ[P]
          (fun η => (ENNReal.ofReal (Real.exp (rf.1*p.1)*Real.exp (-t*Real.exp p.1))*rf.2 p.2)*
            (markedDistinctMoment rs η (Fin.cons p.1 z)*ENNReal.ofReal (Real.exp (-t*markedStableTotal η)))) := by
        filter_upwards [markedStable_regular ν hb hb1] with η hη
        dsimp [H]
        rw [ite_eq_right hx,markedDistinctMoment_add_dirac rs hmt η p hη.1 hη.2
          (Fin.cons p.1 z) ⟨0,rfl⟩,markedStableTotal_add_dirac p η hη.1,mul_add,Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      have hM : Measurable (fun η => markedDistinctMoment rs η (Fin.cons p.1 z)*
          ENNReal.ofReal (Real.exp (-t*markedStableTotal η))) :=
        ((markedDistinctMoment_measurable rs hmt (m+1)).comp (measurable_id.prodMk measurable_const)).mul (by fun_prop)
      rw [lintegral_congr_ae he,lintegral_const_mul _ hM,
        ih (fun r hr' => hr r (List.mem_cons_of_mem rf hr')) hmt (Fin.cons p.1 z),ite_eq_right hx]
    rw [hstart,poissonRandomMeasureLaw_mecke _ hH]
    change (∫⁻ p, ∫⁻ η, H (Measure.dirac p+η,p) ∂P ∂(stableLogIntensity b).prod ν) = _
    simp_rw [hinner]
    rw [lintegral_mul_const]
    · have hx : ∀ᵐ x ∂stableLogIntensity b, ¬ ∃ i, z i = x := by
        filter_upwards [ae_all_iff.mpr (fun i : Fin m => (stableLogIntensity b).ae_ne (z i))] with x hx
        exact fun h => by obtain ⟨i,hi⟩ := h; exact hx i hi.symm
      have hp : ∀ᵐ p ∂(stableLogIntensity b).prod ν, ¬ ∃ i, z i = p.1 :=
        (measurePreserving_fst (μ := stableLogIntensity b) (ν := ν)).quasiMeasurePreserving.ae hx
      rw [lintegral_congr_ae (hp.mono fun p hp => ite_eq_right hp),lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (Real.exp (rf.1*x)*Real.exp (-t*Real.exp x)))
          (g := rf.2) (by fun_prop) (hm rf (by simp)).aemeasurable,
        stableLogIntensity_laplace_moment hb.le (hr rf (by simp)) ht]
      simp only [List.map_cons,List.prod_cons]
      dsimp [C,L]
      ring
    · exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_fst)
        ((by fun_prop : Measurable (fun p : ℝ × S => ENNReal.ofReal (Real.exp (rf.1*p.1)*Real.exp (-t*Real.exp p.1)))).mul ((hm rf (by simp)).comp measurable_snd))

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
  simp only [normalizedMeasure,Measure.map_smul _ hf.aemeasurable,
    Measure.map_apply hf MeasurableSet.univ,Set.preimage_univ]

omit [Nonempty S] in
lemma markedStableMassKernel_projection (η : Measure (ℝ × S)) :
    (markedStableMassKernel η).map Prod.fst = stableMassKernel (η.map Prod.fst) := by
  change (normalizedMeasure (η.withDensity (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1)))).map Prod.fst =
    normalizedMeasure ((η.map Prod.fst).withDensity (fun x => ENNReal.ofReal (Real.exp x)))
  rw [normalizedMeasure_map _ measurable_fst,map_withDensity_comp η measurable_fst (by fun_prop)]
  rfl

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

end SphericalPerceptronFreeEnergy

end

end OAI
