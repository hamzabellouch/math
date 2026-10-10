import Mathlib
import OAI.Probability.SphericalField.Poisson.DistinctMoments

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

lemma markedStableTotalE_projection (η : Measure (ℝ × S)) :
    markedStableTotalE η = stableJumpMomentE 1 (η.map Prod.fst) := by
  simp only [markedStableTotalE,stableJumpMomentE,one_mul]
  rw [lintegral_map (by fun_prop) measurable_fst]

lemma markedStableTotal_projection (η : Measure (ℝ × S)) :
    markedStableTotal η = stablePoissonTotal (η.map Prod.fst) := by
  simp only [markedStableTotal,markedStableTotalE_projection,stableJumpMomentE,one_mul,stablePoissonTotal]

instance markedStableCountKernel_sfinite : IsSFiniteKernel (markedStableCountKernel (S := S)) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

lemma markedStableCountKernel_eq (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η) :
    markedStableCountKernel η = η := by
  rw [markedStableCountKernel,Kernel.withDensity_apply _ (by fun_prop : Measurable
    (Function.uncurry (fun (η : Measure (ℝ × S)) (p : ℝ × S) => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1)))))]
  change (((η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ)⁻¹) •
    η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1))).withDensity
      (fun p => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) = η
  have hmass : η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ =
      ENNReal.ofReal (markedStableTotal η) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ENNReal.ofReal_toReal hf).symm
  rw [hmass,withDensity_smul_measure,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have hd : (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1)*
      ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) =
      (fun _ : ℝ × S => ENNReal.ofReal (markedStableTotal η)) := by
    funext p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.exp_neg]
    field_simp
  change (ENNReal.ofReal (markedStableTotal η))⁻¹ • η.withDensity
    (fun p => ENNReal.ofReal (Real.exp p.1)*ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) = η
  rw [hd,withDensity_const,smul_smul,ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,one_smul]

lemma markedStableTotalE_add_dirac (p : ℝ × S) (η : Measure (ℝ × S)) :
    markedStableTotalE (Measure.dirac p+η) = ENNReal.ofReal (Real.exp p.1)+markedStableTotalE η := by
  simp only [markedStableTotalE,lintegral_add_measure]
  rw [lintegral_dirac' _ (by fun_prop)]

lemma markedStableTotal_add_dirac (p : ℝ × S) (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) :
    markedStableTotal (Measure.dirac p+η) = Real.exp p.1+markedStableTotal η := by
  rw [markedStableTotal,markedStableTotalE_add_dirac,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hf,ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rfl

lemma markedStableCountKernel_add_dirac (η : Measure (ℝ × S)) (p : ℝ × S)
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η) :
    markedStableCountKernel (Measure.dirac p+η) = Measure.dirac p+η := by
  apply markedStableCountKernel_eq
  · rw [markedStableTotalE_add_dirac]; exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hf⟩
  · rw [markedStableTotal_add_dirac p η hf]; linarith [Real.exp_pos p.1]

variable [Nonempty S]
lemma markedStable_project_law (ν : Measure S) [IsProbabilityMeasure ν] (b : ℝ) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (Measure.map Prod.fst) =
      poissonRandomMeasureLaw (stableLogIntensity b) := by
  rw [poissonRandomMeasureLaw_map _ measurable_fst]
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

lemma markedStable_regular (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν),
      markedStableTotalE η ≠ ⊤ ∧ 0 < markedStableTotal η := by
  have hpres : MeasurePreserving (Measure.map (Prod.fst : ℝ × S → ℝ))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ measurable_fst,markedStable_project_law ν b⟩
  have he := hpres.quasiMeasurePreserving.ae ((stablePoisson_total_finite hb hb1).and (stablePoissonTotal_pos hb hb1))
  simpa only [markedStableTotalE_projection,markedStableTotal_projection,stableJumpMomentE,one_mul] using he

lemma markedStable_laplace (ν : Measure S) [IsProbabilityMeasure ν] {b t : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫⁻ η, ENNReal.ofReal (Real.exp (-t*markedStableTotal η))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have he := stablePoissonTotal_laplace_lintegral hb hb1 ht
  rw [← markedStable_project_law ν b] at he
  rw [lintegral_map (by fun_prop) (Measure.measurable_map _ measurable_fst)] at he
  simpa only [markedStableTotal_projection] using he

def markedDistinctMoment : List (ℝ × (S → ℝ≥0∞)) → {m : ℕ} → Measure (ℝ × S) → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | rf::rs, _, η, z => ∫⁻ p, if ∃ i, z i = p.1 then 0 else
      ENNReal.ofReal (Real.exp (rf.1*p.1))*rf.2 p.2*
        markedDistinctMoment rs η (Fin.cons p.1 z) ∂markedStableCountKernel η

omit [Nonempty S] in
lemma markedDistinctMoment_measurable (rs : List (ℝ × (S → ℝ≥0∞)))
    (hr : ∀ rf ∈ rs, Measurable rf.2) (m : ℕ) :
    Measurable (fun p : Measure (ℝ × S) × (Fin m → ℝ) => markedDistinctMoment rs p.1 p.2) := by
  induction rs generalizing m with
  | nil => exact measurable_const
  | cons rf rs ih =>
    let κ : Kernel (Measure (ℝ × S) × (Fin m → ℝ)) (ℝ × S) := markedStableCountKernel.comap
      (Prod.fst : Measure (ℝ × S) × (Fin m → ℝ) → Measure (ℝ × S)) measurable_fst
    have hD : Measurable (fun p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) =>
        markedDistinctMoment rs p.1.1 (Fin.cons p.2.1 p.1.2)) := by
      exact (ih (fun r hr' => hr r (List.mem_cons_of_mem rf hr')) (m+1)).comp
        (measurable_fst.fst.prodMk (measurable_fin_cons measurable_snd.fst measurable_fst.snd))
    have hset : MeasurableSet {p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) |
        ∃ i, p.1.2 i = p.2.1} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd.fst
    exact (measurable_const.ite hset (((by fun_prop : Measurable (fun p :
      (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) => ENNReal.ofReal (Real.exp (rf.1*p.2.1)))).mul
      ((hr rf (by simp)).comp measurable_snd.snd)).mul hD)).lintegral_kernel_prod_right' (κ := κ)

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

end MarkedStable
end SphericalPerceptron
end
end
end

end OAI
