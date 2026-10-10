import OAI.Probability.ProjectionMoments.Streaming

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner

section
open Learner
variable {d M T : ℕ}

lemma Realizer.uniform_event_law [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (S : Set (UnitSphere d × Result d M)) (hS : MeasurableSet S) :
    ((uniformSphere d).prod (K.tapeLaw.prod (sampleLaw d T)))
      {z | (z.1,(R.toLearner.terminal z.1 z.2.1 z.2.2,R.toLearner.estimate z.1 z.2.1 z.2.2)) ∈ S} =
    ∫⁻ z : UnitSphere d × Samples d T,
      K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
        {r | (z.1,r) ∈ S} ∂((uniformSphere d).prod (sampleLaw d T)) := by
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := K.tapeLaw))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) K.tapeLaw)
  have hE : MeasurableSet {z : UnitSphere d × (Tape M T × Samples d T) |
      (z.1,(R.toLearner.terminal z.1 z.2.1 z.2.2,R.toLearner.estimate z.1 z.2.1 z.2.2)) ∈ S} :=
    (measurable_fst.prodMk ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules))) hS
  rw [← hp.measure_preimage hE.nullMeasurableSet,Measure.prod_apply (hp.measurable hE)]
  apply lintegral_congr
  intro z
  have hs : MeasurableSet {r : Result d M | (z.1,r) ∈ S} :=
    (measurable_const.prodMk measurable_id) hS
  rw [←R.conditional_joint_law z.1 z.2,Measure.map_apply _ hs]
  · rfl
  · exact ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules)).comp
        (show Measurable (fun ω : Tape M T => (z.1,(ω,z.2))) from by fun_prop)

lemma Realizer.uniformSuccess_eq [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer) (ε : ℝ) :
    R.toLearner.uniformSuccess K.tapeLaw ε = K.uniformSuccess ε := by
  exact R.uniform_event_law {z | angularError z.1 z.2.2 ≤ ε}
    (measurableSet_le (show Measurable (fun z : UnitSphere d × Result d M => angularError z.1 z.2.2) from by unfold angularError; fun_prop) measurable_const)

lemma Realizer.uniformFixedSuccess_eq [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer) (ε : ℝ) (t : ℕ) :
    R.toLearner.uniformFixedSuccess K.tapeLaw ε t = K.uniformFixedSuccess ε t := by
  exact R.uniform_event_law {z | z.2.1.1 = t ∧ angularError z.1 z.2.2 ≤ ε}
    ((measurableSet_eq_fun (show Measurable (fun z : UnitSphere d × Result d M => z.2.1.1) from by fun_prop) measurable_const).inter
      (measurableSet_le (show Measurable (fun z : UnitSphere d × Result d M => angularError z.1 z.2.2) from by unfold angularError; fun_prop) measurable_const))

lemma jointExperimentLaw_congr {K K' : FiniteKernelLearner d M T}
    (hi : K.initial = K'.initial) (ho : K.output = K'.output)
    (obs : Fin T → (Vector d × ℝ))
    (ht : ∀ t j i, K.transition t j (obs i) = K'.transition t j (obs i)) :
    K.jointExperimentLaw obs = K'.jointExperimentLaw obs := by
  have htag : ∀ t j i, K.taggedKernel t j (obs i) = K'.taggedKernel t j (obs i) := by
    intro t j i
    cases j with
    | inr a => rfl
    | inl j => simp only [taggedKernel,ht]
  have hout : K.terminalJointOutput = K'.terminalJointOutput := by
    funext j
    unfold terminalJointOutput
    congr 1
    cases j with
    | inl j => exact congrFun (congrFun ho T) j
    | inr a => exact congrFun (congrFun ho a.1) a.2
  unfold jointExperimentLaw
  rw [hi,hout]
  congr 1
  funext a
  rw [kernelRun_congr T (taggedStart a) obs htag]

lemma exists_borel_same_joint (K : FiniteKernelLearner d M T) (hK : K.CompletedRules) (hd : 3 ≤ d) :
    ∃ K' : FiniteKernelLearner d M T, K'.BorelRules ∧
      ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
        K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫)) =
        K'.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫)) := by
  obtain ⟨K',hK',hi,ho,ht⟩ := K.exists_borel_version hK
  refine ⟨K',hK',?_⟩
  let : NeZero d := ⟨by omega⟩
  have hg : ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)), ∀ t j (i : Fin T),
      K.transition t j (z.2 i,⟪z.1.val,z.2 i⟫) = K'.transition t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (E := Vector d) (by simpa using hd) i).ae (ht t j).symm
  filter_upwards [hg] with z hz
  exact jointExperimentLaw_congr hi.symm ho.symm _ hz

theorem exists_equivalent_tape (K : FiniteKernelLearner d M T) (hK : K.CompletedRules) (hd : 3 ≤ d) :
    ∃ (ρ : Measure (Tape M T)) (L : Learner d M T (Tape M T)),
      IsProbabilityMeasure ρ ∧ L.MeasurableRules ∧ L.Admissible ρ ∧
      (∀ ε, L.uniformSuccess ρ ε = K.uniformSuccess ε) ∧
      (∀ ε t, L.uniformFixedSuccess ρ ε t = K.uniformFixedSuccess ε t) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨K',hK',he⟩ := K.exists_borel_same_joint hK hd
  let R := Classical.choice (K'.exists_realizer hK')
  refine ⟨K'.tapeLaw,R.toLearner,inferInstance,R.measurableRules,
    R.toLearner.admissible_of_measurable R.measurableRules K'.tapeLaw,?_,?_⟩
  · intro ε
    rw [R.uniformSuccess_eq]
    apply lintegral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  · intro ε t
    rw [R.uniformFixedSuccess_eq]
    apply lintegral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]

end

universe u
variable {d M T : ℕ}

lemma seed_average_bound {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {f : Ξ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ᵐ ξ ∂ρ, f ξ ≤ C) : ∫⁻ ξ, f ξ ∂ρ ≤ C := by
  calc
    _ ≤ ∫⁻ _, C ∂ρ := lintegral_mono_ae h
    _ = C := by simp

lemma exists_successful_seed {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {P : Ξ → Prop} (hP : ∀ᵐ ξ ∂ρ, P ξ)
    {f : Ξ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (hs : c ≤ ∫⁻ ξ, f ξ ∂ρ) :
    ∃ ξ, P ξ ∧ c ≤ f ξ := by
  by_contra h
  have hlt : ∀ᵐ ξ ∂ρ, f ξ < c := by
    filter_upwards [hP] with ξ hξ
    exact lt_of_not_ge (fun hf => h ⟨ξ,hξ,hf⟩)
  have hbound : ∫⁻ ξ, f ξ ∂ρ ≤ c := seed_average_bound ρ (ae_le_of_ae_lt hlt)
  have hstrict := lintegral_strict_mono (show ρ ≠ 0 from by
    intro he; have hh := measure_univ (μ := ρ); rw [he] at hh; simp at hh)
    (aemeasurable_const (b := c)) (ne_top_of_le_ne_top hc hbound) hlt
  have hh : ∫⁻ ξ, f ξ ∂ρ < c := by simpa using hstrict
  exact not_lt_of_ge hs hh

theorem riesz_success :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q)) := by
  obtain ⟨C,hC,h⟩ := Learner.riesz_success.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK q W
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL

theorem haar_success :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.haar_success.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK k Nstar
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL

theorem cap_fixed_stop :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.cap_fixed_stop.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK t ht k α
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,_,he⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε t]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL
    (L.measurable_terminal hB).fst.aemeasurable t ht

theorem fixed_quadratic_memory : FixedQuadraticMemory.{u} := by
  intro A hA
  obtain ⟨c,hc,d₀,h⟩ := NoiselessRegression.fixed_quadratic_memory.{0} A hA
  refine ⟨c,hc,max d₀ 3,?_⟩
  intro d hd M T hM ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  obtain ⟨ξ,hξ,hsξ⟩ := exists_successful_seed ρ hK (ENNReal.div_ne_top (by norm_num) (by norm_num) : (2/3 : ℝ≥0∞) ≠ ∞) hs
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  apply h d (by omega) M T hM ε hε hε10 (Tape M T) ν hν L hL
  rwa [he ε]

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d:ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
    ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε →
    c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)

theorem subquadratic_memory : SubquadraticMemory.{u} := by
  obtain ⟨c,hc,h⟩ := NoiselessRegression.subquadratic_memory.{0}
  refine ⟨c,hc,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := h M hM
  refine ⟨max d₀ 3,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  obtain ⟨ξ,hξ,hsξ⟩ := exists_successful_seed ρ hK (ENNReal.div_ne_top (by norm_num) (by norm_num) : (2/3 : ℝ≥0∞) ≠ ∞) hs
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  apply hd₀ d (by omega) T ε hε hε10 (Tape (M d) T) ν hν L hL
  exact Or.inl ((he ε).symm ▸ hsξ)

end FiniteKernelLearner

lemma fresh_seed_kernel_version {X Ξ J : Type*} [MeasurableSpace X]
    [MeasurableSpace Ξ] [Fintype J] [Nonempty J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (μ : Measure X) [SFinite μ]
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (P : X × Ξ → Measure J) (hP : ∀ z, IsProbabilityMeasure (P z))
    (hm : ∀ j, AEMeasurable (fun z => P z {j}) (μ.prod ρ)) :
    ∃ κ : Kernel X J, IsMarkovKernel κ ∧
      ∀ᵐ x ∂μ, ∀ j, κ x {j} = ∫⁻ ξ, P (x,ξ) {j} ∂ρ := by
  obtain ⟨κ,hκ,he⟩ := finite_kernel_borel_version (μ.prod ρ) P hP hm
  let : IsMarkovKernel κ := hκ
  let η : Kernel X J := κ ∘ₖ ((Kernel.id : Kernel X X) ×ₖ Kernel.const X ρ)
  refine ⟨η,inferInstance,?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod he] with x hx
  intro j
  rw [show η x {j} = ∫⁻ ξ, κ (x,ξ) {j} ∂ρ from ?_]
  · apply lintegral_congr_ae
    filter_upwards [hx] with ξ hξ
    rw [hξ]
  · change (κ ∘ₖ ((Kernel.id : Kernel X X) ×ₖ Kernel.const X ρ)) x {j} = _
    rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton j),Kernel.prod_apply,
      Kernel.id_apply,Kernel.const_apply]
    rw [lintegral_prod _ (κ.measurable_coe (measurableSet_singleton j)).aemeasurable]
    apply lintegral_dirac'
    exact (κ.measurable_coe (measurableSet_singleton j)).lintegral_prod_right

end NoiselessRegression

end

end OAI
