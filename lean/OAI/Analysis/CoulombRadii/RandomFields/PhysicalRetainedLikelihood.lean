import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalLikelihoodBridge

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

def flattenIndexedNoise (n : ℕ) (H : Type*) [Fintype H] :
    (H → Fin n → Fin 3 → ℝ) ≃ᵐ ((H × (Fin n × Fin 3)) → ℝ) where
  toEquiv := {
    toFun := fun u ia => u ia.1 ia.2.1 ia.2.2
    invFun := fun v h i a => v (h,i,a)
    left_inv := by intro u; rfl
    right_inv := by intro v; rfl }
  measurable_toFun := by change Measurable (fun (u : H → Fin n → Fin 3 → ℝ) (ia : H × (Fin n × Fin 3)) => u ia.1 ia.2.1 ia.2.2); fun_prop
  measurable_invFun := by change Measurable (fun (v : (H × (Fin n × Fin 3)) → ℝ) (h : H) (i : Fin n) (a : Fin 3) => v (h,i,a)); fun_prop

lemma flattenIndexedNoise_preserving (n : ℕ) (H : Type*) [Fintype H] :
    MeasurePreserving (flattenIndexedNoise n H)
      (Measure.pi (fun _ : H => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw))))
      (Measure.pi (fun _ : H × (Fin n × Fin 3) => observationNoiseLaw)) := by
  refine ⟨(flattenIndexedNoise n H).measurable,?_⟩
  refine (Measure.pi_eq (fun v hv => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have he : (flattenIndexedNoise n H) ⁻¹' Set.univ.pi v=
      Set.univ.pi (fun j => Set.univ.pi (fun i => Set.univ.pi (fun a => v (j,i,a)))) := by
    ext u
    simp only [mem_preimage,Set.mem_pi,mem_univ,true_implies,flattenIndexedNoise,
      MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
    exact ⟨fun h j i a => h (j,i,a),fun h ⟨j,i,a⟩ => h j i a⟩
  rw [he]
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

abbrev RetainedScales (J j : ℕ) := {k : Fin J // j≤k.val}

def retainedNoise {n J : ℕ} (j : ℕ) (u : ObservationNoise n J) :
    (RetainedScales J j × (Fin n × Fin 3)) → ℝ :=
  fun ia => u ia.1.val ia.2.1 ia.2.2

lemma retainedNoise_preserving (n J j : ℕ) :
    MeasurePreserving (@retainedNoise n J j) (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : RetainedScales J j × (Fin n × Fin 3) => observationNoiseLaw)) := by
  have hp : MeasurePreserving
      (fun u : ObservationNoise n J => fun k : RetainedScales J j => u k.val)
      (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : RetainedScales J j =>
        Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))) :=
    measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin J => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))
      (fun k : Fin J => j≤k.val))
  exact (flattenIndexedNoise_preserving n (RetainedScales J j)).comp hp

def retainedObservationData {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ)
    (z : ObservationSample n J) : (RetainedScales J j × (Fin n × Fin 3)) → ℝ :=
  fun ia => z.1 ia.2.1 ia.2.2+ℓ ia.1*z.2 ia.1.val ia.2.1 ia.2.2

lemma measurable_retainedObservationData {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ) :
    Measurable (@retainedObservationData n J j ℓ) := by
  unfold retainedObservationData
  fun_prop

lemma arrayEventLikelihood_retained_integral {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ)
    (hℓ : ∀ h, ℓ h≠0) (B : Set ((RetainedScales J j × (Fin n × Fin 3)) → ℝ))
    (hB : MeasurableSet B) (x : Configuration n) :
    arrayEventLikelihood ℓ B x=
      ∫ u, B.indicator (fun _ => (1:ℝ)) (retainedObservationData j ℓ (x,u))
        ∂allObservationNoiseLaw n J := by
  have hm : Measurable (fun u : (RetainedScales J j × (Fin n × Fin 3)) → ℝ =>
      B.indicator (fun _ => (1:ℝ)) (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)) :=
    (measurable_const.indicator hB).comp (by fun_prop)
  rw [arrayEventLikelihood_integral ℓ hℓ,←(retainedNoise_preserving n J j).map_eq]
  exact integral_map_of_stronglyMeasurable (retainedNoise_preserving n J j).measurable hm.stronglyMeasurable

theorem physical_retainedEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (j : ℕ) (ℓ : RetainedScales J j → ℝ) (hℓ : ∀ k, ℓ k≠0)
    {B : Set ((RetainedScales J j × (Fin n × Fin 3)) → ℝ)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, (retainedObservationData j ℓ ⁻¹' B).indicator (fun z => F z.1) sample
      ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*F x) := by
  let := rawLaw_isProbability hψ hn
  have hi : Integrable (fun z : ObservationSample n J => F z.1)
      (observationLaw J (rawLaw ψ)) :=
    (integrable_const C).mono' (hF.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hA := hB.preimage (measurable_retainedObservationData j ℓ)
  rw [observationLaw,integral_prod _ (hi.indicator hA)]
  have hi2 : (fun x : Configuration n => ∫ u,
      (retainedObservationData j ℓ ⁻¹' B).indicator (fun z => F z.1) (x,u)
        ∂allObservationNoiseLaw n J)=
      fun x => arrayEventLikelihood ℓ B x*F x := by
    funext x
    rw [arrayEventLikelihood_retained_integral j ℓ hℓ B hB x,←integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases h : retainedObservationData j ℓ (x,u)∈B <;> simp [h]
  rw [hi2,integral_rawLaw hψ]
  apply rawExpectation_eq_stateWeightedIntegral (C:=C) hψ
    (((arrayEventLikelihood_contDiff ℓ hB).continuous.measurable).mul hF)
  intro x
  change ‖arrayEventLikelihood ℓ B x*F x‖≤C
  rw [norm_mul,Real.norm_of_nonneg (arrayEventLikelihood_nonneg ℓ hB x)]
  exact (mul_le_mul_of_nonneg_right (arrayEventLikelihood_le_one ℓ hB x)
    (norm_nonneg _)).trans (by simpa using hC x)
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

def retainedTailObservation {n J : ℕ} (j : ℕ)
    (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) : Fin J → UnorderedArray n :=
  fun k => if hk : j≤k.val then forgetOrder (observationArrayPositions ⟨k,hk⟩ z) else forgetOrder 0

lemma measurable_retainedTailObservation {n J : ℕ} (j : ℕ) :
    Measurable (@retainedTailObservation n J j) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : j≤k.val
  · simpa only [retainedTailObservation,dite_eq_left hk,Function.comp_def] using
      measurable_forgetOrder.comp (measurable_observationArrayPositions (⟨k,hk⟩ : RetainedScales J j))
  · simpa only [retainedTailObservation,dite_eq_right hk] using
      (measurable_const : Measurable (fun _ : (RetainedScales J j × (Fin n × Fin 3)) → ℝ =>
        forgetOrder (0 : Configuration n)))

lemma retainedTailObservation_permute {n J : ℕ} (j : ℕ)
    (p : Equiv.Perm (Fin n)) (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
    retainedTailObservation j (permuteObservationArray p z)=retainedTailObservation j z := by
  funext k
  by_cases hk : j≤k.val
  · simp only [retainedTailObservation,dite_eq_left hk]
    exact forgetOrder_permutation (observationArrayPositions ⟨k,hk⟩ z) p
  · simp only [retainedTailObservation,dite_eq_right hk]

lemma retainedTailObservation_physical {n J : ℕ} (r : Fin J → ℝ)
    (j : ℕ) (sample : ObservationSample n J) :
    retainedTailObservation j (retainedObservationData j (fun k => (r k.val)^(101/100:ℝ)) sample)=
      tailObservation r j sample := by
  funext k
  by_cases hk : j≤k.val
  · simp only [retainedTailObservation,tailObservation,dite_eq_left hk,ite_eq_left hk,observedArray]
    congr 1
    funext i
    ext a
    simp [observationArrayPositions,retainedObservationData,observedOrdered,
      observationNoiseVector_coordinate]
  · simp only [retainedTailObservation,tailObservation,dite_eq_right hk,ite_eq_right hk]

lemma physical_retainedTailEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, (tailObservation r j ⁻¹' B).indicator (fun z => F z.1) sample
      ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x =>
      arrayEventLikelihood (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
        (retainedTailObservation j ⁻¹' B) x*F x) := by
  have he : retainedObservationData j (fun k => (r k.val)^(101/100:ℝ)) ⁻¹'
      (retainedTailObservation j ⁻¹' B)=tailObservation r j ⁻¹' B := by
    ext sample
    simp only [mem_preimage,retainedTailObservation_physical]
  rw [←he]
  exact physical_retainedEvent_bayes_integral hψ hn j _
    (fun k => (Real.rpow_pos_of_pos (hr k.val) _).ne')
    (hB.preimage (measurable_retainedTailObservation j)) hF hC

lemma physical_retainedTailEvent_probability {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B) :
    (observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)=
    stateWeightedIntegral ψ (arrayEventLikelihood (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
      (retainedTailObservation j ⁻¹' B)) := by
  have H := physical_retainedTailEvent_bayes_integral hψ hn r hr j hB
    (measurable_const : Measurable (fun _ : Configuration n => (1:ℝ)))
    (C:=1) (fun _ => by simp)
  simpa only [integral_indicator_const _ (hB.preimage (measurable_tailObservation r j)),
    smul_eq_mul,mul_one] using H

theorem physical_retainedTailEvent_state {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hbase : energy Z ψ g≤E+D₀)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (hp : 0<(observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)) :
    ∃ u : Coulomb.H1Vector n, Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u≤E+(D₀+observationEventEnergyConstant*
        observationWidthSquareSum (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))*
        (1-Real.log ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)))^5) ∧
      ∀ F : Configuration n → ℝ, Measurable F → (∃ C : ℝ, ∀ x, ‖F x‖≤C) →
      Coulomb.potentialForm (fun x => F ((flattenConfiguration n).symm x)) u=
        ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
          ∫ sample, (tailObservation r j ⁻¹' B).indicator (fun z => F z.1) sample
            ∂observationLaw J (rawLaw ψ) := by
  have hpEq := physical_retainedTailEvent_probability hd.2.2.1 hn r hr j hB
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (fun k => Real.rpow_pos_of_pos (hr k.val) _)
    (hB.preimage (measurable_retainedTailObservation j))
    (fun p z => by simp only [mem_preimage,retainedTailObservation_permute])
    (hpEq ▸ hp)
  refine ⟨u,hu,hum,?_,?_⟩
  · simpa only [hpEq] using hue
  · intro F hF hbound
    obtain ⟨C,hC⟩ := hbound
    rw [hlaw,physical_retainedTailEvent_bayes_integral hd.2.2.1 hn r hr j hB hF hC,hpEq]
    simp only [ContinuousLinearEquiv.symm_apply_apply]

end NeutralAtom

end

end OAI
