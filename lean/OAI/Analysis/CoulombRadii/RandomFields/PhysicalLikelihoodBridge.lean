import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationMatching
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalMatching

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

def flattenObservationNoise (n J : ℕ) :
    ObservationNoise n J ≃ᵐ ((Fin J × (Fin n × Fin 3)) → ℝ) where
  toEquiv := {
    toFun := fun u ia => u ia.1 ia.2.1 ia.2.2
    invFun := fun v j i a => v (j,i,a)
    left_inv := by intro u; rfl
    right_inv := by intro v; rfl }
  measurable_toFun := by change Measurable (fun (u : ObservationNoise n J) (ia : Fin J × (Fin n × Fin 3)) => u ia.1 ia.2.1 ia.2.2); fun_prop
  measurable_invFun := by change Measurable (fun (v : (Fin J × (Fin n × Fin 3)) → ℝ) (j : Fin J) (i : Fin n) (a : Fin 3) => v (j,i,a)); fun_prop

lemma flattenObservationNoise_preserving (n J : ℕ) :
    MeasurePreserving (flattenObservationNoise n J) (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : Fin J × (Fin n × Fin 3) => observationNoiseLaw)) := by
  refine ⟨(flattenObservationNoise n J).measurable,?_⟩
  refine (Measure.pi_eq (fun v hv => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have he : (flattenObservationNoise n J) ⁻¹' Set.univ.pi v=
      Set.univ.pi (fun j => Set.univ.pi (fun i => Set.univ.pi (fun a => v (j,i,a)))) := by
    ext u
    simp only [mem_preimage,Set.mem_pi,mem_univ,true_implies,flattenObservationNoise,
      MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
    exact ⟨fun h j i a => h (j,i,a),fun h ⟨j,i,a⟩ => h j i a⟩
  rw [he]
  simp only [allObservationNoiseLaw,Measure.pi_pi]
  simp only [Fintype.prod_prod_type]

def observationCoordinateData {n J : ℕ} (ℓ : Fin J → ℝ)
    (z : ObservationSample n J) : (Fin J × (Fin n × Fin 3)) → ℝ :=
  fun ia => z.1 ia.2.1 ia.2.2+ℓ ia.1*z.2 ia.1 ia.2.1 ia.2.2

lemma measurable_observationCoordinateData {n J : ℕ} (ℓ : Fin J → ℝ) :
    Measurable (@observationCoordinateData n J ℓ) := by
  unfold observationCoordinateData
  fun_prop

lemma observationCoordinateData_positions {n J : ℕ} (r : Fin J → ℝ)
    (sample : ObservationSample n J) (j : Fin J) :
    observationArrayPositions j (observationCoordinateData (fun k => (r k)^(101/100:ℝ)) sample)=
      observedOrdered r j sample := by
  funext i
  ext a
  simp [observationArrayPositions,observationCoordinateData,observedOrdered,
    observationNoiseVector_coordinate]

lemma arrayEventLikelihood_nested_integral {n J : ℕ} (ℓ : Fin J → ℝ)
    (hℓ : ∀ h, ℓ h≠0) (B : Set ((Fin J × (Fin n × Fin 3)) → ℝ))
    (x : Configuration n) :
    arrayEventLikelihood ℓ B x=
      ∫ u, B.indicator (fun _ => (1:ℝ)) (observationCoordinateData ℓ (x,u))
        ∂allObservationNoiseLaw n J := by
  rw [arrayEventLikelihood_integral ℓ hℓ]
  exact ((flattenObservationNoise_preserving n J).integral_comp'
    (fun u => B.indicator (fun _ => (1:ℝ)) (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia))).symm

lemma rawExpectation_eq_stateWeightedIntegral {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {F : Configuration n → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    rawExpectation ψ F=stateWeightedIntegral ψ F := by
  unfold rawExpectation configurationDensity stateWeightedIntegral
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun σ _ =>
    (hψ σ).norm.integrable_sq.bdd_mul hF.aestronglyMeasurable
      (Eventually.of_forall hC))

theorem physical_arrayEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, ℓ h≠0)
    {B : Set ((Fin J × (Fin n × Fin 3)) → ℝ)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, ((observationCoordinateData ℓ) ⁻¹' B).indicator
      (fun z => F z.1) sample ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*F x) := by
  let := rawLaw_isProbability hψ hn
  have hi : Integrable (fun z : ObservationSample n J => F z.1)
      (observationLaw J (rawLaw ψ)) :=
    (integrable_const C).mono' (hF.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hA := hB.preimage (measurable_observationCoordinateData ℓ)
  rw [observationLaw,integral_prod _ (hi.indicator hA)]
  have hi2 : (fun x : Configuration n => ∫ u,
      ((observationCoordinateData ℓ) ⁻¹' B).indicator (fun z => F z.1) (x,u)
        ∂allObservationNoiseLaw n J)=
      fun x => arrayEventLikelihood ℓ B x*F x := by
    funext x
    rw [arrayEventLikelihood_nested_integral ℓ hℓ B x,←integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases h : observationCoordinateData ℓ (x,u)∈B <;> simp [h]
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

def coordinateTailObservation {n J : ℕ} (j : ℕ)
    (z : (Fin J × (Fin n × Fin 3)) → ℝ) : Fin J → UnorderedArray n :=
  fun k => if j≤k.val then forgetOrder (observationArrayPositions k z) else forgetOrder 0

lemma measurable_coordinateTailObservation {n J : ℕ} (j : ℕ) :
    Measurable (@coordinateTailObservation n J j) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : j≤k.val
  · simpa only [coordinateTailObservation,ite_eq_left hk,Function.comp_def] using
      measurable_forgetOrder.comp (measurable_observationArrayPositions k)
  · simpa only [coordinateTailObservation,ite_eq_right hk] using
      (measurable_const : Measurable (fun _ : (Fin J × (Fin n × Fin 3)) → ℝ =>
        forgetOrder (0 : Configuration n)))

lemma coordinateTailObservation_permute {n J : ℕ} (j : ℕ)
    (p : Equiv.Perm (Fin n)) (z : (Fin J × (Fin n × Fin 3)) → ℝ) :
    coordinateTailObservation j (permuteObservationArray p z)=coordinateTailObservation j z := by
  funext k
  by_cases hk : j≤k.val
  · simp only [coordinateTailObservation,ite_eq_left hk]
    exact forgetOrder_permutation (observationArrayPositions k z) p
  · simp only [coordinateTailObservation,ite_eq_right hk]

lemma coordinateTailObservation_physical {n J : ℕ} (r : Fin J → ℝ)
    (j : ℕ) (sample : ObservationSample n J) :
    coordinateTailObservation j (observationCoordinateData (fun k => (r k)^(101/100:ℝ)) sample)=
      tailObservation r j sample := by
  funext k
  by_cases hk : j≤k.val
  · simp only [coordinateTailObservation,tailObservation,ite_eq_left hk,
      observationCoordinateData_positions,observedArray]
  · simp only [coordinateTailObservation,tailObservation,ite_eq_right hk]

lemma physical_tailEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, (tailObservation r j ⁻¹' B).indicator (fun z => F z.1) sample
      ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x =>
      arrayEventLikelihood (fun k => (r k)^(101/100:ℝ))
        (coordinateTailObservation j ⁻¹' B) x*F x) := by
  have he : observationCoordinateData (fun k => (r k)^(101/100:ℝ)) ⁻¹'
      (coordinateTailObservation j ⁻¹' B)=tailObservation r j ⁻¹' B := by
    ext sample
    simp only [mem_preimage,coordinateTailObservation_physical]
  rw [←he]
  exact physical_arrayEvent_bayes_integral hψ hn _
    (fun k => (Real.rpow_pos_of_pos (hr k) _).ne')
    (hB.preimage (measurable_coordinateTailObservation j)) hF hC

lemma physical_tailEvent_probability {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B) :
    (observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)=
    stateWeightedIntegral ψ (arrayEventLikelihood (fun k => (r k)^(101/100:ℝ))
      (coordinateTailObservation j ⁻¹' B)) := by
  have H := physical_tailEvent_bayes_integral hψ hn r hr j hB
    (measurable_const : Measurable (fun _ : Configuration n => (1:ℝ)))
    (C:=1) (fun _ => by simp)
  simpa only [integral_indicator_const _ (hB.preimage (measurable_tailObservation r j)),
    smul_eq_mul,mul_one] using H

theorem physical_tailEvent_state {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hbase : energy Z ψ g≤E+D₀)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (hp : 0<(observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)) :
    ∃ u : Coulomb.H1Vector n, Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u≤E+(D₀+observationEventEnergyConstant*
        observationWidthSquareSum (fun k => (r k)^(101/100:ℝ))*
        (1-Real.log ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)))^5) ∧
      ∀ F : Configuration n → ℝ, Measurable F → (∃ C : ℝ, ∀ x, ‖F x‖≤C) →
      Coulomb.potentialForm (fun x => F ((flattenConfiguration n).symm x)) u=
        ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
          ∫ sample, (tailObservation r j ⁻¹' B).indicator (fun z => F z.1) sample
            ∂observationLaw J (rawLaw ψ) := by
  have hpEq := physical_tailEvent_probability hd.2.2.1 hn r hr j hB
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k => (r k)^(101/100:ℝ)) (fun k => Real.rpow_pos_of_pos (hr k) _)
    (hB.preimage (measurable_coordinateTailObservation j))
    (fun p z => by simp only [mem_preimage,coordinateTailObservation_permute])
    (hpEq ▸ hp)
  refine ⟨u,hu,hum,?_,?_⟩
  · simpa only [hpEq] using hue
  · intro F hF hbound
    obtain ⟨C,hC⟩ := hbound
    rw [hlaw,physical_tailEvent_bayes_integral hd.2.2.1 hn r hr j hB hF hC,hpEq]
    simp only [ContinuousLinearEquiv.symm_apply_apply]

end NeutralAtom

end

end OAI
