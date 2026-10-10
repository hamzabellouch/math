import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationSmallScale
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalLikelihoodBridge

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem atomic_observed_small_annular_count_tail {α A B β : ℝ}
    (hα : 0<α) (hαA : α<A) (hAB : A<B) (hBβ : B<β) :
    ∃ K : ℝ, 0<K ∧ ∀ D₀ : ℝ, 0 ≤ D₀ → ∃ s : ℝ, 0<s ∧
    ∀ {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D₀ → ∀ {r : ℝ}, 0<r → r<s →
    stateWeightedIntegral ψ (arrayEventLikelihood (fun _ : Fin 1 => r^(101/100:ℝ))
      {y | K/r^3<rawCount {z : Position | A*r ≤ ‖z‖ ∧ ‖z‖ ≤ B*r} (observationArrayPositions 0 y)}) ≤ r^40 := by
  obtain ⟨C,hC,hbound⟩ := atomic_observed_annular_count_tail hα (by linarith : α<β)
  let K := 2*Real.sqrt C+1
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro D₀ hD
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0, r<1 ∧ singleObservationOffset D₀ r*r^7 ≤ 1 ∧
      Real.sqrt 3*r^(101/100:ℝ)/r<A-α ∧ Real.sqrt 3*r^(101/100:ℝ)/r<β-B := by
    have hm := (singleObservationOffset_scaled_tendsto D₀).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
    have ha := observation_displacement_ratio_tendsto.eventually (gt_mem_nhds (by linarith : 0<A-α))
    have hb := observation_displacement_ratio_tendsto.eventually (gt_mem_nhds (by linarith : 0<β-B))
    have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r<1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hr,hm,ha,hb] with r hr hm ha hb
    exact ⟨hr,hm.le,ha,hb⟩
  obtain ⟨s,hs,hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hevent
  refine ⟨s,hs,?_⟩
  intro n Z hZ ψ g hd hn hmin E hE hbase r hr hrs
  obtain ⟨hr1,hm,ha,hb⟩ := hsub ⟨hr,hrs⟩
  have hδ : 0 ≤ singleObservationOffset D₀ r := by
    unfold singleObservationOffset
    have hl : Real.log (r^40) ≤ 0 := Real.log_nonpos (by positivity) (pow_le_one₀ hr.le hr1.le)
    exact add_nonneg hD (mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
      (sq_nonneg _)) (pow_nonneg (by linarith) _))
  have hmass := screenMass_small_offset hr hr1.le hδ hm
  have hcoeff : 4*C<K^2 := by
    dsimp [K]
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C]
  have hth : C*(Coulomb.screenMass (singleObservationOffset D₀ r) r)^2<(K/r^3)^2 := by
    calc
      _ ≤ C*(2/r^3)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Coulomb.screenMass_pos _ _).le hmass 2) hC
      _ < (K/r^3)^2 := by
        rw [div_pow,div_pow,←mul_div_assoc]
        exact (div_lt_div_iff_of_pos_right (pow_pos (pow_pos hr _) _)).mpr (by nlinarith)
  have ha' : α*r+Real.sqrt 3*r^(101/100:ℝ)<A*r := by
    have := (div_lt_iff₀ hr).mp ha
    nlinarith
  have hb' : B*r+Real.sqrt 3*r^(101/100:ℝ)<β*r := by
    have := (div_lt_iff₀ hr).mp hb
    nlinarith
  have hsum : observationWidthSquareSum (fun _ : Fin 1 => r^(101/100:ℝ))=((r^(101/100:ℝ))⁻¹)^2 := by
    simp [observationWidthSquareSum]
  have ht' : C*(Coulomb.screenMass (D₀+observationEventEnergyConstant*
      observationWidthSquareSum (fun _ : Fin 1 => r^(101/100:ℝ))*(1-Real.log (r^40))^5) r)^2<(K/r^3)^2 := by
    simpa only [hsum,singleObservationOffset] using hth
  exact hbound Z hZ hd hn hmin hE hbase hD _
    (fun _ => Real.rpow_pos_of_pos hr _) (0:Fin 1) hr (by positivity) (by positivity) ha' hb' ht'
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

def observationSingleScale {n J : ℕ} (k : Fin J)
    (sample : ObservationSample n J) : ObservationSample n 1 :=
  (sample.1, fun _ => sample.2 k)

lemma observationSingleScale_preserving {n J : ℕ}
    (ν : Measure (Configuration n)) [SFinite ν] (k : Fin J) :
    MeasurePreserving (observationSingleScale k) (observationLaw J ν) (observationLaw 1 ν) := by
  have hn : MeasurePreserving (fun u : ObservationNoise n J => fun _ : Fin 1 => u k)
      (allObservationNoiseLaw n J) (allObservationNoiseLaw n 1) :=
    (measurePreserving_funUnique
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))
      (Fin 1)).symm.comp (measurePreserving_eval _ k)
  exact (MeasurePreserving.id ν).prod hn

lemma physical_arrayEvent_probability {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (ℓ : Fin J → ℝ) (hℓ : ∀ k, ℓ k≠0)
    {B : Set ((Fin J × (Fin n × Fin 3)) → ℝ)} (hB : MeasurableSet B) :
    (observationLaw J (rawLaw ψ)).real (observationCoordinateData ℓ ⁻¹' B)=
      stateWeightedIntegral ψ (arrayEventLikelihood ℓ B) := by
  have H := physical_arrayEvent_bayes_integral hψ hn ℓ hℓ hB
    (measurable_const : Measurable (fun _ : Configuration n => (1:ℝ)))
    (C:=1) (fun _ => by simp)
  simpa only [integral_indicator_const _ (hB.preimage (measurable_observationCoordinateData ℓ)),
    smul_eq_mul,mul_one] using H

theorem physical_observed_small_annular_count_tail {α A B β : ℝ}
    (hα : 0<α) (hαA : α<A) (hAB : A<B) (hBβ : B<β) :
    ∃ K : ℝ, 0<K ∧ ∀ D₀ : ℝ, 0≤D₀ → ∃ s : ℝ, 0<s ∧
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D₀ → ∀ (r : Fin J → ℝ) (k : Fin J), 0<r k → r k<s →
    (observationLaw J (rawLaw ψ)).real
      {sample | K/(r k)^3<rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
        (observedOrdered r k sample)}≤(r k)^40 := by
  obtain ⟨K,hK,H⟩ := atomic_observed_small_annular_count_tail hα hαA hAB hBβ
  refine ⟨K,hK,?_⟩
  intro D₀ hD
  obtain ⟨s,hs,Hs⟩ := H D₀ hD
  refine ⟨s,hs,?_⟩
  intro n J Z hZ ψ g hd hn hmin E hE hbase r k hr hrs
  have := rawLaw_isProbability hd.2.2.1 hn
  let S : Set ((Fin 1 × (Fin n × Fin 3)) → ℝ) :=
    {y | K/(r k)^3<rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
      (observationArrayPositions 0 y)}
  have hS : MeasurableSet S := observed_annular_event_measurable _ _ _ _
  have hp := physical_arrayEvent_probability hd.2.2.1 hn
    (fun _ : Fin 1 => (r k)^(101/100:ℝ)) (fun _ => (Real.rpow_pos_of_pos hr _).ne') hS
  have hpre : observationSingleScale k ⁻¹'
      (observationCoordinateData (fun _ : Fin 1 => (r k)^(101/100:ℝ)) ⁻¹' S)=
      {sample | K/(r k)^3<rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
        (observedOrdered r k sample)} := by
    ext sample
    have he : observationArrayPositions (0:Fin 1)
        (observationCoordinateData (fun _ : Fin 1 => (r k)^(101/100:ℝ))
          (observationSingleScale k sample))=observedOrdered r k sample := by
      funext i
      ext a
      simp [observationArrayPositions,observationCoordinateData,observationSingleScale,
        observedOrdered,observationNoiseVector_coordinate]
    simp only [mem_preimage,S,mem_ofPred_eq,he]
  rw [←hpre]
  have he := (observationSingleScale_preserving (rawLaw ψ) k).measure_preimage
    (hS.preimage (measurable_observationCoordinateData
      (fun _ : Fin 1 => (r k)^(101/100:ℝ)))).nullMeasurableSet
  unfold Measure.real
  rw [he]
  change (observationLaw 1 (rawLaw ψ)).real _≤_
  rw [hp]
  exact Hs Z hZ hd hn hmin hE hbase hr hrs
end NeutralAtom
end

end
end

end OAI
