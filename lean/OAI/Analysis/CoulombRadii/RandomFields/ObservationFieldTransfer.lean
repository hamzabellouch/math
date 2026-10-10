import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationPatchScale
import OAI.Analysis.CoulombRadii.FieldAnalysis.FreshTransferScale

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem atomic_observation_fresh_field_transfer {D A : ℝ} (hD : 0≤D) (hA : 0<A) :
    ∃ s : ℝ, 0<s ∧ ∀ {n : ℕ} (Z : ℕ) (hZ : 1≤Z)
    {ψ : Wavefunction n} {g : Gradient n}, FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → ∀ {r : ℝ}, 0<r → r<s →
    ∀ {B : Set ((Fin 1 × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
    (∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈B ↔ y∈B) →
    r^42≤ stateWeightedIntegral ψ (arrayEventLikelihood (fun _ : Fin 1 => r^(101/100:ℝ)) B) →
    ∀ (y : Position) (hy : y≠0), Coulomb.atomicCellScale y≤A*r →
    ∃ u : Coulomb.H1Vector n, Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u≤E+inverseObservationOffset D r ∧
      (∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
        (stateWeightedIntegral ψ (arrayEventLikelihood (fun _ : Fin 1 => r^(101/100:ℝ)) B))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood (fun _ : Fin 1 => r^(101/100:ℝ)) B x*
          F (flattenConfiguration n x))) ∧
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
    ∃ T : Coulomb.AtomicBudgetHistory (Coulomb.atom Z hZ) u
        (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm (Coulomb.atom Z hZ)≤Coulomb.form (Coulomb.atom Z hZ) u+
        Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
      Coulomb.atomicPatchTFGap (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
        ((Coulomb.atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤
        2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
        (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*(Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
      |Coulomb.coreScreenedField (Coulomb.atom Z hZ) u y-
        Coulomb.atomicPatchMeanField (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
          ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        Coulomb.atomicTransferConstant*(Coulomb.atomicCellScale y)^(-1999/500:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,hscale⟩ := exists_inverseObservationOffset_small hD hA
  obtain ⟨s₁,hs₁,_,hpatch⟩ := Coulomb.exists_atomic_fresh_field_transfer
  refine ⟨min s₀ (s₁/A),lt_min hs₀ (div_pos hs₁ hA),?_⟩
  intro n Z hZ ψ g hd hn hmin E hE hbase r hr hrs B hB hsym hprob y hy hya
  have hrs₀ : r<s₀ := hrs.trans_le (min_le_left _ _)
  have hr1 : r≤1 := hrs₀.le.trans hs₀1
  have hp : 0<stateWeightedIntegral ψ (arrayEventLikelihood (fun _ : Fin 1 => r^(101/100:ℝ)) B) :=
    (pow_pos hr 42).trans_le hprob
  have hp1 := stateWeightedIntegral_le_one hd hn
    (arrayEventLikelihood_contDiff (fun _ : Fin 1 => r^(101/100:ℝ)) hB).continuous.measurable
    (arrayEventLikelihood_nonneg _ hB) (arrayEventLikelihood_le_one _ hB)
  have hm := observationEventOffset_mono_probability (fun _ : Fin 1 => r^(101/100:ℝ)) D
    (pow_pos hr 42) hprob hp1
  have hm' : D+observationEventEnergyConstant*
      observationWidthSquareSum (fun _ : Fin 1 => r^(101/100:ℝ))*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood (fun _ : Fin 1 => r^(101/100:ℝ)) B)))^5≤
      inverseObservationOffset D r := by
    simpa [inverseObservationOffset,observationWidthSquareSum] using hm
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun _ : Fin 1 => r^(101/100:ℝ)) (fun _ => Real.rpow_pos_of_pos hr _) hB hsym hp
  have hue' := hue.trans (add_le_add le_rfl hm')
  refine ⟨u,hu,hum,hue',hlaw,?_⟩
  apply hpatch (Coulomb.atom Z hZ) (by intro i; rfl) u hu hum hE hue'
    (inverseObservationOffset_nonneg hD hr hr1) y hy
  · have hh : r<s₁/A := hrs.trans_le (min_le_right _ _)
    exact hya.trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hA).mp hh)
  · exact hscale hr hrs₀ (Coulomb.atomicCellScale_pos hy) hya
end NeutralAtom
end

end
end

end OAI
