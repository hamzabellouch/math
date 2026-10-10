import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationMatching
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicNear

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

def inverseObservationOffset (D r : ℝ) : ℝ :=
  D+observationEventEnergyConstant*((r^(101/100:ℝ))⁻¹)^2*(1-Real.log (r^42))^5

lemma inverseObservationOffset_scaled_tendsto (D : ℝ) :
    Tendsto (fun r => inverseObservationOffset D r*r^(349/50:ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<124/125)).sub
    ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ)<124/125)).const_mul 42)
  have hh := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<349/50)).const_mul D).add
    ((ht.pow 5).const_mul observationEventEnergyConstant)
  simp only [mul_zero,sub_self,zero_pow (by decide : 5≠0),add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0<r := hr
  have hpn : r^(101/100:ℝ)≠0 := (Real.rpow_pos_of_pos hr _).ne'
  have hmul : (r^(124/125:ℝ))^5*(r^(101/100:ℝ))^2=r^(349/50:ℝ) := by
    rw [←Real.rpow_natCast (r^(124/125:ℝ)) 5,←Real.rpow_mul hr.le,
      ←Real.rpow_natCast (r^(101/100:ℝ)) 2,←Real.rpow_mul hr.le,←Real.rpow_add hr]
    norm_num
  have hratio : ((r^(101/100:ℝ))⁻¹)^2*r^(349/50:ℝ)=(r^(124/125:ℝ))^5 := by
    rw [←hmul]
    field_simp
  dsimp [inverseObservationOffset]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    D*r^(349/50:ℝ)+observationEventEnergyConstant*(r^(124/125:ℝ)-42*(Real.log r*r^(124/125:ℝ)))^5 =
      D*r^(349/50:ℝ)+observationEventEnergyConstant*(r^(124/125:ℝ))^5*(1-42*Real.log r)^5 := by ring
    _ = _ := by rw [←hratio]; ring

lemma inverseObservationOffset_nonneg {D r : ℝ} (hD : 0≤D) (hr : 0<r) (hr1 : r≤1) :
    0 ≤ inverseObservationOffset D r := by
  have hl : Real.log (r^42)≤0 := Real.log_nonpos (by positivity) (pow_le_one₀ hr.le hr1)
  exact add_nonneg hD (mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
    (sq_nonneg _)) (pow_nonneg (by linarith) _))

lemma exists_inverseObservationOffset_small {D A : ℝ} (hD : 0≤D) (hA : 0<A) :
    ∃ s : ℝ, 0<s ∧ s≤1 ∧ ∀ {r a : ℝ}, 0<r → r<s → 0<a → a≤A*r →
      inverseObservationOffset D r≤a^(-349/50:ℝ) := by
  have ht := (inverseObservationOffset_scaled_tendsto D).mul_const (A^(349/50:ℝ))
  simp only [zero_mul] at ht
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      r<1 ∧ inverseObservationOffset D r*r^(349/50:ℝ)*A^(349/50:ℝ)<1 := by
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,
      ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hh
    exact ⟨hr,hh⟩
  obtain ⟨s,hs,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨min s 1,lt_min hs (by norm_num),min_le_right _ _,?_⟩
  intro r a hr hrs ha haA
  obtain ⟨hr1,hh⟩ := hsub ⟨hr,hrs.trans_le (min_le_left _ _)⟩
  have hδ := inverseObservationOffset_nonneg hD hr hr1.le
  have hmul : inverseObservationOffset D r*a^(349/50:ℝ)≤1 := by
    calc
      _ ≤ inverseObservationOffset D r*(A*r)^(349/50:ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le haA (by norm_num)) hδ
      _ = inverseObservationOffset D r*r^(349/50:ℝ)*A^(349/50:ℝ) := by rw [Real.mul_rpow hA.le hr.le]; ring
      _ ≤ 1 := hh.le
  rw [neg_div,Real.rpow_neg ha.le,inv_eq_one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).mpr hmul

theorem atomic_observation_refined_patch {D A : ℝ} (hD : 0≤D) (hA : 0<A) :
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
        2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,hscale⟩ := exists_inverseObservationOffset_small hD hA
  obtain ⟨s₁,hs₁,_,hpatch⟩ := Coulomb.exists_atomic_small_physical_gap
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
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

theorem atomic_observation_patch_and_near_bound {D A : ℝ} (hD : 0≤D) (hA : 0<A) :
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
    (∀ {R : ℝ}, 0≤R → R≤4*Coulomb.atomicCellScale y →
      Coulomb.potentialForm (Coulomb.nearPotential y R) u≤
        Coulomb.atomicNearConstant*(Coulomb.atomicCellScale y)^(-21/5:ℝ)*R^(1/5:ℝ)) ∧
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
        2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,hscale⟩ := exists_inverseObservationOffset_small hD hA
  obtain ⟨s₁,hs₁,hs₁1,hnear⟩ := Coulomb.exists_atomic_near_scale
  obtain ⟨s₂,hs₂,hpatch⟩ := atomic_observation_refined_patch hD hA
  refine ⟨min s₂ (min s₀ (s₁/A)),lt_min hs₂ (lt_min hs₀ (div_pos hs₁ hA)),?_⟩
  intro n Z hZ ψ g hd hn hmin E hE hbase r hr hrs B hB hsym hprob y hy hya
  have hrs₂ : r<s₂ := hrs.trans_le (min_le_left _ _)
  have hrs' : r < min s₀ (s₁/A) := hrs.trans_le (min_le_right _ _)
  have hrs₀ : r<s₀ := hrs'.trans_le (min_le_left _ _)
  have hay : Coulomb.atomicCellScale y<s₁ := hya.trans_lt (by
    simpa only [mul_comm] using (lt_div_iff₀ hA).mp (hrs'.trans_le (min_le_right _ _)))
  obtain ⟨u,hu,hm,he,hlaw,T⟩ := hpatch Z hZ hd hn hmin hE hbase hr hrs₂ hB hsym hprob y hy hya
  refine ⟨u,hu,hm,he,hlaw,?_,T⟩
  exact hnear (Coulomb.atom Z hZ) (by intro i; rfl) u hu hm hE he
    (inverseObservationOffset_nonneg hD hr (hrs₀.le.trans hs₀1)) y hy hay
    (hscale hr hrs₀ (Coulomb.atomicCellScale_pos hy) hya)
end NeutralAtom

end

end OAI
