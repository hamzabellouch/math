import Mathlib
import OAI.Analysis.CoulombRadii.Screening.UpperDeficit
import OAI.Analysis.CoulombRadii.LimitTheory.AtomicOutKinetic
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorBottomBridge
import OAI.Analysis.CoulombRadii.RandomFields.BinaryDeletion
import OAI.Analysis.CoulombRadii.Screening.CoreCount

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb.RecordedEnsemble

lemma core_gap_lower {J n Z : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    (hF : T.CoreFermionic) (hmono : Antitone (sectorFormBottom S))
    {E P : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (hP : (P:EReal)≤ sectorFormBottom S (Z-1)) :
    E*T.totalMass+(P-E)*T.favorableMass Z≤T.totalCoreForm S := by
  have H p : E*mass (T.vector p)+(P-E)*(if (T.core p:ℝ)<(Z:ℝ) then mass (T.vector p) else 0)≤
      sliceExpectation (T.vector p) (fun s x => form S ((T.vector p).coreSlice s x).normalized) := by
    by_cases hp : (T.core p:ℝ)<(Z:ℝ)
    · rw [ite_eq_left hp]
      have hk : T.core p≤Z-1 := by have := (Nat.cast_lt (α:=ℝ)).mp hp; omega
      have h := slice_core_form_ge_sector S (T.vector p) (fun s => (hF p).coreSlice s) (hP.trans (hmono hk))
      nlinarith
    · rw [ite_eq_right hp,mul_zero,add_zero]
      exact slice_core_form_ge_baseline S (T.vector p) (fun s => (hF p).coreSlice s) hE
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => H p)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,totalMass,favorableMass,totalCoreForm] using hh

lemma predecessor_bound_of_core_budget {J n Z : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    (hF : T.CoreFermionic) (hmono : Antitone (sectorFormBottom S))
    {E P M C : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (hP : (P:EReal)≤ sectorFormBottom S (Z-1)) (hEP : E≤P)
    (hM : 0<M) (hm : T.totalMass=1) (hmean : 1≤(Z:ℝ)-T.coreMean)
    (hsecond : T.coreDeficitMoment Z≤M) (henergy : T.totalCoreForm S≤E+C) :
    P≤E+M*C := by
  have H := core_gap_lower S T hF hmono hE hP
  rw [hm,mul_one] at H
  have hf := favorableMass_of_core_moments T hM hm hmean hsecond
  have hc := mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr hEP)
  have hd : (P-E)/M≤C := by
    simp only [div_eq_mul_inv,one_mul] at hc
    rw [div_eq_mul_inv]
    linarith
  have hmC := (div_le_iff₀ hM).mp hd
  nlinarith

end Coulomb.RecordedEnsemble
end

end
section
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma event_count_upper {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F : Configuration n → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0≤F x) (hF1 : ∀ x, F x≤1)
    {A : Set Position} (hA : MeasurableSet A) {T : ℝ}
    (hmatch : ∀ x, 0<F x → Coulomb.localCount A (flattenConfiguration n x)≤T)
    (hp : 0<stateWeightedIntegral ψ F) :
    (stateWeightedIntegral ψ F)⁻¹*stateWeightedIntegral ψ
      (fun x => F x*Coulomb.localCount A (flattenConfiguration n x))≤T := by
  have hm : Measurable (fun x : Configuration n => Coulomb.localCount A (flattenConfiguration n x)) :=
    (Coulomb.localCount_measurable hA).comp (flattenConfiguration n).continuous.measurable
  have H := stateWeightedIntegral_mono_bounded hd
    (F:=fun x => F x*Coulomb.localCount A (flattenConfiguration n x))
    (G:=fun x => T*F x) (hF.mul hm) (measurable_const.mul hF)
    (C:=(n:ℝ)) (D:=|T|)
    (fun x => by
      rw [abs_of_nonneg (mul_nonneg (hF0 x) (Coulomb.localCount_nonneg A _))]
      exact (mul_le_of_le_one_left (Coulomb.localCount_nonneg A _) (hF1 x)).trans
        (Coulomb.localCount_le A _))
    (fun x => by
      rw [abs_mul,abs_of_nonneg (hF0 x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF1 x))
    (fun x => by
      by_cases hx : F x=0
      · simp [hx]
      · have H := mul_le_mul_of_nonneg_left (hmatch x (lt_of_le_of_ne (hF0 x) (Ne.symm hx))) (hF0 x)
        simpa only [mul_comm] using H)
  rw [stateWeightedIntegral_const_mul] at H
  calc
    _ ≤ (stateWeightedIntegral ψ F)⁻¹*(T*stateWeightedIntegral ψ F) :=
      mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hp.le)
    _ = T := by field_simp

theorem atomic_arrayEvent_deficit_upper {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈s ↔ y∈s)
    (hp : 0<stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)) {r T : ℝ} (hr : 0<r)
    (hmatch : ∀ x, 0<arrayEventLikelihood ℓ s x →
      Coulomb.localCount (Metric.ball 0 r) (flattenConfiguration n x)≤(Z:ℝ)-T) :
    T≤2*Coulomb.atomicInnerFieldConstant*Coulomb.screenMass
      (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
        (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r := by
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase ℓ hℓ hs hsym hp
  have hb := Coulomb.atomic_inner_deficit_upper (Coulomb.atom Z hZ) (by intro i; rfl)
    u hu hum hE hue (observationEventOffset_nonneg hd hn hD ℓ hs hp) hr
  rw [Coulomb.expectedPopulation_eq u measurableSet_ball] at hb
  change Coulomb.totalCharge (Coulomb.atom Z hZ)-Coulomb.potentialForm _ u≤_ at hb
  rw [hlaw] at hb
  have hlow := event_count_upper hd (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
    measurableSet_ball hmatch hp
  have hcharge : Coulomb.totalCharge (Coulomb.atom Z hZ)=(Z:ℝ) := by
    simp [Coulomb.totalCharge,Coulomb.atom]
  rw [hcharge] at hb
  linarith

lemma raw_inner_observed_count_le {n : ℕ} (x y : Configuration n) {r a e : ℝ}
    (hre : r+e≤a) (hxy : ∀ i, ‖y i-x i‖≤e) :
    Coulomb.localCount (Metric.ball 0 r) (flattenConfiguration n x)≤
      rawCount (Metric.ball 0 a) y := by
  simp only [Coulomb.localCount,position_flattenConfiguration,rawCount]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x i∈Metric.ball 0 r
  · have hx' : ‖x i‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hh : ‖y i‖≤‖y i-x i‖+‖x i‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y i-x i) (x i)
    have hy : y i∈Metric.ball 0 a := by
      rw [Metric.mem_ball,dist_zero_right]
      linarith [hxy i]
    simp only [indicator_of_mem hx,indicator_of_mem hy,le_refl]
  · rw [indicator_of_notMem hx]
    exact indicator_nonneg (fun _ _ => by positivity) _

lemma observed_deficit_event_measurable {H : Type*} {n : ℕ} (h : H) (Z a T : ℝ) :
    MeasurableSet {y : (H × (Fin n × Fin 3)) → ℝ |
      T<Z-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} :=
  measurableSet_lt measurable_const (measurable_const.sub
    ((measurable_rawCount measurableSet_ball).comp (measurable_observationArrayPositions h)))

lemma observed_deficit_event_symmetric {H : Type*} {n : ℕ} (h : H) (Z a T : ℝ)
    (p : Equiv.Perm (Fin n)) (y : (H × (Fin n × Fin 3)) → ℝ) :
    permuteObservationArray p y∈{y | T<Z-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} ↔
    y∈{y | T<Z-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} := by
  have he : observationArrayPositions h (permuteObservationArray p y)=observationArrayPositions h y ∘ p := rfl
  simp only [mem_ofPred_eq,he,rawCount,Function.comp_apply]
  have hh := Equiv.sum_comp p (fun i => (Metric.ball 0 a).indicator (fun _ => (1:ℝ)) (observationArrayPositions h y i))
  exact congrArg (fun q => T<Z-q) hh |> Iff.of_eq

theorem atomic_observed_inner_deficit_tail {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H) {r a T p₀ : ℝ}
    (hr : 0<r) (hp₀ : 0<p₀) (hre : r+Real.sqrt 3*ℓ h≤a)
    (hth : 2*Coulomb.atomicInnerFieldConstant*Coulomb.screenMass
      (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r<T) :
    stateWeightedIntegral ψ (arrayEventLikelihood ℓ
      {y | T<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)})≤p₀ := by
  let s : Set ((H × (Fin n × Fin 3)) → ℝ) :=
    {y | T<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)}
  have hs : MeasurableSet s := observed_deficit_event_measurable h Z a T
  by_contra hc
  have hp : 0<stateWeightedIntegral ψ (arrayEventLikelihood ℓ s) := hp₀.trans (lt_of_not_ge hc)
  have hp1 := stateWeightedIntegral_le_one hd hn (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
  have hm : ∀ x, 0<arrayEventLikelihood ℓ s x →
      Coulomb.localCount (Metric.ball 0 r) (flattenConfiguration n x)≤(Z:ℝ)-T := by
    intro x hx
    obtain ⟨u,hu,he⟩ := arrayEventLikelihood_pos_matching ℓ (fun k => (hℓ k).ne') s x hx
    have H := raw_inner_observed_count_le x
      (observationArrayPositions h (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)) hre
      (observationArrayPositions_displacement ℓ hℓ x hu h)
    change T<(Z:ℝ)-rawCount _ _ at he
    linarith
  have hb := atomic_arrayEvent_deficit_upper Z hZ hd hn hmin hE hbase hD ℓ hℓ hs
    (observed_deficit_event_symmetric h Z a T) hp hr hm
  have hδ := observationEventOffset_mono_probability ℓ D₀ hp₀ (le_of_not_ge hc) hp1
  have hmass : Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r≤
    Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r := by
    unfold Coulomb.screenMass
    exact add_le_add le_rfl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hδ hr.le))
  have := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (by norm_num : (0:ℝ)≤2) Coulomb.atomicInnerFieldConstant_nonneg)
  linarith

end NeutralAtom

end

end
end

end OAI
