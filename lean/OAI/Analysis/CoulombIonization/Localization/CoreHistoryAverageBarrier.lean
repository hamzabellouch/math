import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutCoreExcess
import OAI.Analysis.CoulombIonization.Localization.FormRawLaw
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryCoordinatesBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

def coreLawAverage {N M : ℕ} (ψ : FormVector (N+M)) (F : FormVector N → ℝ) : ℝ :=
  ∑ t : Spins M, ∫ v, F (coreSlice ψ t v)

lemma coreLawAverage_mass {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ) :
    coreLawAverage ψ formMass = formMass ψ := hψ.integral_coreSlice_mass

lemma nextCoreObservation_statistic_integrable {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (F : FormVector (cutCoreNumber c) → ℝ)
    (hF : ∀ s, Integrable (fun u => F (coreSlice (nextCoreObservation p hp ψ c) s u)))
    (t : Spins M) :
    Integrable (fun v => coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) F) := by
  apply integrable_finsetSum
  intro s _
  have hi := integrable_join (hF (joinLists s t))
  simp only [nextCoreObservation_slice] at hi
  exact hi.integral_prod_right

theorem coreLawAverage_next {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (F : FormVector (cutCoreNumber c) → ℝ)
    (hF : ∀ s, Integrable (fun u => F (coreSlice (nextCoreObservation p hp ψ c) s u))) :
    coreLawAverage (nextCoreObservation p hp ψ c) F =
      ∑ t : Spins M, ∫ v, coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) F := by
  unfold coreLawAverage
  rw [←sum_spin_join]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [←integral_join (hF (joinLists s t))]
    simp only [nextCoreObservation_slice]
  · intro s _
    have hi := integrable_join (hF (joinLists s t))
    simp only [nextCoreObservation_slice] at hi
    exact hi.integral_prod_right

lemma coreLawAverage_next_mass {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    formMass (nextCoreObservation p hp ψ c) =
      ∑ t : Spins M, ∫ v, formMass (orderedCutForm p hp (coreSlice ψ t v) c) := by
  rw [←coreLawAverage_mass (nextCoreObservation_sobolev hψ p hp c),
    coreLawAverage_next ψ p hp c formMass
      (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_mass_integrable s)]
  apply Finset.sum_congr rfl
  intro t _
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_mass (orderedCutForm_sobolev p hp hv c)

lemma nextCoreObservation_mass_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (t : Spins M) :
    Integrable (fun v => formMass (orderedCutForm p hp (coreSlice ψ t v) c)) := by
  apply (nextCoreObservation_statistic_integrable ψ p hp c formMass
    (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_mass_integrable s) t).congr
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_mass (orderedCutForm_sobolev p hp hv c)

lemma coreLawAverage_excess {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (Z lam : ℝ) :
    coreLawAverage ψ (corePriceExcess Z lam) =
      (∑ t : Spins M, ∫ v, formEnergy Z (coreSlice ψ t v))+
        lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ := by
  have he (t : Spins M) : (∫ v, corePriceExcess Z lam (coreSlice ψ t v)) =
      (∫ v, formEnergy Z (coreSlice ψ t v))+lam*N*(∫ v, formMass (coreSlice ψ t v))-
        priceEnergy (energy Z) lam*(∫ v, formMass (coreSlice ψ t v)) := by
    simp only [corePriceExcess]
    rw [integral_sub,integral_add,integral_const_mul,integral_const_mul]
    · exact hψ.coreSlice_energy_integrable Z t
    · exact (hψ.coreSlice_mass_integrable t).const_mul (lam*N)
    · exact (hψ.coreSlice_energy_integrable Z t).add
        ((hψ.coreSlice_mass_integrable t).const_mul (lam*N))
    · exact (hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam)
  unfold coreLawAverage
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
    hψ.integral_coreSlice_mass]

lemma coreLawAverage_ordered_excess {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ) :
    coreLawAverage (orderedCutForm p hp ψ c) (corePriceExcess Z lam) =
      cutCoreExcess p hp Z lam ψ c :=
  coreLawAverage_excess (orderedCutForm_sobolev p hp hψ c) Z lam

lemma coreLawAverage_next_excess {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ) :
    coreLawAverage (nextCoreObservation p hp ψ c) (corePriceExcess Z lam) =
      ∑ t : Spins M, ∫ v, cutCoreExcess p hp Z lam (coreSlice ψ t v) c :=
by
  rw [coreLawAverage_next ψ p hp c (corePriceExcess Z lam)
    (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_excess_integrable Z lam s)]
  apply Finset.sum_congr rfl
  intro t _
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_ordered_excess hv p hp c Z lam

lemma nextCoreObservation_excess_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (t : Spins M) (Z lam : ℝ) :
    Integrable (fun v => cutCoreExcess p hp Z lam (coreSlice ψ t v) c) :=
by
  apply (nextCoreObservation_statistic_integrable ψ p hp c (corePriceExcess Z lam)
    (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_excess_integrable Z lam s) t).congr
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_ordered_excess hv p hp c Z lam

open MeasureTheory Filter
open scoped BigOperators

def rawFormPair {N : ℕ} (ψ : FormVector N) (g : Configuration N → ℝ) : ℝ :=
  ∑ s : Spins N, ∫ x, g x*‖ψ.value s x‖^2

lemma rawFormPair_eq_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    rawFormPair ψ g = ∫ x, g x ∂formRawLaw ψ :=
  (formRawLaw_integral_eq_spin_sum hψ hg hB).symm

lemma leftList_measurable {N M : ℕ} : Measurable (leftList (N := N) (M := M) (α := Space)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma rawFormPair_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (t : Spins M) : Integrable (fun v => rawFormPair (coreSlice ψ t v) g) := by
  apply integrable_finsetSum
  intro s _
  have hi : Integrable (fun x => g (leftList x)*‖ψ.value (joinLists s t) x‖^2) :=
    ((hψ.1 _).norm.integrable_sq).bdd_mul (hg.comp leftList_measurable).aestronglyMeasurable
      (ae_of_all _ (fun x => hB (leftList x)))
  have hj := (integrable_join (N := N) (M := M) hi).integral_prod_right
  simpa only [coreSlice,leftList_join] using hj

lemma coreLawAverage_rawFormPair {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    coreLawAverage ψ (fun φ => rawFormPair φ g) = rawFormPair ψ (g ∘ leftList) := by
  have hi (s : Spins (N+M)) : Integrable (fun x => g (leftList x)*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul (hg.comp leftList_measurable).aestronglyMeasurable
      (ae_of_all _ (fun x => hB (leftList x)))
  have he (s : Spins N) (t : Spins M) :
      (∫ v : Configuration M, ∫ x : Configuration N,
        g x*‖(coreSlice ψ t v).value s x‖^2) =
      ∫ x, g (leftList x)*‖ψ.value (joinLists s t) x‖^2 := by
    simpa only [coreSlice,leftList_join] using integral_join (N := N) (M := M) (hi (joinLists s t))
  unfold coreLawAverage rawFormPair
  have hsum (t : Spins M) :
      (∫ v, ∑ s : Spins N, ∫ x, g x*‖(coreSlice ψ t v).value s x‖^2) =
      ∑ s : Spins N, ∫ v, ∫ x, g x*‖(coreSlice ψ t v).value s x‖^2 := by
    apply integral_finsetSum
    intro s _
    simpa only [coreSlice,leftList_join] using
      (integrable_join (N := N) (M := M) (hi (joinLists s t))).integral_prod_right
  simp_rw [hsum,he]
  exact sum_spin_join (fun s : Spins (N+M) => ∫ x, g (leftList x)*‖ψ.value s x‖^2)

def cutCorePositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) :
    Configuration (cutCoreNumber c) :=
  fun i => x (cutOrder c (finSumFinEquiv (Sum.inl i)))

lemma cutCorePositions_reindex {L : ℕ} (c : Fin L → Fin 2)
    (x : Configuration (cutCoreNumber c+cutOutNumber c)) :
    cutCorePositions c (x ∘ (cutOrder c).symm) = leftList x := by
  ext i
  simp only [cutCorePositions,Function.comp_apply,Equiv.symm_apply_apply,leftList]

lemma cutCorePositions_measurable {L : ℕ} (c : Fin L → Fin 2) : Measurable (cutCorePositions c) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply _

lemma cutCore_rawFormPair {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevVector ψ)
    (c : Fin L → Fin 2) {g : Configuration (cutCoreNumber c) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    coreLawAverage (orderedCutForm p hp ψ c) (fun φ => rawFormPair φ g) =
      rawFormPair (multiplyForm (spatialProduct p hp c) ψ) (g ∘ cutCorePositions c) := by
  rw [coreLawAverage_rawFormPair (orderedCutForm_sobolev p hp hψ c) hg hB]
  have he (s : Spins (cutCoreNumber c+cutOutNumber c)) :
      (∫ x, g (leftList x)*‖(orderedCutForm p hp ψ c).value s x‖^2) =
      ∫ x, g (cutCorePositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value
        (s ∘ (cutOrder c).symm) x‖^2 := by
    simpa only [orderedCutForm,reindexForm,cutCorePositions_reindex] using
      integral_reindex (cutOrder c) (fun x => g (cutCorePositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value (s ∘ (cutOrder c).symm) x‖^2)
  unfold rawFormPair
  simp only [Function.comp_apply]
  simp_rw [he]
  exact sum_spin_reindex (cutOrder c) (fun s : Spins L =>
    ∫ x, g (cutCorePositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2)

lemma sum_cutCorePositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) (f : Space → ℝ) :
    (∑ i, f (cutCorePositions c x i)) = ∑ i, if c i = 0 then f (x i) else 0 := by
  classical
  have he := Equiv.sum_comp (Fintype.equivFin {i // c i = 0}).symm (fun i => f (x i.val))
  have hs := Finset.sum_subtype (p := fun i => c i = 0) (F := inferInstance) (Finset.univ.filter (fun i => c i = 0))
    (fun _ => by simp) (fun i => f (x i))
  calc
    _ = ∑ i : {i // c i = 0}, f (x i.val) := by
      simpa only [cutCorePositions,cutOrder,Equiv.trans_apply,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumCompl_apply_inl] using he
    _ = ∑ i ∈ Finset.univ.filter (fun i => c i = 0), f (x i) := hs.symm
    _ = _ := Finset.sum_filter _ _

end CoulombAtom

end

end OAI
