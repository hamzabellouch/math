import Mathlib
import OAI.Analysis.CoulombIonization.Localization.FreshObservedSandwichBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation

lemma cutOutPositions_measurable {N : ℕ} (c : Fin N → Fin 2) :
    Measurable (cutOutPositions c) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma fresh_cut_support_of_raw_ae {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (c : Fin N → Fin 2) {P : Configuration (cutOutNumber c) → Prop}
    (hP : MeasurableSet {u | P u})
    (hraw : ∀ᵐ x ∂formRawLaw ψ, (spatialProduct p hp c).value x ≠ 0 → P (cutOutPositions c x)) :
    ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm p hp ψ c) s u) ≠ 0 → P u := by
  classical
  let g : Configuration (cutOutNumber c) → ℝ := fun u => if P u then 0 else 1
  have hg : Measurable g := measurable_const.ite hP measurable_const
  have hgn (u) : 0 ≤ g u := by dsimp only [g]; split_ifs <;> norm_num
  have hgb (u) : ‖g u‖ ≤ 1 := by dsimp only [g]; split_ifs <;> norm_num
  have hv := (ae_withDensity_iff' (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal).mp hraw
  have hzero (s : Spins N) : ∀ᵐ x,
      g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 = 0 := by
    filter_upwards [hv] with x hx
    by_cases hd : ENNReal.ofReal (formRawDensity ψ x) = 0
    · have hs : ‖ψ.value s x‖^2 ≤ formRawDensity ψ x := by
        unfold formRawDensity
        exact Finset.single_le_sum (fun t _ => sq_nonneg ‖ψ.value t x‖) (Finset.mem_univ s)
      have hn : ‖ψ.value s x‖ = 0 := sq_eq_zero_iff.mp
        (le_antisymm (hs.trans (ENNReal.ofReal_eq_zero.mp hd)) (sq_nonneg _))
      simp only [multiplyForm,norm_eq_zero.mp hn,mul_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    · by_cases hm : (spatialProduct p hp c).value x = 0
      · simp only [multiplyForm,hm,Complex.ofReal_zero,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
      · simp only [g,ite_eq_left (hx hd hm),zero_mul]
  have hi (s : Spins (cutOutNumber c)) :
      Integrable (fun u => g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) :=
    ((orderedCutForm_sobolev p hp hψ c).coreSlice_mass_integrable s).bdd_mul
      hg.aestronglyMeasurable (ae_of_all _ hgb)
  have hsum : (∑ s : Spins (cutOutNumber c), ∫ u,
      g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = 0 := by
    rw [cutOuter_expectation_eq_full p hp hψ c hg hgb]
    exact Finset.sum_eq_zero (fun s _ => integral_eq_zero_of_ae (hzero s))
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
    integral_nonneg (fun u => mul_nonneg (hgn u) (formMass_nonneg _)))).mp hsum
  intro s
  have he := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (fun u => mul_nonneg (hgn u) (formMass_nonneg _))) (hi s)).mp
      (hterms s (Finset.mem_univ s))
  filter_upwards [he] with u hu
  intro hm
  by_contra hpu
  exact hm (by simpa only [g,ite_eq_right hpu,one_mul,Pi.zero_apply] using hu)

lemma event_fresh_cut_support {N K : ℕ} (F G : fermionGraph N) (ell : Fin K → ℝ)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (c : Fin N → Fin 2) {P : Configuration (cutOutNumber c) → Prop}
    (hP : MeasurableSet {u | P u})
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))} (hA : MeasurableSet A)
    {d : ℝ≥0∞} (hlaw : graphRawLaw G = d • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    (hpath : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A →
      (spatialProduct p hp c).value z.1 ≠ 0 → P (cutOutPositions c z.1)) :
    ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm p hp (graphFormVector G) c) s u) ≠ 0 → P u := by
  have hpred : MeasurableSet {x | (spatialProduct p hp c).value x ≠ 0 → P (cutOutPositions c x)} := by
    have hval : Measurable (spatialProduct p hp c).value :=
      (spatialProduct p hp c).regular.continuous.measurable
    have he : {x | (spatialProduct p hp c).value x ≠ 0 → P (cutOutPositions c x)} =
        {x | (spatialProduct p hp c).value x = 0} ∪ (cutOutPositions c) ⁻¹' {u | P u} := by
      ext x; simp only [mem_ofPred_eq,mem_union,mem_preimage]; tauto
    rw [he]
    exact (measurableSet_eq_fun hval measurable_const).union (hP.preimage (cutOutPositions_measurable c))
  apply fresh_cut_support_of_raw_ae p hp (graphFormVector_sobolev G).sobolevVector c hP
  rw [formRawLaw_graph]
  exact event_rawLaw_ae F G ell hlaw hpred hA hpath

end CoulombAtom

end

end OAI
