import OAI.Probability.RadialTransition.BadRemoval

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma measurableSet_nearCube (r : ℝ) (x : Position) : MeasurableSet (nearCube r x) := by
  simp only [nearCube, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_le (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).sub continuous_const).abs.measurable) measurable_const

lemma nearCube_translate (r : ℝ) (x : Position) :
    nearCube r x = translateSet (x-WithLp.toLp 2 (fun _ : Fin 3 => r)) (cube (2*r)) := by
  ext y
  change (∀ k, |y k-x k| ≤ r) ↔ ∀ k, 0 ≤ y k-(x k-r) ∧ y k-(x k-r) ≤ 2*r
  simp only [abs_le]
  constructor <;> intro h k <;> obtain ⟨h1,h2⟩ := h k <;> constructor <;> linarith

lemma volume_nearCube (r : ℝ) (x : Position) :
    volume (nearCube r x) = ENNReal.ofReal (2*r)^3 := by
  rw [nearCube_translate, volume_translateSet _ _ (measurableSet_cube _), volume_cube]

lemma nearMask_self {r : ℝ} (hr : 0 ≤ r) (x : Position) : nearMask r x x = 1 := by
  apply indicator_of_mem
  intro k
  simpa using hr

lemma lintegral_nearMask_prod (n : ℕ) (r : ℝ) (x : Position) :
    (∫⁻ y : Fin n → Position, ∏ j, nearMask r x (y j) ∂Measure.pi (fun _ => volume)) =
      (ENNReal.ofReal (2*r)^3)^n := by
  have he (y : Fin n → Position) :
      (∏ j, nearMask r x (y j)) = (Set.pi univ (fun _ : Fin n => nearCube r x)).indicator (fun _ => 1) y := by
    simp [nearMask, Set.indicator, Finset.prod_boole, Set.mem_pi]
  simp_rw [he]
  change (∫⁻ y, (Set.pi univ (fun _ : Fin n => nearCube r x)).indicator (1 : (Fin n → Position) → ℝ≥0∞) y ∂Measure.pi (fun _ => volume)) = _
  rw [lintegral_indicator_one, Measure.pi_pi, volume_nearCube]
  · simp
  · exact MeasurableSet.univ_pi (fun _ => measurableSet_nearCube r x)

lemma lintegral_rootStar (A : Set Position) (hA : MeasurableSet A) {r : ℝ} (hr : 0 ≤ r)
    (n : ℕ) (i : Fin (n+1)) :
    (∫⁻ x : Fin (n+1) → Position, regionMask A (x i)*∏ j, nearMask r (x i) (x j)
      ∂Measure.pi (fun _ => volume)) = volume A*(ENNReal.ofReal (2*r)^3)^n := by
  have hprod : Measurable (fun p : Position × (Fin n → Position) =>
      regionMask A p.1 * ∏ j, nearMask r p.1 (p.2 j)) := by
    apply ((measurable_regionMask hA).comp measurable_fst).mul
    apply Finset.measurable_prod
    intro j _
    exact (measurable_nearMask r).comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hh := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure Position)) i).lintegral_comp hprod
  simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply, Fin.removeNth_apply] at hh
  have he (x : Fin (n+1) → Position) : (∏ j, nearMask r (x i) (x j)) = ∏ j : Fin n, nearMask r (x i) (x (i.succAbove j)) := by
    rw [i.prod_univ_succAbove, nearMask_self hr, one_mul]
  simp_rw [he]
  rw [hh, lintegral_prod _ hprod.aemeasurable]
  have hfin (x : Position) : regionMask A x ≠ ⊤ := by
    by_cases hx : x ∈ A <;> simp [regionMask, hx]
  simp_rw [lintegral_const_mul' _ _ (hfin _)]
  simp_rw [lintegral_nearMask_prod]
  rw [lintegral_mul_const']
  · change (∫⁻ x, A.indicator (1 : Position → ℝ≥0∞) x) * _ = _
    rw [lintegral_indicator_one hA]
  · exact (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))

lemma lintegral_starWeight (A : Set Position) (hA : MeasurableSet A) {r : ℝ} (hr : 0 ≤ r)
    (n : ℕ) :
    (∫⁻ x : Fin (n+1) → Position, starWeight A r (configurationMultiset x)
      ∂Measure.pi (fun _ => volume)) = (n+1 : ℕ)*(volume A*(ENNReal.ofReal (2*r)^3)^n) := by
  simp only [starWeight, configurationMultiset_sum_map, configurationMultiset_prod_map]
  rw [lintegral_finsetSum]
  · simp_rw [lintegral_rootStar A hA hr]
    simp
  · intro i _
    apply ((measurable_regionMask hA).comp (measurable_pi_apply i)).mul
    apply Finset.measurable_prod
    intro j _
    have hm := (measurable_nearMask r).comp
      ((show Measurable (fun x : Fin (n+1) → Position => x i) from measurable_pi_apply i).prodMk
        (show Measurable (fun x : Fin (n+1) → Position => x j) from measurable_pi_apply j))
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hm

end RadialTransition
end

end OAI
