import OAI.Probability.RadialTransition.CorePressureLower

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma measurableSet_tetraRegion (t a : ℝ) : MeasurableSet (tetraRegion t a) := by
  apply MeasurableSet.inter
  · exact (measurableSet_cube a).preimage (measurable_pi_apply 0)
  · change MeasurableSet {x : Fin 4 → Position | ∀ j : Fin 3, x j.succ-x 0-tetraVertex t j.succ ∈ cube (tetraEpsilon t)}
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_cube _).preimage (((measurable_pi_apply j.succ).sub (measurable_pi_apply 0)).sub measurable_const)

lemma lintegral_tetra_fiber (t : ℝ) (x : Position) :
    (∫⁻ y : Fin 3 → Position, ∏ j, regionMask (cube (tetraEpsilon t)) (y j-x-tetraVertex t j.succ)
      ∂Measure.pi (fun _ => volume)) = (ENNReal.ofReal (tetraEpsilon t)^3)^3 := by
  have he (y : Fin 3 → Position) :
      (∏ j, regionMask (cube (tetraEpsilon t)) (y j-x-tetraVertex t j.succ)) =
      (Set.pi univ (fun j : Fin 3 => translateSet (x+tetraVertex t j.succ) (cube (tetraEpsilon t)))).indicator (fun _ => 1) y := by
    simp only [regionMask, Set.indicator, Finset.prod_boole]
    have hm : (∀ j : Fin 3, y j-x-tetraVertex t j.succ ∈ cube (tetraEpsilon t)) ↔
        y ∈ Set.pi univ (fun j : Fin 3 => translateSet (x+tetraVertex t j.succ) (cube (tetraEpsilon t))) := by
      simp [Set.mem_pi, translateSet, sub_sub]
    simp [hm]
  simp_rw [he]
  change (∫⁻ y, (Set.pi univ (fun j : Fin 3 => translateSet (x+tetraVertex t j.succ) (cube (tetraEpsilon t)))).indicator (1 : (Fin 3 → Position) → ℝ≥0∞) y ∂Measure.pi (fun _ => volume)) = _
  rw [lintegral_indicator_one, Measure.pi_pi]
  · simp_rw [volume_translateSet _ _ (measurableSet_cube _), volume_cube]
    simp
  · exact MeasurableSet.univ_pi (fun _ => measurableSet_translate (measurableSet_cube _))

lemma volume_tetraRegion (t a : ℝ) :
    volume (tetraRegion t a) = ENNReal.ofReal a^3*(ENNReal.ofReal (tetraEpsilon t)^3)^3 := by
  let F (p : Position × (Fin 3 → Position)) : ℝ≥0∞ :=
    regionMask (cube a) p.1 * ∏ j, regionMask (cube (tetraEpsilon t)) (p.2 j-p.1-tetraVertex t j.succ)
  have hF : Measurable F := by
    apply ((measurable_regionMask (measurableSet_cube _)).comp measurable_fst).mul
    apply Finset.measurable_prod
    intro j _
    apply (measurable_regionMask (measurableSet_cube _)).comp
    fun_prop
  have he (x : Fin 4 → Position) :
      (tetraRegion t a).indicator (fun _ => (1:ℝ≥0∞)) x =
      F (x 0, fun j => x j.succ) := by
    by_cases h1 : x 0 ∈ cube a <;>
      by_cases h2 : ∀ j : Fin 3, x j.succ-x 0-tetraVertex t j.succ ∈ cube (tetraEpsilon t) <;>
      simp [F, regionMask, tetraRegion, Set.indicator, Finset.prod_boole, h1, h2]

  rw [← lintegral_indicator_one (measurableSet_tetraRegion t a)]
  change (∫⁻ x, (tetraRegion t a).indicator (fun _ => (1:ℝ≥0∞)) x) = _
  rw [volume_pi]
  simp_rw [he]
  have hh := (measurePreserving_piFinSuccAbove (fun _ : Fin 4 => (volume : Measure Position)) 0).lintegral_comp hF
  simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply] at hh
  have her (x : Fin 4 → Position) : Fin.removeNth 0 x = fun j => x j.succ := by
    funext j
    simp only [Fin.removeNth_apply, Fin.succAbove_zero]
  simp_rw [her] at hh
  rw [hh, lintegral_prod _ hF.aemeasurable]
  have hfin (x : Position) : regionMask (cube a) x ≠ ⊤ := by
    by_cases hx : x ∈ cube a <;> simp [regionMask, hx]
  simp only [F]
  simp_rw [lintegral_const_mul' _ _ (hfin _), lintegral_tetra_fiber]
  rw [lintegral_mul_const']
  · change (∫⁻ x, (cube a).indicator (1 : Position → ℝ≥0∞) x) * _ = _
    rw [lintegral_indicator_one (measurableSet_cube _), volume_cube]
  · exact ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

lemma partitionOn_tetra_lower (t a β : ℝ) (ha : 0 ≤ a) :
    a^3*(tetraEpsilon t)^9/24 ≤ partitionOn (corePotential t) (cube (a+3*microLength t)) 4 β := by
  have hs : tetraRegion t a ⊆ configurationCube (a+3*microLength t) 4 := fun _ hx => tetraRegion_cube hx
  have hc : Set.univ.pi (fun _ : Fin 4 => cube (a+3*microLength t)) = configurationCube (a+3*microLength t) 4 := by
    ext x
    simp [configurationCube, Set.mem_pi]
  have hfin : volume (cube (a+3*microLength t)) ≠ ⊤ := by rw [volume_cube]; finiteness
  let : IsFiniteMeasure (volume.restrict (cube (a+3*microLength t))) := isFiniteMeasure_restrict.mpr hfin
  have hi := integrable_orderedBoltzmann (ι := Fin 4) (continuous_corePotential t) (bounded_corePotential t) β (Measure.pi (fun _ : Fin 4 => volume.restrict (cube (a+3*microLength t))))
  rw [← Measure.restrict_pi_pi, hc, ← volume_pi] at hi
  have hle := integral_mono_measure (Measure.restrict_mono hs le_rfl)
    (Eventually.of_forall (fun x : Fin 4 → Position => (Real.exp_pos (-β*orderedEnergy (corePotential t) x)).le)) hi
  have he : (∫ x in tetraRegion t a, Real.exp (-β*orderedEnergy (corePotential t) x)) =
      a^3*(tetraEpsilon t)^9 := by
    have hh : (∫ x in tetraRegion t a, Real.exp (-β*orderedEnergy (corePotential t) x)) =
        ∫ _x in tetraRegion t a, (1:ℝ) := by
      apply setIntegral_congr_fun (measurableSet_tetraRegion t a)
      intro x hx
      change Real.exp (-β*orderedEnergy (corePotential t) x) = 1
      rw [orderedEnergy_fin, tetraRegion_core_zero hx, mul_zero, Real.exp_zero]
    rw [hh, integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      volume_tetraRegion, smul_eq_mul, mul_one, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (tetraEpsilon_pos t).le]
    ring
  rw [he] at hle
  rw [partitionOn, rawPartition_setIntegral, hc]
  norm_num only [Nat.factorial, Nat.cast_ofNat, inv_eq_one_div]
  linarith

end RadialTransition
end

end OAI
