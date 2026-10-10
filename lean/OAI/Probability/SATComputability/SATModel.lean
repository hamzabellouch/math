import OAI.Probability.DilutedSpin.Model

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

def literalFactor (sign value : Bool) : ℝ := if value = sign then 0 else 1

theorem literalFactor_nonneg (sign value : Bool) : 0 ≤ literalFactor sign value := by
  unfold literalFactor
  split <;> norm_num

theorem literalFactor_le_one (sign value : Bool) : literalFactor sign value ≤ 1 := by
  unfold literalFactor
  split <;> norm_num

theorem product_literalFactor (J s : Fin 3 → Bool) :
    (∏ l, literalFactor (J l) (s l)) = if ∀ l, s l ≠ J l then 1 else 0 := by
  classical
  split_ifs with h
  · apply Finset.prod_eq_one
    intro l _
    simp [literalFactor, h l]
  · obtain ⟨l, hl⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    simp only [not_not] at hl
    simp [literalFactor, hl]

noncomputable def satInteraction (β : ℝ) (J : Fin 3 → Bool) : Interaction 3 :=
  fun s => if ∀ l, s l ≠ J l then -β else 0

noncomputable def satSample (β : ℝ) (J : Fin 3 → Bool) : InteractionSample 3 :=
  (satInteraction β J, 1, Real.exp (-β) - 1, fun l => literalFactor (J l))

theorem satSample_factorization (β : ℝ) (J s : Fin 3 → Bool) :
    Real.exp ((satSample β J).1 s) =
      (satSample β J).2.1 *
        (1 + (satSample β J).2.2.1 * ∏ l, (satSample β J).2.2.2 l (s l)) := by
  simp only [satSample, satInteraction, product_literalFactor]
  split_ifs <;> simp

theorem satInteraction_norm_le {β : ℝ} (hβ : 0 ≤ β) (J : Fin 3 → Bool) :
    ‖satInteraction β J‖ ≤ β := by
  apply (pi_norm_le_iff_of_nonneg hβ).mpr
  intro s
  unfold satInteraction
  split <;> simp [Real.norm_eq_abs, abs_of_nonneg hβ, hβ]

theorem satSample_product_bound {β : ℝ} (hβ : 0 < β) (J s : Fin 3 → Bool) :
    |(satSample β J).2.2.1 * ∏ l, (satSample β J).2.2.2 l (s l)| < 1 := by
  have he : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-β)
  simp only [satSample, product_literalFactor]
  split_ifs
  · rw [mul_one, abs_of_neg (by linarith)]
    linarith
  · norm_num

noncomputable def signLaw : ProbabilityMeasure (Fin 3 → Bool) :=
  ⟨(PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure, inferInstance⟩

noncomputable def satModel (a : ℝ≥0) (β : ℝ) : Model 3 where
  alpha := a
  disorder := signLaw.map (satSample β)
  field := ⟨Measure.dirac 0, inferInstance⟩

theorem satModel_supported (a : ℝ≥0) (β : ℝ) :
    ∀ᵐ z ∂(satModel a β).disorder.toMeasure, ∃ J, satSample β J = z := by
  exact ae_map_mem_range (Set.finite_range _).measurableSet
    (measurable_of_countable _).aemeasurable

theorem satModel_interaction_integrable (a : ℝ≥0) {β : ℝ} (hβ : 0 ≤ β) :
    Integrable (fun z : InteractionSample 3 => ‖z.1‖) (satModel a β).disorder.toMeasure := by
  apply Integrable.of_bound (by fun_prop) β
  filter_upwards [satModel_supported a β] with z hz
  obtain ⟨J, rfl⟩ := hz
  simpa only [norm_norm, satSample] using satInteraction_norm_le hβ J

theorem satModel_field_integrable (a : ℝ≥0) (β : ℝ) :
    Integrable (fun h : ℝ => |h|) (satModel a β).field.toMeasure := by
  change Integrable (fun h : ℝ => |h|) (Measure.dirac 0)
  exact integrable_dirac (by simp)

theorem signLaw_equiv (e : (Fin 3 → Bool) ≃ (Fin 3 → Bool)) :
    Measure.map e signLaw.toMeasure = signLaw.toMeasure := by
  apply Measure.ext_of_singleton
  intro J
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton J)]
  have he : e ⁻¹' {J} = {e.symm J} := by
    ext K
    change e K = J ↔ K = e.symm J
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      simpa using congrArg e h
  rw [he]
  change (PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure {e.symm J} =
    (PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure {J}
  rw [PMF.toMeasure_apply_singleton, PMF.toMeasure_apply_singleton] <;> simp

def permuteSigns (e : Equiv.Perm (Fin 3)) : (Fin 3 → Bool) ≃ (Fin 3 → Bool) where
  toFun J := fun l => J (e.symm l)
  invFun J := fun l => J (e l)
  left_inv J := by funext l; simp
  right_inv J := by funext l; simp

theorem satInteraction_permute (β : ℝ) (e : Equiv.Perm (Fin 3)) (J s : Fin 3 → Bool) :
    satInteraction β J (fun l => s (e l)) =
      satInteraction β (permuteSigns e J) s := by
  have h : (∀ l, s (e l) ≠ J l) ↔ ∀ l, s l ≠ J (e.symm l) := by
    constructor
    · intro h l
      simpa using h (e.symm l)
    · intro h l
      simpa using h (e l)
  simp only [satInteraction, permuteSigns, Equiv.coe_fn_mk]
  exact if_congr h rfl rfl

theorem satModel_symmetric (a : ℝ≥0) (β : ℝ) (e : Equiv.Perm (Fin 3)) :
    IdentDistrib (fun z : InteractionSample 3 => z.1)
      (fun z : InteractionSample 3 => fun s : Fin 3 → Spin => z.1 (fun l => s (e l)))
      (satModel a β).disorder.toMeasure (satModel a β).disorder.toMeasure := by
  constructor
  · exact measurable_fst.aemeasurable
  · exact (show Measurable (fun z : InteractionSample 3 => fun s : Fin 3 → Spin =>
        z.1 (fun l => s (e l))) by fun_prop).aemeasurable
  · change Measure.map _ (Measure.map (satSample β) signLaw.toMeasure) =
      Measure.map _ (Measure.map (satSample β) signLaw.toMeasure)
    rw [Measure.map_map measurable_fst (measurable_of_countable _),
      Measure.map_map (show Measurable (fun z : InteractionSample 3 => fun s : Fin 3 → Spin =>
        z.1 (fun l => s (e l))) by fun_prop) (measurable_of_countable _)]
    change Measure.map (satInteraction β) signLaw.toMeasure =
      Measure.map (fun J => fun s => satInteraction β J (fun l => s (e l))) signLaw.toMeasure
    simp_rw [satInteraction_permute]
    change Measure.map (satInteraction β) signLaw.toMeasure =
      Measure.map (satInteraction β ∘ permuteSigns e) signLaw.toMeasure
    rw [← Measure.map_map (measurable_of_countable (satInteraction β))
      (measurable_of_countable (permuteSigns e)), signLaw_equiv]

end FixedClauseThreshold.Computability

end OAI
