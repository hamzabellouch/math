import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Conditional

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ProbabilityTheory Classical

namespace Invariant233.CoordinateConditioning

variable {ι : Type*} {X Y : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem integral_finset_prod (S : Finset ι) (f : ∀ i, X i → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    ∫ x, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ =
      ∏ i ∈ S, ∫ x, f i x ∂μ i := by
  classical
  have he : (fun x : ∀ i, X i => ∏ i ∈ S, f i (x i)) =
      (fun z : ∀ i : S, X i => ∏ i : S, f i (z i)) ∘ S.restrict := by
    funext x
    simp only [Function.comp_apply, Finset.restrict]
    exact (S.prod_coe_sort (fun i => f i (x i))).symm
  rw [he]
  change (∫ x, (∏ i : S, f i (S.restrict x i)) ∂Measure.infinitePi μ) = _
  rw [MeasureTheory.integral_restrict_infinitePi μ (s := S)
    (f := fun z : ∀ i : S, X i => ∏ i : S, f i (z i))]
  · rw [integral_fintype_prod_eq_prod]
    exact S.prod_coe_sort (fun i => ∫ x, f i x ∂μ i)
  · exact (Finset.measurable_prod Finset.univ
      (fun (i : S) _ => (hf i).comp (measurable_pi_apply i))).aestronglyMeasurable

theorem integrable_finset_prod (S : Finset ι) (f : ∀ i, X i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, ‖f i x‖ ≤ 1) :
    Integrable (fun x : ∀ i, X i => ∏ i ∈ S, f i (x i)) (Measure.infinitePi μ) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (Finset.measurable_prod S
      (fun i _ => (hf i).comp (measurable_pi_apply i))).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hb i (x i))

private theorem prod_extend (S T : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ S ∪ T, (if i ∈ S then f i else 1) = ∏ i ∈ S, f i := by
  classical
  rw [Finset.prod_ite_mem]
  simp

omit [∀ i, MeasurableSpace (X i)] in

private theorem cylinder_indicator_prod (S T : Finset ι) (f : ∀ i, X i → ℝ)
    (B : ∀ i, Set (X i)) (x : ∀ i, X i) :
    ((T : Set ι).pi B).indicator (fun x => ∏ i ∈ S, f i (x i)) x =
      ∏ i ∈ S ∪ T,
        (if i ∈ T then (B i).indicator
          (fun z => if i ∈ S then f i z else 1) (x i)
         else if i ∈ S then f i (x i) else 1) := by
  classical
  by_cases hx : x ∈ (T : Set ι).pi B
  · rw [Set.indicator_of_mem hx]
    have hval : ∀ i ∈ S ∪ T,
        (if i ∈ T then (B i).indicator (fun z => if i ∈ S then f i z else 1) (x i)
          else if i ∈ S then f i (x i) else 1) = if i ∈ S then f i (x i) else 1 := by
      intro i hi
      by_cases hit : i ∈ T
      · rw [ite_eq_left hit, Set.indicator_of_mem (hx i hit)]
      · rw [ite_eq_right hit]
    rw [Finset.prod_congr rfl hval]
    exact (prod_extend S T (fun i => f i (x i))).symm
  · rw [Set.indicator_of_notMem hx]
    symm
    simp only [Set.mem_pi, Finset.mem_coe, not_forall] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_union_right S hi)
    rw [ite_eq_left hi, Set.indicator_of_notMem hxi]

theorem setIntegral_cylinder_prod_eq
    (S T : Finset ι) (A : ∀ i, X i → Y i)
    (hA : ∀ i, Measurable (A i))
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i))
    (hg : ∀ i, Measurable (g i))
    (hloc : ∀ i (B : Set (Y i)), MeasurableSet B →
      ∫ x in A i ⁻¹' B, g i x ∂μ i = ∫ x in A i ⁻¹' B, f i x ∂μ i)
    (B : ∀ i, Set (Y i)) (hB : ∀ i, MeasurableSet (B i)) :
    ∫ x in (fun x i => A i (x i)) ⁻¹' (T : Set ι).pi B,
        ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ =
      ∫ x in (fun x i => A i (x i)) ⁻¹' (T : Set ι).pi B,
        ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ := by
  classical
  have hp : (fun x i => A i (x i)) ⁻¹' (T : Set ι).pi B =
      (T : Set ι).pi (fun i => A i ⁻¹' B i) := rfl
  have hm : MeasurableSet ((T : Set ι).pi (fun i => A i ⁻¹' B i)) :=
    MeasurableSet.pi T.countable_toSet (fun i _ => hA i (hB i))
  rw [hp, ← integral_indicator hm, ← integral_indicator hm]
  simp_rw [cylinder_indicator_prod]
  let factors (F : ∀ i, X i → ℝ) : ∀ i, X i → ℝ := fun i z =>
    if i ∈ T then (A i ⁻¹' B i).indicator
      (fun z => if i ∈ S then F i z else 1) z
    else if i ∈ S then F i z else 1
  change (∫ x, ∏ i ∈ S ∪ T, factors g i (x i) ∂Measure.infinitePi μ) =
    (∫ x, ∏ i ∈ S ∪ T, factors f i (x i) ∂Measure.infinitePi μ)
  rw [integral_finset_prod μ (S ∪ T) (factors g),
    integral_finset_prod μ (S ∪ T) (factors f)]
  · apply Finset.prod_congr rfl
    intro i hi
    dsimp only [factors]
    by_cases hit : i ∈ T <;> by_cases his : i ∈ S
    · simp only [ite_eq_left hit, ite_eq_left his]
      rw [integral_indicator (hA i (hB i)), integral_indicator (hA i (hB i))]
      exact hloc i (B i) (hB i)
    · simp only [ite_eq_left hit, ite_eq_right his]
    · simp only [ite_eq_right hit, ite_eq_left his]
      simpa using hloc i Set.univ MeasurableSet.univ
    · simp only [ite_eq_right hit, ite_eq_right his]
  all_goals
    intro i
    have hset : MeasurableSet (A i ⁻¹' B i) := hA i (hB i)
    dsimp only [factors]
    split_ifs <;> fun_prop

theorem setIntegral_observed_prod_eq
    (S : Finset ι) (A : ∀ i, X i → Y i)
    (hA : ∀ i, Measurable (A i))
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i))
    (hg : ∀ i, Measurable (g i))
    (hfb : ∀ i x, ‖f i x‖ ≤ 1) (hgb : ∀ i x, ‖g i x‖ ≤ 1)
    (hloc : ∀ i (B : Set (Y i)), MeasurableSet B →
      ∫ x in A i ⁻¹' B, g i x ∂μ i = ∫ x in A i ⁻¹' B, f i x ∂μ i)
    (B : Set (∀ i, Y i)) (hB : MeasurableSet B) :
    ∫ x in (fun x i => A i (x i)) ⁻¹' B,
        ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ =
      ∫ x in (fun x i => A i (x i)) ⁻¹' B,
        ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ := by
  classical
  let obs : (∀ i, X i) → (∀ i, Y i) := fun x i => A i (x i)
  have hm : Measurable obs := Measurable.of_eval
    (fun i => (hA i).comp (measurable_pi_apply i))
  have hfi := integrable_finset_prod μ S f hf hfb
  have hgi := integrable_finset_prod μ S g hg hgb
  have htotal : (∫ x, ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ) =
      (∫ x, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ) := by
    rw [integral_finset_prod μ S g hg, integral_finset_prod μ S f hf]
    apply Finset.prod_congr rfl
    intro i hi
    simpa using hloc i Set.univ MeasurableSet.univ
  refine MeasurableSpace.induction_on_inter
    (C := fun D _ =>
      (∫ x in obs ⁻¹' D, ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ) =
        (∫ x in obs ⁻¹' D, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ))
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (fun _ => MeasurableSet.univ)) ?_ ?_ ?_ ?_ B hB
  · simp
  · rintro C ⟨T, D, hD, rfl⟩
    exact setIntegral_cylinder_prod_eq μ S T A hA f g hf hg hloc D
      (fun i => hD i (Set.mem_univ i))
  · intro C hC ih
    have heqg := integral_add_compl (hm hC) hgi
    have heqf := integral_add_compl (hm hC) hfi
    change (∫ x in obs ⁻¹' C, ∏ i ∈ S, g i (x i) ∂Measure.infinitePi μ) =
      (∫ x in obs ⁻¹' C, ∏ i ∈ S, f i (x i) ∂Measure.infinitePi μ) at ih
    rw [Set.preimage_compl]
    linarith
  · intro C hdisj hC ih
    rw [Set.preimage_iUnion,
      integral_iUnion (fun n => hm (hC n))
        (fun i j hij => (hdisj hij).preimage obs) hgi.integrableOn,
      integral_iUnion (fun n => hm (hC n))
        (fun i j hij => (hdisj hij).preimage obs) hfi.integrableOn]
    exact tsum_congr ih

theorem condExp_finset_prod
    (S : Finset ι) (A : ∀ i, X i → Y i)
    (hA : ∀ i, Measurable (A i))
    (f : ∀ i, X i → ℝ) (p : ∀ i, Y i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hp : ∀ i, Measurable (p i))
    (hfb : ∀ i x, ‖f i x‖ ≤ 1) (hpb : ∀ i y, ‖p i y‖ ≤ 1)
    (hloc : ∀ i (B : Set (Y i)), MeasurableSet B →
      ∫ x in A i ⁻¹' B, p i (A i x) ∂μ i = ∫ x in A i ⁻¹' B, f i x ∂μ i) :
    (Measure.infinitePi μ)[(fun x => ∏ i ∈ S, f i (x i)) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance] =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, p i (A i (x i))) := by
  classical
  let obs : (∀ i, X i) → (∀ i, Y i) := fun x i => A i (x i)
  have hm : Measurable obs := Measurable.of_eval
    (fun i => (hA i).comp (measurable_pi_apply i))
  have hpA : ∀ i, Measurable (fun x => p i (A i x)) := fun i => (hp i).comp (hA i)
  have hpAb : ∀ i x, ‖p i (A i x)‖ ≤ 1 := fun i x => hpb i (A i x)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm.comap_le
    (integrable_finset_prod μ S f hf hfb)
  · intro B hB hfin
    exact (integrable_finset_prod μ S _ hpA hpAb).integrableOn
  · intro B hB hfin
    obtain ⟨C, hC, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
    exact setIntegral_observed_prod_eq μ S A hA f _ hf hpA hfb hpAb hloc C hC
  · have hobs : @Measurable _ _ (MeasurableSpace.comap obs inferInstance) _ obs :=
      Measurable.of_comap_le le_rfl
    exact ((Finset.measurable_prod S (fun i _ =>
      (hp i).comp (measurable_pi_apply i))).comp hobs).aestronglyMeasurable

section Labels

variable {L : ι → Type*} [∀ i, MeasurableSpace (L i)]
  [∀ i, StandardBorelSpace (L i)] [∀ i, Nonempty (L i)]

theorem condExp_label_product
    (S : Finset ι) (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i))
    (C : ∀ i, Set (L i)) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.infinitePi μ)[(fun x => ∏ i ∈ S,
      (label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)) (x i)) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance] =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, (condDistrib (label i) (A i) (μ i) (A i (x i))).real (C i)) := by
  apply condExp_finset_prod μ S A hA
    (fun i => (label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)))
    (fun i y => (condDistrib (label i) (A i) (μ i) y).real (C i))
  · intro i
    exact measurable_const.indicator (hl i (hC i))
  · intro i
    exact (Kernel.measurable_coe _ (hC i)).ennreal_toReal
  · intro i x
    by_cases hx : label i x ∈ C i <;> simp [Set.indicator, hx]
  · intro i y
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  · intro i B hB
    have he := condDistrib_ae_eq_condExp (μ := μ i) (hA i) (hl i) (hC i)
    calc
      (∫ x in A i ⁻¹' B, (condDistrib (label i) (A i) (μ i) (A i x)).real (C i) ∂μ i) =
          ∫ x in A i ⁻¹' B,
            (μ i)[(label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)) |
              MeasurableSpace.comap (A i) inferInstance] x ∂μ i :=
        integral_congr_ae (ae_restrict_of_ae he)
      _ = _ := setIntegral_condExp (hA i).comap_le
        ((integrable_const (1 : ℝ)).indicator (hl i (hC i))) ⟨B, hB, rfl⟩

theorem condExp_label_inter
    (S : Finset ι) (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i))
    (C : ∀ i, Set (L i)) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.infinitePi μ)⟦(⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance⟧ =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, (condDistrib (label i) (A i) (μ i) (A i (x i))).real (C i)) := by
  have hind :
      (⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i).indicator
        (fun _ => (1 : ℝ)) =
      (fun x => ∏ i ∈ S, (label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)) (x i)) := by
    funext x
    simpa [Set.indicator, Finset.prod_apply] using
      (prod_indicator_apply S
        (fun i => (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i)
        (fun _ _ => (1 : ℝ)) x).symm
  change MeasureTheory.condExp _ (Measure.infinitePi μ) _ =ᵐ[Measure.infinitePi μ] _
  rw [hind]
  exact condExp_label_product μ S A hA label hl C hC

theorem iCondIndepFun_labels [Countable ι] [∀ i, StandardBorelSpace (X i)]
    (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i)) :
    iCondIndepFun
      (MeasurableSpace.comap (fun x i => A i (x i)) inferInstance)
      (Measurable.of_eval (fun i => (hA i).comp (measurable_pi_apply i))).comap_le
      (fun i x => label i (x i)) (Measure.infinitePi μ) := by
  classical
  apply (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (μ := Measure.infinitePi μ)
    (m' := MeasurableSpace.comap (fun x i => A i (x i)) inferInstance)
    (fun i => inferInstance) (fun i (x : ∀ i, X i) => label i (x i))
    (fun i => (hl i).comp (measurable_pi_apply i))).2
  intro S C hC
  let D : ∀ i, Set (L i) := fun i => if i ∈ S then C i else Set.univ
  have hD : ∀ i, MeasurableSet (D i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa [D, hi] using hC i hi
    · simp [D, hi]
  have hDC : ∀ i ∈ S, D i = C i := fun i hi => ite_eq_left hi
  have hsets : (⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i) =
      (⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' D i) := by
    apply Set.iInter₂_congr
    intro i hi
    rw [hDC i hi]
  rw [hsets]
  have hjoint := condExp_label_inter μ S A hA label hl D hD
  have hsingle : ∀ i ∈ S,
      (Measure.infinitePi μ)⟦(fun x : ∀ i, X i => label i (x i)) ⁻¹' C i |
        MeasurableSpace.comap (fun x i => A i (x i)) inferInstance⟧ =ᵐ[Measure.infinitePi μ]
        (fun x => (condDistrib (label i) (A i) (μ i) (A i (x i))).real (D i)) := by
    intro i hi
    simpa [hDC i hi] using condExp_label_inter μ {i} A hA label hl D hD
  have hall := (ae_ball_iff S.countable_toSet).2 hsingle
  filter_upwards [hjoint, hall] with x hx hallx
  rw [Finset.prod_apply, hx]
  exact Finset.prod_congr rfl (fun i hi => (hallx i hi).symm)

theorem condExp_label_inter_of_disintegration
    (S : Finset ι) (A : ∀ i, X i → Y i) (hA : ∀ i, Measurable (A i))
    (label : ∀ i, X i → L i) (hl : ∀ i, Measurable (label i))
    (κ : ∀ i, Kernel (Y i) (L i)) [∀ i, IsFiniteKernel (κ i)]
    (hκ : ∀ i, (μ i).map (fun x => (A i x, label i x)) = (μ i).map (A i) ⊗ₘ κ i)
    (C : ∀ i, Set (L i)) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.infinitePi μ)⟦(⋂ i ∈ S, (fun x : ∀ i, X i => label i (x i)) ⁻¹' C i) |
      MeasurableSpace.comap (fun x i => A i (x i)) inferInstance⟧ =ᵐ[Measure.infinitePi μ]
      (fun x => ∏ i ∈ S, (κ i (A i (x i))).real (C i)) := by
  refine (condExp_label_inter μ S A hA label hl C hC).trans ?_
  have hlocal (i : ι) : ∀ᵐ x ∂μ i,
      condDistrib (label i) (A i) (μ i) (A i x) = κ i (A i x) :=
    ae_of_ae_map (hA i).aemeasurable
      (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hA i) (hl i) (hκ i))
  have hglobal (i : ι) : ∀ᵐ x ∂Measure.infinitePi μ,
      condDistrib (label i) (A i) (μ i) (A i (x i)) = κ i (A i (x i)) :=
    (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae (hlocal i)
  filter_upwards [(ae_ball_iff S.countable_toSet).2 (fun i _ => hglobal i)] with x hx
  exact Finset.prod_congr rfl (fun i hi => congrArg (fun ν => ν.real (C i)) (hx i hi))

end Labels

end Invariant233.CoordinateConditioning

end

end OAI
