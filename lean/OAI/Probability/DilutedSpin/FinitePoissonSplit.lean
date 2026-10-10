import OAI.Probability.DilutedSpin.CavityIndex
import OAI.Probability.DilutedSpin.UpperMoments

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

noncomputable def finiteUniform (A : Type*) [Fintype A] [Nonempty A]
    [MeasurableSpace A] : Measure A := (PMF.uniformOfFintype A).toMeasure
instance finiteUniform_prob (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] :
    IsProbabilityMeasure (finiteUniform A) := by unfold finiteUniform; infer_instance

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompleteSpace E] in
lemma centeredExp_integrable (V : X → E) (hV : Measurable V) (L : StrongDual ℝ E) :
    Integrable (fun x => Complex.exp ((L (V x):ℂ)*Complex.I)-1) μ := by
  have hi : Integrable (fun x => Complex.exp ((L (V x):ℂ)*Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  exact hi.sub (integrable_const _)

omit [CompleteSpace E] in
lemma centered_finite_mark {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (V : X×A → E) (hV : Measurable V) (L : StrongDual ℝ E) :
    charFunDual (Measure.map V (μ.prod (finiteUniform A))) L-1 =
      (Fintype.card A:ℂ)⁻¹ * ∑ a, ∫ x, Complex.exp ((L (V (x,a)):ℂ)*Complex.I)-1 ∂μ := by
  rw [charFunDual_centered_map _ V hV,integral_prod_symm _ (centeredExp_integrable _ V hV L),
    integral_finiteUniform]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]

/-- Exact splitting of a finite marked process, allowing marks outside two
 disjoint families to be replaced by zero. The rates retain their exact finite-size values. -/
lemma finite_poisson_split {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (eA : A → C) (eB : B → C) (good : C → Prop) [DecidablePred good]
    (hs : ∀ f : C → ℂ, (∑ c,if good c then f c else 0) = (∑ a,f (eA a))+(∑ b,f (eB b)))
    (V : X×C → E) (hV : Measurable V) (r : ℝ≥0) :
    compoundPoisson r (Measure.map (fun z : X×C => if good z.2 then V z else 0)
      (μ.prod (finiteUniform C))) =
      compoundPoisson (r*(Fintype.card A)/(Fintype.card C))
        (Measure.map (fun z : X×A => V (z.1,eA z.2)) (μ.prod (finiteUniform A))) ∗
      compoundPoisson (r*(Fintype.card B)/(Fintype.card C))
        (Measure.map (fun z : X×B => V (z.1,eB z.2)) (μ.prod (finiteUniform B))) := by
  have hm0 : Measurable (fun z : X×C => if good z.2 then V z else 0) :=
    hV.ite (((Set.to_countable {c | good c}).measurableSet).preimage measurable_snd) measurable_const
  have hmA : Measurable (fun z : X×A => V (z.1,eA z.2)) :=
    hV.comp (measurable_fst.prodMk ((measurable_of_countable eA).comp measurable_snd))
  have hmB : Measurable (fun z : X×B => V (z.1,eB z.2)) :=
    hV.comp (measurable_fst.prodMk ((measurable_of_countable eB).comp measurable_snd))
  let : IsProbabilityMeasure (Measure.map (fun z : X×C => if good z.2 then V z else 0)
      (μ.prod (finiteUniform C))) :=
    (Measure.isProbabilityMeasure_map_iff hm0.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (Measure.map (fun z : X×A => V (z.1,eA z.2))
      (μ.prod (finiteUniform A))) :=
    (Measure.isProbabilityMeasure_map_iff hmA.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (Measure.map (fun z : X×B => V (z.1,eB z.2))
      (μ.prod (finiteUniform B))) :=
    (Measure.isProbabilityMeasure_map_iff hmB.aemeasurable).mpr inferInstance
  apply compoundPoisson_superposition_centered
  intro L
  rw [centered_finite_mark μ _ hm0,centered_finite_mark μ _ hmA,centered_finite_mark μ _ hmB]
  have he (c : C) : (∫ x, Complex.exp ((L (if good c then V (x,c) else 0):ℂ)*Complex.I)-1 ∂μ) =
      if good c then (∫ x,Complex.exp ((L (V (x,c)):ℂ)*Complex.I)-1 ∂μ) else 0 := by
    split_ifs <;> simp
  simp only [he]
  rw [hs]
  have ha : (Fintype.card A:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card B:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card C:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp
  simp only [mul_comm Complex.I]

end DilutedSpinGlass

end

end OAI
