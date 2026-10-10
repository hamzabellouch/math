import OAI.Probability.CriticalZ3.Basic

namespace OAI

universe uE uF uI

open MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
open MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

noncomputable def law (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.infinitePi (fun e => bernoulliMeasure true false (p e))

instance law_probability (p : E → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (law p) := by
  unfold law; infer_instance

noncomputable def finiteLaw (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) : Measure (J → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance finiteLaw_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (finiteLaw J p) := by unfold finiteLaw; infer_instance

theorem map_restrict (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).map J.restrict = finiteLaw J p := Measure.infinitePi_map_restrict _

theorem cylinder_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (J → Bool)) :
    law p (J.restrict ⁻¹' A) = finiteLaw J p A := by
  rw [←map_restrict,Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite A).measurableSet]

theorem cylinder_integral (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (f : (J → Bool) → ℝ) :
    (∫ ω, f (J.restrict ω) ∂law p) = ∫ ξ,f ξ ∂finiteLaw J p := by
  rw [←map_restrict]
  exact (integral_map (Finset.measurable_restrict _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

noncomputable def extend (J : Finset E) (ξ : J → Bool) : E → Bool :=
  fun e => if h : e ∈ J then ξ ⟨e,h⟩ else false

def DeterminedBy (J : Finset E) (f : (E → Bool) → F) : Prop :=
  ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω

theorem determinedBy_eq_extend {J : Finset E} {f : (E → Bool) → F}
    (hf : DeterminedBy J f) (ω : E → Bool) : f ω = f (extend J (J.restrict ω)) := by
  apply hf
  intro e he
  simp [extend,he,Finset.restrict]

theorem probability_determined (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    law p A = finiteLaw J p {ξ | extend J ξ ∈ A} := by
  rw [←cylinder_probability]
  congr 1
  ext ω
  exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])

theorem measurableSet_determined (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : MeasurableSet A := by
  have he : A = J.restrict ⁻¹' {ξ | extend J ξ ∈ A} := by
    ext ω
    exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

theorem map_reindex (e : E ≃ F) (p : F → Set.Icc (0 : ℝ) 1) :
    (law p).map (fun ω i => ω (e i)) = law (fun i => p (e i)) := by
  have h := Measure.infinitePi_map_piCongrLeft
    (fun i => bernoulliMeasure true false (p (e i))) e.symm
  have he : ((MeasurableEquiv.piCongrLeft (fun _ : E => Bool) e.symm) : (F → Bool) → E → Bool) =
      fun ω i => ω (e i) := by
    funext ω i
    change Equiv.piCongrLeft (fun _ : E => Bool) e.symm ω i = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  simpa only [law,Equiv.apply_symm_apply,he] using h

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
open MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

noncomputable def law [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance law_probability [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (law p) := by unfold law; infer_instance

noncomputable def mean [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) (f : (E → Bool) → ℝ) : ℝ :=
  ∫ ω, f ω ∂law p

def extend (ω : E → Bool) (b : Bool) : Option E → Bool
  | none => b
  | some e => ω e

theorem extend_mono (b : Bool) : Monotone (fun ω : E → Bool => extend ω b) := by
  intro ω ω' h e
  cases e with
  | none => exact le_rfl
  | some e => exact h e

theorem extend_false_le_true (ω : E → Bool) : extend ω false ≤ extend ω true := by
  intro e
  cases e with
  | none => exact Bool.false_le _
  | some e => exact le_rfl

theorem mean_mono [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {f g : (E → Bool) → ℝ} (h : ∀ ω, f ω ≤ g ω) : mean p f ≤ mean p g :=
  integral_mono Integrable.of_finite Integrable.of_finite h

theorem mean_option [Fintype E] (p : Option E → Set.Icc (0 : ℝ) 1)
    (f : (Option E → Bool) → ℝ) :
    mean p f = (p none : ℝ) * mean (fun e => p (some e)) (fun ω => f (extend ω true)) +
      (1 - (p none : ℝ)) * mean (fun e => p (some e)) (fun ω => f (extend ω false)) := by
  unfold mean law
  rw [← Measure.pi_map_piOptionEquivProd (fun i => bernoulliMeasure true false (p i))]
  rw [integral_map (MeasurableEquiv.piOptionEquivProd (fun _ : Option E => Bool)).symm.measurable.aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [integral_prod _ Integrable.of_finite]
  have heq : ∀ ω b, (MeasurableEquiv.piOptionEquivProd (fun _ : Option E => Bool)).symm (ω,b) =
      extend ω b := by
    intro ω b
    funext e
    cases e <;> rfl
  simp_rw [heq,integral_bernoulliMeasure,smul_eq_mul]
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul, integral_const_mul]

theorem mean_equiv {F : Type uF} [Fintype E] [Fintype F] (e : E ≃ F)
    (p : F → Set.Icc (0 : ℝ) 1) (f : (F → Bool) → ℝ) :
    mean p f = mean (fun a => p (e a)) (fun ω => f (fun b => ω (e.symm b))) := by
  have h := (measurePreserving_piCongrLeft (fun b => bernoulliMeasure true false (p b)) e).integral_comp
    (MeasurableEquiv.piCongrLeft (fun _ : F => Bool) e).measurableEmbedding f
  have he : ∀ ω, (MeasurableEquiv.piCongrLeft (fun _ : F => Bool) e) ω =
      fun b => ω (e.symm b) := by
    intro ω
    funext b
    change Equiv.piCongrLeft (fun _ : F => Bool) e ω b = ω (e.symm b)
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  simpa only [mean,law,he,Function.comp_def] using h.symm

/-- Finite product positive association for arbitrary real increasing observables. -/
theorem increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
  have h : ∀ (E : Type u) [Fintype E], ∀ (p : E → Set.Icc (0 : ℝ) 1)
      (f g : (E → Bool) → ℝ), Monotone f → Monotone g →
      mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
    apply Fintype.induction_empty_option
    · intro E F _ e ih p f g hf hg
      let _ : Fintype E := Fintype.ofEquiv F e.symm
      simp only [mean_equiv e p]
      apply ih
      · intro ω ω' h
        exact hf (fun b => h (e.symm b))
      · intro ω ω' h
        exact hg (fun b => h (e.symm b))
    · intro p f g _ _
      have heq (f : (PEmpty.{u+1} → Bool) → ℝ) : f = fun _ => f (fun x => x.elim) := by
        funext ω
        exact congrArg f (Subsingleton.elim _ _)
      rw [heq f,heq g]
      simp [mean]
    · intro E _ ih p f g hf hg
      let p' := fun e => p (some e)
      let f₀ := fun ω => f (extend ω false)
      let f₁ := fun ω => f (extend ω true)
      let g₀ := fun ω => g (extend ω false)
      let g₁ := fun ω => g (extend ω true)
      have h₀ := ih p' f₀ g₀ (hf.comp (extend_mono false)) (hg.comp (extend_mono false))
      have h₁ := ih p' f₁ g₁ (hf.comp (extend_mono true)) (hg.comp (extend_mono true))
      have hfm : mean p' f₀ ≤ mean p' f₁ := mean_mono p' (fun ω => hf (extend_false_le_true ω))
      have hgm : mean p' g₀ ≤ mean p' g₁ := mean_mono p' (fun ω => hg (extend_false_le_true ω))
      have hq0 : 0 ≤ (p none : ℝ) := (p none).2.1
      have hq1 : 0 ≤ 1 - (p none : ℝ) := sub_nonneg.mpr (p none).2.2
      have hc : 0 ≤ (p none : ℝ) * (1 - (p none : ℝ)) *
          (mean p' f₁ - mean p' f₀) * (mean p' g₁ - mean p' g₀) := by positivity
      have hsum := add_le_add (mul_le_mul_of_nonneg_left h₁ hq0) (mul_le_mul_of_nonneg_left h₀ hq1)
      simp only [mean_option]
      change ((p none : ℝ) * mean p' f₁ + (1 - (p none : ℝ)) * mean p' f₀) *
        ((p none : ℝ) * mean p' g₁ + (1 - (p none : ℝ)) * mean p' g₀) ≤
        (p none : ℝ) * mean p' (fun ω => f₁ ω * g₁ ω) +
        (1 - (p none : ℝ)) * mean p' (fun ω => f₀ ω * g₀ ω)
      nlinarith
  exact h E p f g hf hg

/-- Harris association also holds for decreasing observables. -/
theorem decreasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Antitone f) (hg : Antitone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
  have h := increasing p (fun ω => -f ω) (fun ω => -g ω) hf.neg hg.neg
  simpa only [mean,integral_neg,neg_mul_neg] using h

noncomputable def prob [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : ℝ := mean p (fun ω => if P ω then 1 else 0)

theorem prob_nonneg [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : 0 ≤ prob p P := integral_nonneg (by intro ω; dsimp; split_ifs <;> norm_num)

theorem prob_eq_real [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : prob p P = (law p).real {ω | P ω} := by
  simpa [prob,mean,Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

theorem indicator_antitone {P : (E → Bool) → Prop} (hP : Antitone P) :
    Antitone (fun ω => if P ω then (1 : ℝ) else 0) := by
  intro ω ω' h
  by_cases h' : P ω'
  · simp [h',hP h h']
  · simp only [h',ite_false]
    split_ifs <;> norm_num

theorem prob_and [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {P Q : (E → Bool) → Prop} (hP : Antitone P) (hQ : Antitone Q) :
    prob p P * prob p Q ≤ prob p (fun ω => P ω ∧ Q ω) := by
  have h := decreasing p _ _ (indicator_antitone hP) (indicator_antitone hQ)
  change mean p _ * mean p _ ≤ mean p _
  convert h using 1
  congr 1
  funext ω
  by_cases h₁ : P ω <;> by_cases h₂ : Q ω <;> simp [h₁,h₂]

/-- The finite-family decreasing-event Harris inequality used for 24 quarter-faces. -/
theorem prob_forall [Fintype E] {I : Type uI} (p : E → Set.Icc (0 : ℝ) 1)
    (s : Finset I) (P : I → (E → Bool) → Prop) (hP : ∀ i ∈ s, Antitone (P i)) :
    (∏ i ∈ s, prob p (P i)) ≤ prob p (fun ω => ∀ i ∈ s, P i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob,mean]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hs : ∀ j ∈ s, Antitone (P j) := fun j hj => hP j (Finset.mem_insert_of_mem hj)
    have h := mul_le_mul_of_nonneg_left (ih hs) (prob_nonneg p (P i))
    refine h.trans ?_
    have hh := prob_and p (hP i (Finset.mem_insert_self i s))
      (fun ω ω' h h' j hj => hs j hj h (h' j hj))
    simpa only [Finset.mem_insert,forall_eq_or_imp] using hh

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

theorem extend_mono (J : Finset E) : Monotone (extend J) := by
  intro ξ ζ h e
  by_cases he : e ∈ J
  · simp only [extend, dite_eq_left he]
    exact h ⟨e,he⟩
  · simp only [extend, dite_eq_right he, le_refl]

/-- Harris's finite-family inequality, applied to actual infinite-product cylinder events. -/
theorem decreasing_forall {I : Type uI} [Fintype I] (J : Finset E)
    (p : E → Set.Icc (0 : ℝ) 1) (A : I → Set (E → Bool))
    (hA : ∀ i ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A i ↔ ω ∈ A i))
    (hmono : ∀ i, Antitone (fun ω => ω ∈ A i)) :
    (∏ i, (law p).real (A i)) ≤ (law p).real (⋂ i, A i) := by
  have he (i : I) : (law p).real (A i) =
      FiniteAssociation.prob (fun e : J => p e) (fun ξ => extend J ξ ∈ A i) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def,
      probability_determined J p (A i) (hA i)]
    rfl
  have hall : (law p).real (⋂ i, A i) =
      FiniteAssociation.prob (fun e : J => p e) (fun ξ => ∀ i, extend J ξ ∈ A i) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def]
    have hd : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ ⋂ i, A i ↔ ω ∈ ⋂ i, A i) := by
      intro ω ω' h
      simp only [Set.mem_iInter]
      exact forall_congr' (fun i => hA i ω ω' h)
    rw [probability_determined J p (⋂ i,A i) hd]
    simp only [Set.mem_iInter]
    rfl
  rw [hall]
  simp_rw [he]
  simpa only [Finset.mem_univ,forall_true_left] using
    FiniteAssociation.prob_forall (fun e : J => p e) Finset.univ
      (fun i ξ => extend J ξ ∈ A i) (fun i _ => (hmono i).comp_monotone (extend_mono J))

/-- The finite law is a polynomial in its bit parameters. -/
theorem finite_mass (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) (ξ : J → Bool) :
    (finiteLaw J p).real {ξ} = ∏ e : J, if ξ e = true then (p e : ℝ) else 1-(p e : ℝ) := by
  rw [Measure.real_def,finiteLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {ξ e} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases ξ e <;> simp [unitInterval.coe_symm_eq]

theorem continuous_probability (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    Continuous (fun p : E → Set.Icc (0 : ℝ) 1 => (law p).real A) := by
  have he (p : E → Set.Icc (0 : ℝ) 1) : (law p).real A =
      ∑ ξ : J → Bool, (∏ e : J, if ξ e then (p e : ℝ) else 1-(p e : ℝ)) *
        (if extend J ξ ∈ A then 1 else 0) := by
    rw [Measure.real_def,probability_determined J p A hA]
    change (finiteLaw J p).real {ξ | extend J ξ ∈ A} = _
    rw [←integral_indicator_one (Set.toFinite _).measurableSet]
    rw [integral_fintype (Integrable.of_finite)]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [finite_mass]
    simp [Set.indicator,smul_eq_mul]
  simp_rw [he]
  apply continuous_finsetSum
  intro ξ _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  cases ξ e
  · exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply e.val))
  · exact continuous_subtype_val.comp (continuous_apply e.val)

end ProductCylinder

end OAI
