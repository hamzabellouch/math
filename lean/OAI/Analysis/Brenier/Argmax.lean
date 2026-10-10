import OAI.Analysis.Brenier.AffineTies

namespace OAI

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Problem358

/-- A finite nonempty family of measurable scores has a measurable maximizing
index. The maximizing score is measurable as well; no measurability assumption
on individual index singletons is needed. -/
theorem exists_measurable_finset_argmax {X ι : Type*}
    [MeasurableSpace X] [MeasurableSpace ι]
    (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) :
    ∀ (s : Finset ι), s.Nonempty →
      ∃ g : X → ι, Measurable g ∧ (∀ x, g x ∈ s) ∧
        Measurable (fun x => f (g x) x) ∧
        ∀ x i, i ∈ s → f i x ≤ f (g x) x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
      intro hs
      by_cases hsn : s.Nonempty
      · obtain ⟨g, hg, hgm, hfg, hmax⟩ := ih hsn
        let p : X → Prop := fun x => f (g x) x ≤ f a x
        let k : X → ι := fun x => if p x then a else g x
        have hp : MeasurableSet {x | p x} := measurableSet_le hfg (hf a)
        have hk : Measurable k := Measurable.ite hp measurable_const hg
        have hfk : Measurable (fun x => f (k x) x) := by
          have hval : (fun x => f (k x) x) =
              (fun x => if p x then f a x else f (g x) x) := by
            funext x
            simp only [k]
            split_ifs <;> rfl
          rw [hval]
          exact Measurable.ite hp (hf a) hfg
        refine ⟨k, hk, ?_, hfk, ?_⟩
        · intro x
          dsimp [k]
          split_ifs
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hgm x)
        · intro x i hi
          dsimp [k]
          split_ifs with hx
          · rcases Finset.mem_insert.mp hi with rfl | hi
            · exact le_rfl
            · exact (hmax x i hi).trans hx
          · rcases Finset.mem_insert.mp hi with rfl | hi
            · exact (lt_of_not_ge hx).le
            · exact hmax x i hi
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        refine ⟨fun _ => a, measurable_const, ?_, hf a, ?_⟩
        · intro x
          simp
        · intro x i hi
          have hia : i = a := by simpa using hi
          subst i
          exact le_rfl

/-- A measurable choice of an index maximizing a finite measurable family. -/
theorem exists_measurable_argmax {X ι : Type*}
    [MeasurableSpace X] [MeasurableSpace ι] [Fintype ι] [Nonempty ι]
    (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) :
    ∃ g : X → ι, Measurable g ∧ Measurable (fun x => f (g x) x) ∧
      ∀ x i, f i x ≤ f (g x) x := by
  classical
  obtain ⟨g, hg, _, hfg, hmax⟩ :=
    exists_measurable_finset_argmax f hf Finset.univ Finset.univ_nonempty
  exact ⟨g, hg, hfg, fun x i => hmax x i (Finset.mem_univ i)⟩

/-- Finite affine maxima have a globally measurable maximizing-slope map,
including on their tie sets. -/
theorem exists_measurable_affine_maximizer {V ι : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [Fintype ι] [Nonempty ι] (y : ι → V) (c : ι → ℝ) :
    ∃ T : V → V, Measurable T ∧ ∀ x, ∃ i,
      T x = y i ∧ ∀ j, ⟪y j, x⟫_ℝ + c j ≤ ⟪y i, x⟫_ℝ + c i := by
  classical
  let : MeasurableSpace ι := ⊤
  have hf (i : ι) : Measurable (fun x : V => ⟪y i, x⟫_ℝ + c i) := by
    fun_prop
  obtain ⟨g, hg, _, hmax⟩ := exists_measurable_argmax
    (fun i x => ⟪y i, x⟫_ℝ + c i) hf
  have hy : Measurable y := Measurable.of_discrete
  exact ⟨fun x => y (g x), hy.comp hg, fun x => ⟨g x, rfl, hmax x⟩⟩

end Problem358

end

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- The law of a finite choice of prescribed values is determined by the choice-cell masses. -/
lemma map_finite_selector {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    [MeasurableSingletonClass β] (ρ : Measure α) (s : α → ι)
    (hs : Measurable s) (y : ι → β) :
    Measure.map (fun x => y (s x)) ρ = ∑ i, ρ (s ⁻¹' {i}) • Measure.dirac (y i) := by
  have hy : Measurable y := measurable_of_countable y
  change Measure.map (y ∘ s) ρ = _
  rw [← Measure.map_map hy hs, Measure.map_eq_sum ρ s hs, Measure.sum_fintype,
    Measure.map_finset_sum hy.aemeasurable]
  simp only [Measure.map_smul _ hy.aemeasurable, Measure.map_dirac]

/-- A version of `map_finite_selector` using supplied cell masses. -/
lemma map_finite_selector_of_masses {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    [MeasurableSingletonClass β] (ρ : Measure α) (s : α → ι)
    (hs : Measurable s) (y : ι → β) (w : ι → ℝ≥0∞)
    (hw : ∀ i, ρ (s ⁻¹' {i}) = w i) :
    Measure.map (fun x => y (s x)) ρ = ∑ i, w i • Measure.dirac (y i) := by
  rw [map_finite_selector ρ s hs y]
  simp_rw [hw]

end Problem358

end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358.ParameterizedArgmax

/-- Off the tie set, maximizing selectors are independent of every choice. -/
theorem ae_eq_of_maximizers
    {X ι : Type*} [MeasurableSpace X] (ρ : Measure X)
    (f : ι → X → ℝ) (k l : X → ι)
    (hsep : ∀ᵐ x ∂ρ, Function.Injective (fun i => f i x))
    (hk : ∀ᵐ x ∂ρ, ∀ i, f i x ≤ f (k x) x)
    (hl : ∀ᵐ x ∂ρ, ∀ i, f i x ≤ f (l x) x) : k =ᵐ[ρ] l := by
  filter_upwards [hsep, hk, hl] with x hsep hk hl
  exact hsep (le_antisymm (hl (k x)) (hk (l x)))

/-- Any pointwise family of prescribed-mass maximizing selectors can be replaced
by one jointly measurable selector. Null ties preserve every mass exactly; no
measurability of the original family of choices is assumed. -/
theorem exists_joint_measurable_argmax_with_masses
    {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]
    [MeasurableSpace ι] [Fintype ι] [Nonempty ι]
    (ρ : P → Measure X) (f : ι → P × X → ℝ) (m : P → ι → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hsep : ∀ p, ∀ᵐ x ∂ρ p, Function.Injective (fun i => f i (p, x)))
    (hex : ∀ p, ∃ k : X → ι,
      (∀ᵐ x ∂ρ p, ∀ i, f i (p, x) ≤ f (k x) (p, x)) ∧
      ∀ i, (ρ p).real {x | k x = i} = m p i) :
    ∃ k : P × X → ι, Measurable k ∧
      (∀ p x i, f i (p, x) ≤ f (k (p, x)) (p, x)) ∧
      ∀ p i, (ρ p).real {x | k (p, x) = i} = m p i := by
  obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax f hf
  refine ⟨k, hk, fun p x i => hmax (p, x) i, ?_⟩
  intro p i
  obtain ⟨l, hl, hmass⟩ := hex p
  have heq : (fun x => k (p, x)) =ᵐ[ρ p] l :=
    ae_eq_of_maximizers (ρ p) (fun i x => f i (p, x)) (fun x => k (p, x)) l
      (hsep p) (Filter.Eventually.of_forall (fun x => hmax (p, x))) hl
  have hsets : {x | k (p, x) = i} =ᵐ[ρ p] {x | l x = i} := by
    filter_upwards [heq] with x hx
    exact congrArg (fun z => z = i) hx
  have hmeasure := measure_congr hsets
  calc
    (ρ p).real {x | k (p, x) = i} = (ρ p).real {x | l x = i} :=
      congrArg ENNReal.toReal hmeasure
    _ = m p i := hmass i

/-- Concrete affine version for the uniform source: joint measurability of the
sites/intercepts and injective sites discharge the score and null-tie premises. -/
theorem exists_joint_measurable_affine_argmax_with_masses
    {P ι : Type*} [MeasurableSpace P] [MeasurableSpace ι]
    [Fintype ι] [Nonempty ι] {d : ℕ} (K : Set (E d))
    (y : P → ι → E d) (c m : P → ι → ℝ)
    (hy : ∀ i, Measurable (fun p => y p i))
    (hc : ∀ i, Measurable (fun p => c p i))
    (hinj : ∀ p, Function.Injective (y p))
    (hex : ∀ p, ∃ k : E d → ι,
      (∀ᵐ x ∂uniformMeasure K, ∀ i,
        ⟪x, y p i⟫ + c p i ≤ ⟪x, y p (k x)⟫ + c p (k x)) ∧
      ∀ i, (uniformMeasure K).real {x | k x = i} = m p i) :
    ∃ k : P × E d → ι, Measurable k ∧
      (∀ p x i, ⟪x, y p i⟫ + c p i ≤
        ⟪x, y p (k (p, x))⟫ + c p (k (p, x))) ∧
      ∀ p i, (uniformMeasure K).real {x | k (p, x) = i} = m p i := by
  apply exists_joint_measurable_argmax_with_masses
    (fun _ => uniformMeasure K) (fun i p => ⟪p.2, y p.1 i⟫ + c p.1 i) m
  · intro i
    exact (measurable_snd.inner ((hy i).comp measurable_fst)).add
      ((hc i).comp measurable_fst)
  · intro p
    filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K (y p) (c p)] with x hx
    intro i j hij
    exact hinj p (hx i j hij)
  · exact hex

end Problem358.ParameterizedArgmax

end

end OAI
