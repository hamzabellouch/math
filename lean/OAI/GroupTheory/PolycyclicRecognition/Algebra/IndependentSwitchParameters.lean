import OAI.GroupTheory.PolycyclicRecognition.Analysis.BackwardSwitchProbability

namespace OAI

/-! # The measurable event of successful independent switch parameters -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

universe u

/-- Two independent samples per switch, in their prescribed order. -/
abbrev SwitchParameters (G : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => G × G × SwitchParameters G k

instance switchParametersMeasurableSpace {G : Type*} [MeasurableSpace G] :
    (k : ℕ) → MeasurableSpace (SwitchParameters G k)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | k + 1 =>
    letI := switchParametersMeasurableSpace (G := G) k
    inferInstanceAs (MeasurableSpace (G × G × SwitchParameters G k))

variable {G : Type*} [Group G] [MeasurableSpace G]

def switchParameterLaw (σ : ℕ → Measure G) :
    (n k : ℕ) → Measure (SwitchParameters G k)
  | _, 0 => Measure.dirac PUnit.unit
  | n, k + 1 => (σ n).prod ((σ n).prod (switchParameterLaw σ (n + 1) k))

instance switchParameterLaw_isProbability (σ : ℕ → Measure G)
    [∀ j, IsProbabilityMeasure (σ j)] (n k : ℕ) :
    IsProbabilityMeasure (switchParameterLaw σ n k) := by
  induction k generalizing n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ k ih =>
    let := ih (n + 1)
    exact inferInstanceAs (IsProbabilityMeasure
      ((σ n).prod ((σ n).prod (switchParameterLaw σ (n + 1) k))))

/-- A parameter is successful precisely when every intermediate state
belongs to the next retained set. -/
def SwitchSuccessful (S : ℕ → Set G) :
    (n k : ℕ) → G → SwitchParameters G k → Prop
  | _, 0, _, _ => True
  | n, k + 1, x, p =>
    x * p.1 * p.2.1⁻¹ ∈ S (n + 1) ∧
      SwitchSuccessful S (n + 1) k (x * p.1 * p.2.1⁻¹) p.2.2

theorem measurableSet_switchSuccessful [MeasurableMul₂ G] [MeasurableInv G]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) :
    MeasurableSet {p : G × SwitchParameters G k | SwitchSuccessful S n k p.1 p.2} := by
  induction k generalizing n with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
    have hm : Measurable (fun p : G × SwitchParameters G (k + 1) =>
        p.1 * p.2.1 * p.2.2.1⁻¹) :=
      (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd.fst.inv
    exact (hS (n + 1) |>.preimage hm).inter
      ((ih (n + 1)).preimage (hm.prodMk measurable_snd.snd.snd))

theorem measurableSet_switchSuccessful_fixed [MeasurableMul₂ G] [MeasurableInv G]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) (x : G) :
    MeasurableSet {p : SwitchParameters G k | SwitchSuccessful S n k x p} :=
  (measurableSet_switchSuccessful S hS n k).preimage (measurable_const.prodMk measurable_id)

/-- The recursive survival integral equals the probability of the actual
measurable successful-parameter event under the independent product law. -/
theorem switchParameterLaw_success [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) (x : G) :
    switchParameterLaw σ n k {p | SwitchSuccessful S n k x p} =
      survivingSwitchProbability σ S n k x := by
  induction k generalizing n x with
  | zero =>
    change (Measure.dirac PUnit.unit) univ = 1
    exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  | succ k ih =>
    rw [← lintegral_indicator_one (measurableSet_switchSuccessful_fixed S hS n (k + 1) x)]
    let f : SwitchParameters G (k + 1) → ℝ≥0∞ :=
      {p | SwitchSuccessful S n (k + 1) x p}.indicator (fun _ => 1)
    have hf : Measurable f := measurable_const.indicator
      (measurableSet_switchSuccessful_fixed S hS n (k + 1) x)
    change (∫⁻ p, f p ∂(σ n).prod ((σ n).prod (switchParameterLaw σ (n + 1) k))) = _
    rw [lintegral_prod f hf.aemeasurable]
    change (∫⁻ s₁, ∫⁻ p, f (s₁, p) ∂(σ n).prod (switchParameterLaw σ (n + 1) k) ∂σ n) = _
    apply lintegral_congr
    intro s₁
    have hf₁ : Measurable (fun p : G × SwitchParameters G k => f (s₁, p)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod (fun p : G × SwitchParameters G k => f (s₁, p)) hf₁.aemeasurable]
    apply lintegral_congr
    intro s₂
    by_cases hy : x * s₁ * s₂⁻¹ ∈ S (n + 1)
    · have he : (fun p => f (s₁, s₂, p)) =
          {p | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p}.indicator (fun _ => 1) := by
        funext p
        change {q | SwitchSuccessful S n (k + 1) x q}.indicator (fun _ => (1 : ℝ≥0∞))
          (s₁, s₂, p) =
            {q | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}.indicator (fun _ => 1) p
        by_cases hp : SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p
        · rw [indicator_of_mem (s := {q : SwitchParameters G (k + 1) |
              SwitchSuccessful S n (k + 1) x q}) (show SwitchSuccessful S n (k + 1) x (s₁, s₂, p) from
            ⟨hy, hp⟩), indicator_of_mem (s := {q : SwitchParameters G k |
              SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}) hp]
        · have hn : ¬ SwitchSuccessful S n (k + 1) x (s₁, s₂, p) := fun h => hp h.2
          rw [indicator_of_notMem (s := {q : SwitchParameters G (k + 1) |
              SwitchSuccessful S n (k + 1) x q}) hn,
            indicator_of_notMem (s := {q : SwitchParameters G k |
              SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}) hp]
      rw [he]
      change (∫⁻ p, {p | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p}.indicator 1 p
        ∂switchParameterLaw σ (n + 1) k) = _
      rw [lintegral_indicator_one
        (measurableSet_switchSuccessful_fixed S hS (n + 1) k (x * s₁ * s₂⁻¹)), ih]
      exact (indicator_of_mem hy _).symm
    · have he : (fun p => f (s₁, s₂, p)) = fun _ => 0 := by
        funext p
        simp only [f, SwitchSuccessful, hy, false_and, mem_ofPred_eq,
          not_false_eq_true, indicator_of_notMem]
      rw [he, lintegral_zero]
      exact (indicator_of_notMem hy _).symm

end PolycyclicRecognition

end

end OAI
