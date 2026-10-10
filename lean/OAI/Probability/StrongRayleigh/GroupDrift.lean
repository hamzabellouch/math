import OAI.Probability.StrongRayleigh.FiniteMarginalObservation
import OAI.Probability.StrongRayleigh.GroupExhaustion
import OAI.Probability.StrongRayleigh.LimsupDrift

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Problem336AdditiveD139

universe u

def groupDrift {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (t : ℝ) (y : Γ → ℝ) (i : Γ) : ℝ :=
  limsup (fun n : ℕ =>
    finiteObservationDrift μ i (translatedGroupExhaustion Γ i n) t y) atTop

theorem groupDrift_eq_finiteFieldMean_limsup
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (t : ℝ) (y : Γ → ℝ) (i : Γ) :
    groupDrift μ t y i = limsup (fun n : ℕ =>
      finiteFieldMean μ (translatedGroupExhaustion Γ i n) (fun j => y j - t / 2) i) atTop := by
  simp only [groupDrift, finiteObservationDrift_eq_finiteFieldMean]

theorem measurable_groupDrift
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) :
    Measurable (fun p : ℝ × (Γ → ℝ) => groupDrift μ p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  exact Measurable.limsup (fun n =>
    measurable_finiteObservationDrift μ i (translatedGroupExhaustion Γ i n))

theorem groupDrift_mem_Icc
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (t : ℝ) (y : Γ → ℝ) (i : Γ) :
    groupDrift μ t y i ∈ Set.Icc (0 : ℝ) 1 := by
  exact limsupDrift_mem_unitInterval (b := fun n (p : ℝ × (Γ → ℝ)) i =>
    finiteObservationDrift μ i (translatedGroupExhaustion Γ i n) p.1 p.2)
    (fun n p i => finiteObservationDrift_mem_Icc μ i _ p.1 p.2) (t, y) i

theorem groupDrift_response_of_finite_response
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : StronglyRayleighCountable μ)
    (t : ℝ) (y y' : Γ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hy : ∀ j, |y j - y' j| ≤ D) (i : Γ) :
    |groupDrift μ t y i - groupDrift μ t y' i| ≤ D / 2 := by
  apply abs_limsup_sub_limsup_le_of_unit_bounds
    (fun n => finiteObservationDrift_mem_Icc μ i _ t y)
    (fun n => finiteObservationDrift_mem_Icc μ i _ t y')
  intro n
  let S := translatedGroupExhaustion Γ i n
  let : Nonempty (insert i S : Finset Γ) := ⟨⟨i, Finset.mem_insert_self i S⟩⟩
  have hSR : StronglyRayleighFinite (finiteMarginal μ (insert i S)) := by
    intro z hz
    rw [finiteGeneratingValue_finiteMarginal]
    exact hμ (insert i S) z hz
  exact finiteObservationDrift_response_of_finite_response μ i S
    (hresponse ↥(insert i S : Finset Γ) (finiteMarginal μ (insert i S)) hSR
      ⟨i, Finset.mem_insert_self i S⟩) t y y' D hD hy

theorem groupDrift_translate
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g i : Γ) (t : ℝ) (y : Γ → ℝ) :
    groupDrift μ t (leftTranslate g y) (g * i) = groupDrift μ t y i := by
  unfold groupDrift
  apply limsup_congr
  apply Eventually.of_forall
  intro n
  rw [translatedGroupExhaustion_equivariant]
  exact finiteObservationDrift_translate μ hμ g i _ t y

theorem groupDrift_leftTranslate
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g : Γ) (t : ℝ) (y : Γ → ℝ) :
    groupDrift μ t (leftTranslate g y) = leftTranslate g (groupDrift μ t y) := by
  funext i
  simpa only [leftTranslate, mul_inv_cancel_left] using
    groupDrift_translate μ hμ g (g⁻¹ * i) t y

@[simp] theorem groupDrift_zero_zero
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (i : Γ) :
    groupDrift μ 0 (fun _ => 0) i =
      ∫ x, boolReal (x i) ∂(μ : Measure (Γ → Bool)) := by
  simp [groupDrift]

end Problem336AdditiveD139

end

end OAI
