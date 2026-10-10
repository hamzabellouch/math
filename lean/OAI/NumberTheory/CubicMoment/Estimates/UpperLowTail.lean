import OAI.NumberTheory.CubicMoment.Estimates.UpperStoppedSuffix
import OAI.NumberTheory.CubicMoment.Estimates.UpperNoStopNegligible

namespace OAI

/-! The full low distinguished-scale branch at upper heights is negligible.
The single stopping identity is applied before either analytic bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def upperLowArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(1/3-2*κ) then
          scaleFirstTailScaleRow i 0 ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def upperLowTail (m : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, upperLowArity i κ ξ H T X

lemma upperLowArity_stopping (i : ℕ) (ξ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ H T : ℝ,
      upperLowArity i κ ξ H T X = upperNoStopArity i κ ρ ξ H T X+
        upperStoppedFilteredArity i κ ρ ξ H T X := by
  filter_upwards [scaleFirstTailScaleRow_upper_stopping i ξ hκ] with X hrow
  intro ρ hρ hρ₂ H T
  unfold upperLowArity upperNoStopArity upperStoppedFilteredArity upperStoppedWindow
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : X^(1/100:ℝ) < T*(3/2:ℝ)^s
  · simp only [hs,ite_true]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : distinguishedScaleLength d < X^(1/3-2*κ)
    · simp only [hd,ite_true]
      exact hrow ρ hρ hρ₂ 0 H (T*(3/2:ℝ)^s) d hd
    · simp only [hd,ite_false,zero_add]
  · simp only [hs,ite_false,zero_add]

lemma upperLowTail_stopping (m : ℕ) (ξ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ H T : ℝ,
      upperLowTail m κ ξ H T X = upperNoStopTail m κ ρ ξ H T X+
        ∑ i ∈ Finset.range m, upperStoppedFilteredArity i κ ρ ξ H T X := by
  have hall : ∀ᶠ X : ℝ in atTop, ∀ i ∈ Finset.range m,
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ H T : ℝ,
      upperLowArity i κ ξ H T X = upperNoStopArity i κ ρ ξ H T X+
        upperStoppedFilteredArity i κ ρ ξ H T X := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => upperLowArity_stopping i ξ hκ
  filter_upwards [hall] with X hr
  intro ρ hρ hρ₂ H T
  unfold upperLowTail upperNoStopTail
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => hr i hi ρ hρ hρ₂ H T)

theorem upperLowTail_isLittleO (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1/12 ∧ ∀ ξ : ℝ, 0 < ξ → ξ < κ/2 →
      ∀ m : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ κ/4 ∧ ∀ H T : ℝ → ℝ,
        (∀ᶠ X : ℝ in atTop, Real.log X ≤ T X) →
        (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
        (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+η/2)) →
        (fun X => upperLowTail m κ ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨κ,hκ,hκsmall,hstop⟩ := upperStoppedFilteredTail_isLittleO hpnt hMV hC hHuxley
  refine ⟨κ,hκ,hκsmall,?_⟩
  intro ξ _hξ hξsmall m
  let η := κ/8
  let ε := (κ/2-ξ)/2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηκ : η ≤ κ/4 := by dsimp [η]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < κ/2 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨ρ,hρ,hρ₂,hsmall,hno⟩ := upperNoStopTail_isLittleO m hpnt hVor hMV hC hκ hκsmall hη hηκ hcap
  refine ⟨η,hη,hηκ,?_⟩
  intro H T hT hH hHX
  have hsetup : ∀ᶠ X : ℝ in atTop,
      1 ≤ H X ∧ H X ≤ X^(1/6+η/2) ∧ Real.log X ≤ T X := by
    filter_upwards [hT,hH,hHX] with X ht hh hx
    exact ⟨hh,hx,ht⟩
  have hHhalf : ∀ᶠ X : ℝ in atTop, H X ≤ X^(1/2:ℝ) := by
    filter_upwards [hHX,eventually_ge_atTop (1:ℝ)] with X hx hX
    exact hx.trans (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [η]; linarith))
  have hsum := (hno ξ H T hsetup).add
    (hstop ρ ξ ε hρ hρ₂ hε.le hsmall hgap m H T hT hH hHhalf)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [upperLowTail_stopping m ξ hκ] with X hid
  exact (hid ρ hρ hρ₂ (H X) (T X)).symm

end CubicFirstMoment

end

end OAI
