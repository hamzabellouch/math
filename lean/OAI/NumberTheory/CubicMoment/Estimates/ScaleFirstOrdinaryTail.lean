import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstOrdinaryStoppedTail
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailLowDecomposition
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstNoStopTailNegligible

namespace OAI

/-! The actual ordinary-height low distinguished-scale contribution is
negligible, by the exact no-stop and two-stage stopped decomposition. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstOrdinaryLowArity (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(69/200:ℝ) then
          scaleFirstTailScaleRow i 0 ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def scaleFirstOrdinaryLowTail (m : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, scaleFirstOrdinaryLowArity i ξ H T X

lemma scaleFirstOrdinaryLowArity_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ (H T : ℝ) (h : ℕ),
      scaleFirstOrdinaryLowArity i ξ H T X =
        scaleFirstOrdinaryNoStopArity i ρ ξ H T X h+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h true+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h false := by
  filter_upwards [scaleFirstTailScaleRow_two_stage i ξ] with X hrow
  intro ρ hρ hρ₂ H T h
  unfold scaleFirstOrdinaryLowArity scaleFirstOrdinaryNoStopArity
    scaleFirstOrdinaryStoppedArity scaleFirstStoppedWindow
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : T*(3/2:ℝ)^s ≤ X^(1/100:ℝ)
  · simp only [hs,ite_true]
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : distinguishedScaleLength d < X^(69/200:ℝ)
    · simp only [hd,ite_true]
      exact hrow ρ hρ hρ₂ 0 H (T*(3/2:ℝ)^s) h d hd
    · simp only [hd,ite_false,zero_add]
  · simp only [hs,ite_false,zero_add]

lemma scaleFirstOrdinaryLowTail_two_stage (m : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ (H T : ℝ) (h : ℕ),
      scaleFirstOrdinaryLowTail m ξ H T X = scaleFirstOrdinaryNoStopTail m ρ ξ H T X h+
        (∑ i ∈ Finset.range m, scaleFirstOrdinaryStoppedArity i ρ ξ H T X h true)+
        (∑ i ∈ Finset.range m, scaleFirstOrdinaryStoppedArity i ρ ξ H T X h false) := by
  have hall : ∀ᶠ X : ℝ in atTop, ∀ i ∈ Finset.range m,
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ (H T : ℝ) (h : ℕ),
      scaleFirstOrdinaryLowArity i ξ H T X =
        scaleFirstOrdinaryNoStopArity i ρ ξ H T X h+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h true+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h false := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => scaleFirstOrdinaryLowArity_two_stage i ξ
  filter_upwards [hall] with X hr
  intro ρ hρ hρ₂ H T h
  unfold scaleFirstOrdinaryLowTail scaleFirstOrdinaryNoStopTail
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => hr i hi ρ hρ hρ₂ H T h)

theorem scaleFirstOrdinaryLowTail_isLittleO (m : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hξ : 0 < ξ) (hξsmall : ξ < 1/100) :
    ∃ Ct : ℕ, ∀ (H T : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X) →
      (fun X => scaleFirstOrdinaryLowTail m ξ (H X) (T X) X)
        =o[atTop] firstMomentScale := by
  let ε := (1/100-ξ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < 1/100 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨ρ,hρ,hρ₂,hsmall,hn⟩ := scaleFirstOrdinaryNoStopTail_isLittleO
    m hpnt hVor hMV hC hcap
  obtain ⟨Ct,hs⟩ := scaleFirstOrdinaryStoppedTail_isLittleO m hpnt hMV hC hHuxley
    hξ (by linarith : ξ ≤ 2/5) hρ hρ₂ hε.le hsmall hgap
  refine ⟨Ct+1,?_⟩
  intro H T hT hH hHX
  have hT' : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X := by
    filter_upwards [hT,eventually_ge_atTop (1:ℝ)] with X ht hX
    exact (pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) (Nat.le_succ Ct)).trans ht
  have hsetup : ∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X ∧ Real.log X ≤ T X := by
    filter_upwards [hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X ht hH hHX hX
    have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
    exact ⟨hH,hHX,(by linarith : Real.log X ≤ 1+Real.log X).trans
      ((le_self_pow₀ hL (Nat.succ_ne_zero Ct)).trans ht)⟩
  let h : ℝ → ℕ := fun _ => 0
  have hsum := ((hn ξ H T h hsetup).add
    (hs H T h (fun _ => true) hT' hH hHX)).add
      (hs H T h (fun _ => false) hT' hH hHX)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [scaleFirstOrdinaryLowTail_two_stage m ξ] with X hid
  exact (hid ρ hρ hρ₂ (H X) (T X) (h X)).symm

end CubicFirstMoment

end

end OAI
