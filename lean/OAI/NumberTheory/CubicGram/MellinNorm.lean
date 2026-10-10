import Mathlib
import OAI.NumberTheory.CubicGram.CubicOperator
import OAI.NumberTheory.CubicGram.MellinDecay

namespace OAI

/-! Mellin integral bounds for coprime radial forms. -/

section

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramMellinPhase_continuous (x : ℝ) : Continuous (fun t => gramMellinPhase t x) := by
  unfold gramMellinPhase
  fun_prop

lemma gramMellinPhase_mul (t : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    gramMellinPhase t (x*y) = gramMellinPhase t x * gramMellinPhase t y := by
  simp only [gramMellinPhase, Real.log_mul hx.ne' hy.ne', mul_add,
    AddChar.map_add_eq_mul, Circle.coe_mul]

lemma gramMellinCoefficient_integrable_phases (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ x y : ℝ) :
    Integrable (fun t => gramMellinCoefficient W hW hW' ρ t * gramMellinPhase t x *
      star (gramMellinPhase t y)) := by
  apply Integrable.mul_bdd (c := 1)
  · exact (gramMellinCoefficient_integrable W hW hW' ρ).mul_bdd
      (gramMellinPhase_continuous x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_gramMellinPhase t x).le))
  · exact (gramMellinPhase_continuous y).star.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp)

lemma thinDyad_mul {x y : ℝ} (hx : x ∈ Icc (1 : ℝ) (Real.sqrt 2))
    (hy : y ∈ Icc (1 : ℝ) (Real.sqrt 2)) : x*y ∈ Icc (1 : ℝ) 2 := by
  constructor
  · calc
      1 = 1*1 := by norm_num
      _ ≤ x*y := mul_le_mul hx.1 hy.1 (by norm_num) (by linarith [hx.1])
  · calc
      _ ≤ Real.sqrt 2 * Real.sqrt 2 :=
        mul_le_mul hx.2 hy.2 (by linarith [hy.1]) (Real.sqrt_nonneg _)
      _ = 2 := Real.mul_self_sqrt (by norm_num)

theorem radialDualProfile_twoRow_separated (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ρ x y z : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Icc (1 : ℝ) 2) (hy : y ∈ Icc (1 : ℝ) (Real.sqrt 2))
    (hz : z ∈ Icc (1 : ℝ) (Real.sqrt 2)) :
    radialDualProfile W (ρ*x/(y*z)) = ∫ t : ℝ,
      gramMellinCoefficient W hW hW' ρ t * gramMellinPhase t x *
        star (gramMellinPhase t y) * star (gramMellinPhase t z) := by
  rw [radialDualProfile_mellin_separated W hW hW' hρ hx (thinDyad_mul hy hz)]
  apply integral_congr_ae
  filter_upwards with t
  rw [gramMellinPhase_mul t (zero_lt_one.trans_le hy.1) (zero_lt_one.trans_le hz.1), star_mul]
  ring

def coprimeRadialForm (S H : Finset Eisenstein) (v w phase : Eisenstein → ℂ)
    (x y : Eisenstein → ℝ) (W : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∑ h ∈ H, phase h * ∑ a ∈ S, ∑ b ∈ S,
    if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
        radialDualProfile W (ρ*x h/(y a*y b)) else 0

def coprimeNormMajorant (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ) : ℝ :=
  ∑ s ∈ U.powerset,
    finiteCubicBound (S.filter (fun a => (∏ p ∈ s, p) ∣ a)) H *
      ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
       (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2

lemma coprimeNormMajorant_nonneg (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ) :
    0 ≤ coprimeNormMajorant S H U v w := by
  apply Finset.sum_nonneg
  intro s hs
  apply div_nonneg _ (by norm_num)
  exact mul_nonneg (finiteCubicBound_nonneg _ _) (add_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

lemma coprimeNormMajorant_phases (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) :
    coprimeNormMajorant S H U (fun a => v a * star (gramMellinPhase t (y a)))
      (fun a => w a * gramMellinPhase t (y a)) = coprimeNormMajorant S H U v w := by
  simp only [coprimeNormMajorant, norm_mul, norm_star, norm_gramMellinPhase, mul_one]

end CubicFirstMoment

namespace CubicFirstMoment

def coprimeMellinKernel (S H : Finset Eisenstein) (v w phase : Eisenstein → ℂ)
    (x y : Eisenstein → ℝ) (t : ℝ) : ℂ :=
  ∑ h ∈ H, (phase h * gramMellinPhase t (x h)) * ∑ a ∈ S, ∑ b ∈ S,
    if IsCoprime a b then
      (v a * star (gramMellinPhase t (y a)) * star (cubicSymbol a h)) *
        star (w b * gramMellinPhase t (y b) * star (cubicSymbol b h)) else 0

lemma coprimeMellinKernel_continuous (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ) :
    Continuous (coprimeMellinKernel S H v w phase x y) := by
  unfold coprimeMellinKernel
  apply continuous_finsetSum
  intro h hh
  apply Continuous.mul
  · exact continuous_const.mul (gramMellinPhase_continuous _)
  · apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    by_cases hab : IsCoprime a b
    · simp only [ite_eq_left hab]
      exact ((continuous_const.mul (gramMellinPhase_continuous _).star).mul
        continuous_const).mul
        (((continuous_const.mul (gramMellinPhase_continuous _)).mul continuous_const).star)
    · simp only [ite_eq_right hab]
      exact continuous_const

lemma norm_coprimeMellinKernel_le (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (t : ℝ) :
    ‖coprimeMellinKernel S H v w phase x y t‖ ≤ coprimeNormMajorant S H U v w := by
  have h := finiteCubicBound_coprime_bilinear S H U hS hU hSU
    (fun a => v a * star (gramMellinPhase t (y a)))
    (fun a => w a * gramMellinPhase t (y a))
    (fun h => phase h * gramMellinPhase t (x h)) (fun h hh => by
      simpa only [norm_mul, norm_gramMellinPhase, mul_one] using hphase h hh)
  change ‖coprimeMellinKernel S H v w phase x y t‖ ≤
    coprimeNormMajorant S H U _ _ at h
  rw [coprimeNormMajorant_phases] at h
  exact h

theorem coprimeRadialForm_mellin (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, x h ∈ Icc (1 : ℝ) 2)
    (hy : ∀ a ∈ S, y a ∈ Icc (1 : ℝ) (Real.sqrt 2))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coprimeRadialForm S H v w phase x y W ρ = ∫ t : ℝ,
      gramMellinCoefficient W hW hW' ρ t * coprimeMellinKernel S H v w phase x y t := by
  let F (h a b : Eisenstein) (t : ℝ) : ℂ :=
    (phase h * (if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0)) *
      (gramMellinCoefficient W hW hW' ρ t * gramMellinPhase t (x h) *
        star (gramMellinPhase t (y a*y b)))
  have hF (h a b : Eisenstein) : Integrable (F h a b) :=
    (gramMellinCoefficient_integrable_phases W hW hW' ρ (x h) (y a*y b)).const_mul _
  have he (h : Eisenstein) (hh : h ∈ H) (a : Eisenstein) (ha : a ∈ S)
      (b : Eisenstein) (hb : b ∈ S) :
      phase h * (if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
          radialDualProfile W (ρ*x h/(y a*y b)) else 0) = ∫ t, F h a b t := by
    rw [show (∫ t, F h a b t) = _ from integral_const_mul _ _]
    rw [← radialDualProfile_mellin_separated W hW hW' hρ (hx h hh)
      (thinDyad_mul (hy a ha) (hy b hb))]
    split_ifs <;> ring
  calc
    _ = ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, ∫ t, F h a b t := by
      unfold coprimeRadialForm
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_congr rfl (fun b hb => he h hh a ha b hb)
    _ = ∫ t, ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, F h a b t := by
      rw [integral_finsetSum H (fun h _ =>
        integrable_finsetSum S (fun a _ => integrable_finsetSum S (fun b _ => hF h a b)))]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_finsetSum S (fun a _ => integrable_finsetSum S (fun b _ => hF h a b))]
      exact Finset.sum_congr rfl (fun a _ => (integral_finsetSum S (fun b _ => hF h a b)).symm)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      unfold coprimeMellinKernel
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [F]
      rw [gramMellinPhase_mul t (zero_lt_one.trans_le (hy a ha).1)
        (zero_lt_one.trans_le (hy b hb).1), star_mul]
      split_ifs <;> simp only [star_mul, mul_zero] <;> ring

end CubicFirstMoment

namespace CubicFirstMoment

theorem coprimeRadialForm_norm_le (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, x h ∈ Icc (1 : ℝ) 2)
    (hy : ∀ a ∈ S, y a ∈ Icc (1 : ℝ) (Real.sqrt 2))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
      (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w := by
  have hc := gramMellinCoefficient_integrable W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase x y).aestronglyMeasurable
    (Eventually.of_forall
      (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y))
  rw [coprimeRadialForm_mellin S H v w phase x y hx hy W hW hW' hρ]
  calc
    _ ≤ ∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t *
        coprimeMellinKernel S H v w phase x y t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖ *
        coprimeNormMajorant S H U v w := by
      apply integral_mono hi.norm (hc.norm.mul_const _)
      intro t
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y t)
        (_root_.norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem coprimeRadialForm_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H U : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      (∀ p ∈ U, primaryPrime p) →
      (∀ a ∈ S, primaryPrimeFactors a ⊆ U) →
      ∀ (v w phase : Eisenstein → ℂ), (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      ∀ (x y : Eisenstein → ℝ),
      (∀ h ∈ H, x h ∈ Icc (1 : ℝ) 2) →
      (∀ a ∈ S, y a ∈ Icc (1 : ℝ) (Real.sqrt 2)) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
        C * coprimeNormMajorant S H U v w := by
  obtain ⟨C, hC, hc⟩ := gramMellinCoefficient_mass_rapidDecay W hW hW' A
  refine ⟨C, hC, ?_⟩
  intro S H U hS hU hSU v w phase hphase x y hx hy ρ hρ
  calc
    _ ≤ (1+ρ)^A * ((∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w) :=
      mul_le_mul_of_nonneg_left
        (coprimeRadialForm_norm_le S H U hS hU hSU v w phase hphase x y hx hy W hW hW' hρ)
        (by positivity)
    _ = ((1+ρ)^A * (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖)) *
        coprimeNormMajorant S H U v w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc ρ hρ) (coprimeNormMajorant_nonneg _ _ _ _ _)

end CubicFirstMoment
end
end

end OAI
