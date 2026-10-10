import OAI.NumberTheory.CubicMoment.Estimates.WideGramMellin
import OAI.NumberTheory.CubicMoment.Estimates.CoprimeMellinIntegral

namespace OAI

/-! Mellin separation of the actual coprime radial form on a fixed compact
norm range. The arithmetic rows are unchanged. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma wideGramMellinCoefficient_integrable_phases (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ x y : ℝ) :
    Integrable (fun t => wideGramMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t x *
      star (gramMellinPhase t y)) := by
  apply Integrable.mul_bdd (c := 1)
  · exact (wideGramMellinCoefficient_integrable M hM W hW hW' ρ).mul_bdd
      (gramMellinPhase_continuous x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_gramMellinPhase t x).le))
  · exact (gramMellinPhase_continuous y).star.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp)


theorem wideCoprimeRadialForm_mellin (M : ℝ) (hM : 0 < M) (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 0 < x h)
    (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coprimeRadialForm S H v w phase x y W ρ = ∫ t : ℝ,
      wideGramMellinCoefficient M hM W hW hW' ρ t * coprimeMellinKernel S H v w phase x y t := by
  let F (h a b : Eisenstein) (t : ℝ) : ℂ :=
    (phase h * (if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0)) *
      (wideGramMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t (x h) *
        star (gramMellinPhase t (y a*y b)))
  have hF (h a b : Eisenstein) : Integrable (F h a b) :=
    (wideGramMellinCoefficient_integrable_phases M hM W hW hW' ρ (x h) (y a*y b)).const_mul _
  have he (h : Eisenstein) (hh : h ∈ H) (a : Eisenstein) (ha : a ∈ S)
      (b : Eisenstein) (hb : b ∈ S) :
      phase h * (if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
          radialDualProfile W (ρ*x h/(y a*y b)) else 0) = ∫ t, F h a b t := by
    rw [show (∫ t, F h a b t) = _ from integral_const_mul _ _]
    rw [← wide_radial_mellin_separated M hM W hW hW' hρ (hx h hh)
      (mul_pos (hy a ha) (hy b hb)) (hlog h hh a ha b hb)]
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
      rw [gramMellinPhase_mul t (hy a ha)
        (hy b hb), star_mul]
      split_ifs <;> simp only [star_mul, mul_zero] <;> ring

theorem wideCoprimeRadialForm_norm_le_mass (M : ℝ) (hM : 0 < M) (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 0 < x h)
    (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
      ∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖*
        coprimeMellinMass S H U v w y t := by
  have hc := wideGramMellinCoefficient_integrable M hM W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase x y).aestronglyMeasurable
    (Eventually.of_forall (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y))
  have hm := hc.norm.mul_bdd
    (coprimeMellinMass_continuous S H U v w y).aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (coprimeMellinMass_nonneg S H U v w y t)]
      exact coprimeMellinMass_le_envelope S H U (fun a ha => (hS a ha).1) v w y t))
  rw [wideCoprimeRadialForm_mellin M hM S H v w phase x y hx hy hlog W hW hW' hρ]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hi.norm hm
  intro t
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_coprimeMellinKernel_le_mass S H U hS hU hSU v w phase hphase x y t)
    (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
