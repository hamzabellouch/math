import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnergy
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBilinearMellin
import OAI.NumberTheory.CubicMoment.Estimates.GramMellinTwist

namespace OAI

/-! Exact full-line Mellin separation of the total-product envelope in a
finite height tail. No Mellin frequency is discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def envelopeCutoffBilinearTail (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (W : ℝ → ℂ) (H T X : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (heightWindowCount H T),
    ∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*W (norm (a*b)/X)*
      heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t)
        (Real.log (norm (a*b))-Real.log X)

theorem envelopeCutoffBilinearTail_mellin (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (H T : ℝ) {X : ℝ} (hX : 0 < X) :
    envelopeCutoffBilinearTail P S α β W H T X =
      ∫ τ : ℝ, zeroLineMellinWeight W X τ*
        cutoffBilinearTail P S (fun a => α a*normTwist (-τ) a)
          (fun b => β b*normTwist (-τ) b) H T X := by
  let c := fun j a b => α a*β b*gauss (a*b)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t)
      (Real.log (norm (a*b))-Real.log X)
  let f := fun j a b τ => zeroLineMellinWeight W X τ*
    (c j a b*mellinPhase (-τ) (norm (a*b)))
  have hn (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) (hb : b ∈ S) :
      0 < norm (a*b) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero (hP a ha)) (primary_ne_zero (hS b hb)))
  have hi (j : ℕ) (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) (hb : b ∈ S) :
      Integrable (f j a b) :=
    metaplectic_mellin_term_integrable W hW hpos hsm hX (hn a ha b hb) (c j a b)
  calc
    _ = ∑ j ∈ Finset.range (heightWindowCount H T),
        ∑ a ∈ P, ∑ b ∈ S, ∫ τ : ℝ, f j a b τ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have he := metaplectic_mellin_term W hW hpos hsm hX (hn a ha b hb) (c j a b)
      simpa only [c,f,mul_assoc,mul_left_comm,mul_comm] using he
    _ = ∫ τ : ℝ, ∑ j ∈ Finset.range (heightWindowCount H T),
        ∑ a ∈ P, ∑ b ∈ S, f j a b τ := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum P
        (fun a ha => integrable_finsetSum S (hi j a ha)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum P (fun a ha => integrable_finsetSum S (hi j a ha))]
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum S (hi j a ha)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [cutoffBilinearTail,cutoffBilinearWindow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [f,c]
      rw [←normTwist_eq_mellinPhase,normTwist_mul (-τ)
        (primary_ne_zero (hP a ha)) (primary_ne_zero (hS b hb))]
      ring

theorem envelopeCutoffBilinearTail_bound (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (H T : ℝ) {X M : ℝ} (hX : 0 < X) (_hM : 0 ≤ M)
    (hb : ∀ u : ℝ,
      ‖cutoffBilinearTail P S (fun a => α a*normTwist u a)
        (fun b => β b*normTwist u b) H T X‖ ≤ M) :
    ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤ zeroLineMellinMass W*M := by
  let F := fun τ : ℝ => cutoffBilinearTail P S (fun a => α a*normTwist (-τ) a)
    (fun b => β b*normTwist (-τ) b) H T X
  have hc : Continuous F := by
    unfold F cutoffBilinearTail cutoffBilinearWindow normTwist
    fun_prop
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hi : Integrable (fun τ => zeroLineMellinWeight W X τ*F τ) :=
    hw.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => hb (-τ)))
  rw [envelopeCutoffBilinearTail_mellin P S α β hP hS W hW hpos hsm H T hX]
  change ‖∫ τ : ℝ, zeroLineMellinWeight W X τ*F τ‖ ≤ _
  calc
    _ ≤ ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ*F τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖*M := by
      apply integral_mono_ae hi.norm (hw.norm.mul_const M)
      filter_upwards with τ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb (-τ)) (_root_.norm_nonneg _)
    _ = (∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖)*M := integral_mul_const _ _
    _ = _ := by rw [zeroLineMellinWeight_mass W hX]

end CubicFirstMoment

end

end OAI
