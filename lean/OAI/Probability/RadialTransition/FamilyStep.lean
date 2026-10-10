import OAI.Probability.RadialTransition.IdealAttainment

namespace OAI

universe uAlpha

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def prepend {α : Type uAlpha} (v : α) (f : ℕ → α) : ℕ → α := fun n => Nat.casesOn n v f

@[simp] lemma prepend_zero {α : Type uAlpha} (v : α) (f : ℕ → α) : prepend v f 0 = v := rfl
@[simp] lemma prepend_succ {α : Type uAlpha} (v : α) (f : ℕ → α) (n : ℕ) : prepend v f (n+1) = f n := rfl

lemma summable_prepend (v : ℝ) {f : ℕ → ℝ} (hf : Summable f) : Summable (prepend v f) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [prepend_succ] using hf

lemma tsum_prepend (v : ℝ) {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n, prepend v f n) = v+∑' n, f n := by
  simpa only [prepend_zero, prepend_succ] using (summable_prepend v hf).tsum_eq_zero_add

lemma prepend_nonneg {a : ℝ} {b : ℕ → ℝ} (ha : 0 ≤ a) (hb : ∀ n, 0 ≤ b n) :
    ∀ n, 0 ≤ prepend a b n := by
  intro n; cases n with
  | zero => exact ha
  | succ n => exact hb n

lemma prepend_range {R : ℝ} {S : ℕ → ℝ} (hR : 1 ≤ R) (hS : ∀ n, 1 ≤ S n) :
    ∀ n, 1 ≤ prepend R S n := by
  intro n; cases n with
  | zero => exact hR
  | succ n => exact hS n

lemma attractionProfile_prepend {a R : ℝ} {b S : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b) (r : ℝ) :
    attractionProfile (prepend a b) (prepend R S) r = a*scaledBumpProfile R r+attractionProfile b S r := by
  unfold attractionProfile
  have he : (fun n => prepend a b n*scaledBumpProfile (prepend R S n) r) =
      prepend (a*scaledBumpProfile R r) (fun n => b n*scaledBumpProfile (S n) r) := by
    funext n; cases n <;> rfl
  rw [he, tsum_prepend _ (summable_attractionProfile hb hS hs r)]

lemma familyPotential_prepend {a R t : ℝ} {b S : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b) :
    familyPotential t (prepend a b) (prepend R S) = familyPotential t b S+singleAttraction R (t*a) := by
  funext r
  simp only [familyPotential, Pi.add_apply, attractionProfile_prepend hb hS hs, singleAttraction]
  ring

lemma familyCellMajorant_prepend {a R t : ℝ} {b S : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b) (i j : Cell) :
    familyCellMajorant t (prepend a b) (prepend R S) i j =
      familyCellMajorant t b S i j+t*a*cellMajorant R bumpIntegral⁻¹ i j := by
  unfold familyCellMajorant
  have he : (fun n => prepend a b n * cellMajorant (prepend R S n) bumpIntegral⁻¹ i j) =
      prepend (a*cellMajorant R bumpIntegral⁻¹ i j) (fun n => b n*cellMajorant (S n) bumpIntegral⁻¹ i j) := by
    funext n; cases n <;> rfl
  rw [he, tsum_prepend _ (summable_cellMajorant hb hS hs i j)]
  ring

end RadialTransition
end

end OAI
