import OAI.NumberTheory.CubicMoment.Estimates.RoughMoebius
import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower

namespace OAI

/-! Literal independent coefficients from the stopping construction.
The selected-side test may contain the first-stage failure and crossing
conditions; the remaining-side test is a separate condition on its divisor.
No coprimality condition is inserted between the two sides. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryPairSupport (S T : Finset Eisenstein) : Finset Eisenstein :=
  (S ×ˢ T).image (fun p => p.1*p.2)

def primaryPairFiber (S T : Finset Eisenstein) (b : Eisenstein) :
    Finset (Eisenstein × Eisenstein) :=
  (S ×ˢ T).filter (fun p => p.1*p.2 = b)

def primaryPairCoefficient (S T : Finset Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  ∑ p ∈ primaryPairFiber S T b, w p

lemma primaryPairCoefficient_sum (S T : Finset Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) (F : Eisenstein → ℂ) :
    (∑ b ∈ primaryPairSupport S T, primaryPairCoefficient S T w b*F b) =
      ∑ p ∈ S ×ˢ T, w p*F (p.1*p.2) := by
  unfold primaryPairCoefficient primaryPairFiber
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b ∈ primaryPairSupport S T,
        ∑ p ∈ S ×ˢ T with p.1*p.2 = b, w p*F (p.1*p.2) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem _ hp) _

def stoppedBeta (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop)
    (b : Eisenstein) : ℂ :=
  primaryPairCoefficient R D
    (fun p => if selected p.1 p.2 then v p.1*cutoffMoebius ψ w p.2 else 0) b

def stoppedAlpha (E U : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
    (remaining : Eisenstein → Prop) (a : Eisenstein) : ℂ :=
  primaryPairCoefficient E U
    (fun p => if remaining p.1 then cutoffMoebius ψ w p.1 else 0) a

/-- Exact collection of the stopped divisors. The selected test depends
only on r,d and the remaining test only on e. -/
theorem stopped_coefficients_sum (R D E U : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (remaining : Eisenstein → Prop)
    (K : Eisenstein → ℂ) :
    (∑ a ∈ primaryPairSupport E U, ∑ b ∈ primaryPairSupport R D,
      stoppedAlpha E U ψ w remaining a*stoppedBeta R D v ψ w selected b*K (a*b)) =
    ∑ p ∈ E ×ˢ U, ∑ q ∈ R ×ˢ D,
      if remaining p.1 ∧ selected q.1 q.2 then
        cutoffMoebius ψ w p.1*v q.1*cutoffMoebius ψ w q.2*
          K ((p.1*p.2)*(q.1*q.2)) else 0 := by
  unfold stoppedAlpha stoppedBeta
  calc
    _ = ∑ a ∈ primaryPairSupport E U,
        primaryPairCoefficient E U
          (fun p => if remaining p.1 then cutoffMoebius ψ w p.1 else 0) a *
        ∑ b ∈ primaryPairSupport R D,
          primaryPairCoefficient R D
            (fun p => if selected p.1 p.2 then v p.1*cutoffMoebius ψ w p.2 else 0) b *
              K (a*b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := by
      rw [primaryPairCoefficient_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [primaryPairCoefficient_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hp' : remaining p.1 <;> by_cases hq' : selected q.1 q.2
      all_goals simp [hp',hq']
      ring

/-- Enlarging the independent sums adds only terms killed individually
by a kernel supported on squarefree products. -/
theorem stopped_coefficients_squarefree (R D E U : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (remaining : Eisenstein → Prop)
    (K : Eisenstein → ℂ) (hK : ∀ n, ¬Squarefree n → K n = 0) :
    (∑ a ∈ primaryPairSupport E U, ∑ b ∈ primaryPairSupport R D,
      stoppedAlpha E U ψ w remaining a*stoppedBeta R D v ψ w selected b*K (a*b)) =
    ∑ p ∈ E ×ˢ U, ∑ q ∈ R ×ˢ D,
      if remaining p.1 ∧ selected q.1 q.2 ∧ Squarefree ((p.1*p.2)*(q.1*q.2)) then
        cutoffMoebius ψ w p.1*v q.1*cutoffMoebius ψ w q.2*
          K ((p.1*p.2)*(q.1*q.2)) else 0 := by
  rw [stopped_coefficients_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hs : Squarefree ((p.1*p.2)*(q.1*q.2))
  · simp [hs]
  · simp [hs,hK _ hs]

lemma primaryPairFiber_card_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein) :
    (primaryPairFiber S T b).card ≤ (S.filter (fun r => r ∣ b)).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hm.1,⟨p.2,(Finset.mem_filter.mp hp).2.symm⟩⟩
  · intro p hp q hq he
    apply Prod.ext he
    have hmul : p.1*p.2 = p.1*q.2 := by
      calc
        _ = b := (Finset.mem_filter.mp hp).2
        _ = q.1*q.2 := (Finset.mem_filter.mp hq).2.symm
        _ = _ := by rw [he]
    exact mul_left_cancel₀ (primary_ne_zero
      (hS p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)) hmul

lemma primaryPairCoefficient_norm_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ p ∈ primaryPairFiber S T b, ‖w p‖ ≤ M) :
    ‖primaryPairCoefficient S T w b‖ ≤ ((S.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hw).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le S T hS b)) hM

end CubicFirstMoment

end

end OAI
