import OAI.NumberTheory.CubicMoment.Estimates.RoughProductMatrix
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedCoefficients

namespace OAI

/-! The small distinguished-product branch in the original ordered
prime expansion. The factorial, independent weights, no-stop term and
sharp total-product support are all retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def distinguishedSmallSupport (P : ι → Finset Eisenstein) (Z : ℝ) : Finset Eisenstein :=
  (orderedConvolutionSupport P).filter (fun r => norm r < Z)

lemma distinguishedTupleCoefficient_filtered_sum (P : ι → Finset Eisenstein)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    (Q : Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ r ∈ (orderedConvolutionSupport P).filter Q,
      distinguishedTupleCoefficient P W ψ w z r*K r) =
      ((Fintype.card ι).factorial:ℂ)⁻¹ *
        ∑ f ∈ (Fintype.piFinset P).filter (fun f => Q (∏ i, f i)),
          (∏ i, W i (f i)*distinguishedPrimeWeight ψ w z (f i))*K (∏ i, f i) := by
  rw [Finset.sum_filter]
  calc
    _ = ((Fintype.card ι).factorial:ℂ)⁻¹ *
        ∑ r ∈ orderedConvolutionSupport P,
          orderedConvolution P (fun i p => W i p*distinguishedPrimeWeight ψ w z p) r *
            (if Q r then K r else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hq : Q r <;> simp [hq,distinguishedTupleCoefficient,mul_assoc]
    _ = ((Fintype.card ι).factorial:ℂ)⁻¹ *
        ∑ f ∈ Fintype.piFinset P,
          (∏ i, W i (f i)*distinguishedPrimeWeight ψ w z (f i))*
            (if Q (∏ i, f i) then K (∏ i, f i) else 0) := by
      rw [orderedConvolution_sum]
    _ = _ := by
      rw [Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro f _hf
      split_ifs <;> simp

/-- The original ordered distinguished tuples with small product are
exactly the no-stop sum plus the independent stopped-coefficient matrix.
No analytic estimate or replacement of the product cutoff is used. -/
theorem distinguished_roughProduct_matrix (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (P : ι → Finset Eisenstein) (hP : ∀ i, ∀ p ∈ P i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (Z Q : ℝ) (h : ℕ)
    (ψ : ℝ → ℝ) (w z : ℝ) (K : Eisenstein → ℂ) :
    (((Fintype.card ι).factorial:ℂ)⁻¹ *
      ∑ f ∈ (Fintype.piFinset P).filter (fun f => norm (∏ i, f i) < Z),
        (∏ i, W i (f i)*distinguishedPrimeWeight ψ w z (f i))*
          ∑ n ∈ primaryProductSlice S X (∏ i, f i),
            (roughProduct ψ w n:ℂ)*K ((∏ i, f i)*n)) =
      (∑ r ∈ distinguishedSmallSupport P Z,
        distinguishedTupleCoefficient P W ψ w z r *
          ∑ u ∈ primaryElementBall X,
            ∑ m ∈ primaryProductSlice S X (r*u) with
              norm r*primeSurrogate (primaryPrimeFactors m)
                (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
              cutoffMoebius ψ w m*K (r*(m*u))) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
          ∑ b ∈ primaryPairSupport (distinguishedSmallSupport P Z) (primaryElementBall X),
            stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
              stoppedBeta (distinguishedSmallSupport P Z) (primaryElementBall X)
                (distinguishedTupleCoefficient P W ψ w z) ψ w
                (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q true) b *
              (if a*b ∈ S then K (a*b) else 0) := by
  rw [←distinguishedTupleCoefficient_filtered_sum P W ψ w z (fun r => norm r < Z)
    (fun r => ∑ n ∈ primaryProductSlice S X r, (roughProduct ψ w n:ℂ)*K (r*n))]
  apply roughProduct_matrix_stopping S (distinguishedSmallSupport P Z) hρ hρ₂ hX hS
  · intro r hr
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    exact primary_finset_prod _ _
      (fun i _ => (hP i (f i) (Fintype.mem_piFinset.mp hf i)).1)
  · intro r hr
    exact (Finset.mem_filter.mp hr).2

end CubicFirstMoment

end

end OAI
