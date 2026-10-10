import OAI.Probability.InvariantIsing.Magnetic.ConstrainedBlockMagneticEstimate
import OAI.Probability.InvariantIsing.Magnetic.MagneticVariational

namespace OAI

/-! The exact magnetization-slice field bound for the zero-temperature
boundary of the magnetic contact comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma constrainedBlockValue_group_le {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (mag γ : A → ℝ) (hmag : ∀ a, |mag a| < 1)
    (hc : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=N*γ a) (h : FieldStep) :
    constrainedBlockValue (spinGroupSlice group k) h ≤ magneticGroupValue γ mag h := by
  have hg := (biasedConstrainedBlockValue_gap hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h (fun i => magneticBias h (mag (group i)))).1
  rw [← magneticBlockGap_eq_biasedGap hN group k hk mag hmag hc] at hg
  have he : (N : ℝ)⁻¹ * ∑ i, constrainedFieldValue h (mag (group i)) = magneticGroupValue γ mag h := by
    rw [sum_sites_group group (fun a => constrainedFieldValue h (mag a))]
    simp only [hcount, magneticGroupValue]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

  rw [he] at hg
  linarith

lemma constrainedBlockValue_entropy_bound {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (mag γ : A → ℝ) (hmag : ∀ a, |mag a| < 1)
    (hc : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=N*γ a)
    (p : OverlapPath) (S : ℝ) (hS : magneticEntropyFunctional γ mag p ≤ (S : EReal)) (h : FieldStep) :
    constrainedBlockValue (spinGroupSlice group k) h + fieldPairing p h/2 ≤ S := by
  have ht : ((magneticGroupValue γ mag h+fieldPairing p h/2 : ℝ) : EReal) ≤ (S : EReal) :=
    (le_iSup (fun h : FieldStep => ((magneticGroupValue γ mag h+fieldPairing p h/2 : ℝ) : EReal)) h).trans hS
  have ht' : magneticGroupValue γ mag h+fieldPairing p h/2 ≤ S := EReal.coe_le_coe_iff.mp ht
  linarith [constrainedBlockValue_group_le hN group k hk mag γ hmag hc hcount h]

end InvariantIsing

end

end OAI
