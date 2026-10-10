import OAI.NumberTheory.TotientAsymptotic.FordStateTransfer
import OAI.NumberTheory.TotientAsymptotic.FordInitialCount

namespace OAI

/-! Finite iteration on images of the actual Ford cutoff states. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordBandCost (C : ℝ) (k : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) : ℝ :=
  (C*(k:ℝ)^2*(B y)^2/(Real.log (U (k-1)))^2)*
    Real.exp (fordBandCap k y S Y*(Real.log k+1))

lemma fordBandCost_nonneg {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) :
    0 ≤ fordBandCost C k y S Y U := by
  unfold fordBandCost
  positivity

lemma state_mass_iteration {M A : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hA : ∀ i ∈ Finset.Icc 2 k,0 ≤ A i)
    (hstep : ∀ i ∈ Finset.Icc 2 k,M (i-1) ≤ A i*M i) :
    M 1 ≤ (∏ i ∈ Finset.Icc 2 k,A i)*M k := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hsub : Finset.Icc 2 k ⊆ Finset.Icc 2 (k+1) := Finset.Icc_subset_Icc le_rfl (by omega)
    have hprev := ih (fun i hi => hA i (hsub hi)) (fun i hi => hstep i (hsub hi))
    have hnew := hstep (k+1) (by simp; omega)
    have hprod : 0 ≤ ∏ i ∈ Finset.Icc 2 k,A i :=
      Finset.prod_nonneg (fun i hi => hA i (hsub hi))
    calc
      _ ≤ (∏ i ∈ Finset.Icc 2 k,A i)*M k := hprev
      _ ≤ (∏ i ∈ Finset.Icc 2 k,A i)*(A (k+1)*M (k+1)) :=
        mul_le_mul_of_nonneg_left (by simpa using hnew) hprod
      _ = _ := by rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ k+1)]; ring

theorem ford_state_iteration : ∃ C D₀ : ℝ,0 < C ∧ 0 < D₀ ∧
    ∀ (b D r : ℕ) (y S : ℝ) (Y U : ℕ → ℝ),Real.exp 2 ≤ y → 1 ≤ B y →
    FordComparisonParameters b y S D r Y U →
    (∀ k ∈ Finset.Icc 2 b,2 ≤ Y k ∧ 1 < U (k-1)) →
    D₀ ≤ Real.sqrt (B S*B y) →
    ∀ T : Finset (ShiftedPair b),
    (∀ t ∈ T,FordComparisonConditions b y S D r Y U t) →
    fordStateMass T Y 1 ≤
      (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)*fordStateMass T Y b := by
  obtain ⟨C,D₀,hC,hD₀,hbound⟩ := ford_state_mass_transfer
  refine ⟨C,D₀,hC,hD₀,?_⟩
  intro b D r y S Y U hy hBy hp hcut hroot T hT
  apply state_mass_iteration hp.1
    (fun k _ => fordBandCost_nonneg hC.le k y S Y U)
  intro k hk
  obtain ⟨hk2,hkb⟩ := Finset.mem_Icc.mp hk
  exact hbound b k D r hkb ⟨k-1,by omega⟩ (by simp; omega)
    y S Y U hy hBy hp (hcut k hk).1 (hcut k hk).2 hroot T hT

end TotientAsymptotic

end

end OAI
