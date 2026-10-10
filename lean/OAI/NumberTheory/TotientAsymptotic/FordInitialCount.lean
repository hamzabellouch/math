import OAI.NumberTheory.TotientAsymptotic.FordInitialFiber

namespace OAI

/-! The full first-band count, with the terminal reciprocal mass left explicit. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordStateMass {b : ℕ} (T : Finset (ShiftedPair b)) (Y : ℕ → ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ s ∈ T.image (fun t => fordFactorState t (Y k)),(factorProduct s:ℝ)⁻¹

lemma fordStateMass_nonneg {b : ℕ} (T : Finset (ShiftedPair b)) (Y : ℕ → ℝ) (k : ℕ) :
    0 ≤ fordStateMass T Y k := by
  classical
  exact Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem ford_initial_count : ∃ C : ℝ,0 < C ∧
    ∀ (b D r : ℕ) (y S : ℝ) (Y U : ℕ → ℝ),Real.exp 2 ≤ y → 1 ≤ B y → 2 ≤ Y 1 →
    FordComparisonParameters b y S D r Y U →
    ∀ T : Finset (ShiftedPair b),(∀ t ∈ T,FordComparisonConditions b y S D r Y U t) →
    (T.card:ℝ) ≤
      (C*(y/(D*r:ℕ))*(B y)^2/(Real.log y/(6*B y))^3)*
        (Real.log y/Real.log (Y 1))*fordStateMass T Y 1 := by
  classical
  obtain ⟨C,hC,hbound⟩ := ford_initial_fiber_count
  refine ⟨C,hC,?_⟩
  intro b D r y S Y U hy hBy hU hp T hT
  let P := T.image (fun t => fordFactorState t (Y 1))
  have hmap : ∀ t ∈ T,fordFactorState t (Y 1) ∈ P :=
    fun t ht => Finset.mem_image.mpr ⟨t,ht,rfl⟩
  have heq : (T.card:ℝ)=∑ s ∈ P,((T.filter (fun t => fordFactorState t (Y 1)=s)).card:ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))
    simpa using hh.symm
  calc
    _ = ∑ s ∈ P,((T.filter (fun t => fordFactorState t (Y 1)=s)).card:ℝ) := heq
    _ ≤ ∑ s ∈ P,(C*(y/(D*r*factorProduct s:ℕ))*(B y)^2/(Real.log y/(6*B y))^3)*
        (Real.log y/Real.log (Y 1)) :=
      Finset.sum_le_sum (fun s hs => hbound b D r y S Y U hy hBy hU hp T hT s hs)
    _ = _ := by
      dsimp only [fordStateMass]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      push_cast
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end TotientAsymptotic

end

end OAI
