import OAI.NumberTheory.TotientAsymptotic.FiniteFactorMass
import OAI.NumberTheory.TotientAsymptotic.PrimeBandPartition
import OAI.NumberTheory.TotientAsymptotic.IntervalPartCount

namespace OAI

/-! Actual prime-band parts satisfy the independent mass estimate used in Ford 4.1. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem partitioned_squarefree_mass : ∃ D : ℝ,0 < D ∧
    ∀ (k : ℕ) (Y : ℕ → ℝ) (c R : Fin k → ℝ),
    (∀ j < k,Y (j+1) ≤ Y j) → (∀ j < k,2 ≤ Y (j+1)) →
    (∀ j,1 ≤ c j) → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,Squarefree n ∧ partBetween n (Y k) (Y 0)=n ∧
      ∀ j : Fin k,R j ≤ (omegaIn n (Y (j.val+1)) (Y j.val):ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ Real.exp
      (∑ j : Fin k,(c j*(B (Y j.val)-B (Y (j.val+1))+D)-R j*Real.log (c j))) := by
  obtain ⟨D,hD,hbound⟩ := finite_squarefree_band_mass
  refine ⟨D,hD,?_⟩
  intro k Y c R hY hY2 hc Q hQ
  let f := fun n (j : Fin k) => partBetween n (Y (j.val+1)) (Y j.val)
  apply hbound k (fun j => Y (j.val+1)) (fun j => Y j.val) c R
    (fun j => hY2 j.val j.isLt) (fun j => hY j.val j.isLt) hc Q f
  · intro n hn
    dsimp [f]
    rw [Fin.prod_univ_eq_prod_range (fun j => partBetween n (Y (j+1)) (Y j)),
      partBetween_adjacent_product n Y k hY]
    exact (hQ n hn).2.1
  · intro n hn j
    have hsq := (hQ n hn).1
    refine ⟨hsq.squarefree_of_dvd (partBetween_dvd hsq.ne_zero _ _),?_,?_⟩
    · intro p hp
      exact partBetween_support n _ _ hp
    · dsimp [f]
      rw [partBetween_omega]
      exact (hQ n hn).2.2 j

/-- A concrete count of the values themselves. The hypotheses concern only
their interval parts, squarefreeness, and factor-count lower bounds. -/
theorem partitioned_band_value_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X z k : ℕ) (Y : ℕ → ℝ) (c R : Fin k → ℝ),
    2 ≤ S → S ≤ z → Y 0=z → Y k=S →
    (∀ j < k,Y (j+1) ≤ Y j) → (∀ j < k,2 ≤ Y (j+1)) →
    (∀ j,1 ≤ c j) → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ X ∧ z*partBetween n S z ≤ X ∧
      Squarefree (partBetween n S z) ∧
      ∀ j : Fin k,R j ≤ (omegaIn (partBetween n S z) (Y (j.val+1)) (Y j.val):ℝ)) →
    (Q.card:ℝ) ≤ C*X*Real.log S/Real.log z * Real.exp
      (∑ j : Fin k,(c j*(B (Y j.val)-B (Y (j.val+1))+D)-R j*Real.log (c j))) := by
  obtain ⟨C,hC,hcount⟩ := interval_part_count
  obtain ⟨D,hD,hmass⟩ := partitioned_squarefree_mass
  refine ⟨C,D,hC,hD,?_⟩
  intro S X z k Y c R hS hSz hY0 hYk hY hY2 hc Q hQ
  let P := Q.image (fun n => partBetween n (S:ℝ) (z:ℝ))
  have hP (n : ℕ) (hn : n ∈ P) :
      Squarefree n ∧ partBetween n (Y k) (Y 0)=n ∧
      ∀ j : Fin k,R j ≤ (omegaIn n (Y (j.val+1)) (Y j.val):ℝ) := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    refine ⟨(hQ v hv).2.2.2.1,?_,(hQ v hv).2.2.2.2⟩
    rw [hYk,hY0,partBetween_idempotent]
  have hm := hmass k Y c R hY hY2 hc P hP
  have hn := hcount S X z hS hSz Q (fun n hn =>
    ⟨(hQ n hn).1,(hQ n hn).2.1,(hQ n hn).2.2.1⟩)
  have hcoeff : 0 ≤ C*X*Real.log S/Real.log z := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _))
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ S by omega)))
    · exact (Real.log_pos (by exact_mod_cast (show 1 < z by omega))).le
  exact hn.trans (mul_le_mul_of_nonneg_left hm hcoeff)

end TotientAsymptotic

end

end OAI
