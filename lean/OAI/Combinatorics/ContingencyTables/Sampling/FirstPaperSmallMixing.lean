import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallChain
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalMassBound

namespace OAI

/-! # Minimum mass and mixing of the actual small chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def stateBound (r : I → ℕ) (_c : J → ℕ) : ℕ :=
  (∑ i,r i)+(dimensionAllowance (I := I) (J := J))*
    ((dimensionAllowance (I := I) (J := J))^12)+
    (dimensionAllowance (I := I) (J := J))^20+2

omit [LinearOrder I] [LinearOrder J] in
lemma stateCapacity_le_bound (r : I → ℕ) (c : J → ℕ) (i : I) (j : J) :
    stateCapacity r c i j ≤ stateBound r c := by
  unfold stateCapacity paperCapacity stateBound
  split_ifs <;> omega

lemma stateWeight_ge_one (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :
    1 ≤ stateWeight r c z := by
  have he := hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)
  change 1 ≤ hardMarginal _ _ _ _ _ _
  rw [he]
  have hp := stateWeight_positive r c z
  change 0 < hardMarginal _ _ _ _ _ _ at hp
  rw [he] at hp
  have hn : 0 < Fintype.card (CompletionFibre (paperSmall r c) (stateCapacity r c) r
      (fun i => r i+PaddedCompletions.rowLargeCount (paperSmall r c) i*
        ((dimensionAllowance (I := I) (J := J))^12)) c
      (fun j => c j+PaddedCompletions.columnLargeCount (paperSmall r c) j*
        ((dimensionAllowance (I := I) (J := J))^12))
      (physicalProfile _ (stateCapacity r c) r c _ z)) := by exact_mod_cast hp
  exact_mod_cast (Nat.succ_le_of_lt hn)

lemma state_total_mass_le (r : I → ℕ) (c : J → ℕ) :
    (∑ z,stateWeight r c z) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J)) :=
  physical_total_mass_le (paperSmall r c) (stateCapacity r c) r c _ (stateBound r c)
    (stateCapacity_le_bound r c)

lemma paperSmallChain_pi_lower (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) :
    1/(((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))) ≤
      (paperSmallChain r c i₀ j₀).π z := by
  have hsum : 0 < ∑ y,stateWeight r c y :=
    Finset.sum_pos (fun y _ => stateWeight_positive r c y) Finset.univ_nonempty
  rw [paperSmallChain_pi]
  exact (one_div_le_one_div_of_le hsum (state_total_mass_le r c)).trans
    (div_le_div_of_nonneg_right (stateWeight_ge_one r c z) hsum.le)

theorem paperSmallChain_point_mixing (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (n : ℕ) (x y : PaperStates r c) :
    let C := paperSmallChain r c i₀ j₀
    |C.iterate n (C.pointDensity y) x-1| ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
        Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160) := by
  have hd : (1:ℝ) ≤ dimensionAllowance (I := I) (J := J) := by
    exact_mod_cast (show 1 ≤ dimensionAllowance (I := I) (J := J) by
      unfold dimensionAllowance
      omega)
  have h := (paperSmallChain r c i₀ j₀).point_mixing_exp
    ((dimensionAllowance (I := I) (J := J):ℝ)^160)
    (1/(((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))))
    (one_le_pow₀ hd) (by positivity) (paperSmallChain_pi_lower r c i₀ j₀)
    (paperSmallChain_poincare r c i₀ j₀) n x y
  simpa only [one_div, div_eq_mul_inv, one_mul, inv_inv, mul_comm] using h

/-- The manuscript's total-variation estimate, for the literal transition
law started at any actual physical state. -/
theorem paperSmallChain_total_variation (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (n : ℕ) (y : PaperStates r c) :
    let C := paperSmallChain r c i₀ j₀
    (∑ x,|C.π x*C.iterate n (C.pointDensity y) x-C.π x|)/2 ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
        Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160) := by
  let C := paperSmallChain r c i₀ j₀
  let δ := ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
    Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160)
  have hpoint (x : PaperStates r c) :
      |C.π x*C.iterate n (C.pointDensity y) x-C.π x| ≤ C.π x*δ := by
    calc
      _ = C.π x*|C.iterate n (C.pointDensity y) x-1| := by
        calc
          _ = |C.π x*(C.iterate n (C.pointDensity y) x-1)| := by
            congr 1
            ring
          _ = _ := by rw [abs_mul,abs_of_pos (C.positive x)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (paperSmallChain_point_mixing r c i₀ j₀ n x y)
        (C.positive x).le
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [← Finset.sum_mul,C.normalized,one_mul] at hsum
  change _ ≤ δ
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  linarith

end ContingencyTables.SmallGraphProfiles

end OAI
