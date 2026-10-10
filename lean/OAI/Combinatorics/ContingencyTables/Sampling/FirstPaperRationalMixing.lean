import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallKernel

namespace OAI

/-! # Mixing in total variation for the actual rational small-walk law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def smallStationaryRat (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) : ℚ :=
  (blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
    (referenceColumns r c _ _ (stateCapacity r c) j₀) x:ℚ)/
  ∑ y : PaperStates r c,(blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
    (referenceColumns r c _ _ (stateCapacity r c) j₀) y:ℚ)

lemma smallStationaryRat_cast (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) :
    (smallStationaryRat r c i₀ j₀ x:ℝ)=(paperSmallChain r c i₀ j₀).π x := by
  unfold smallStationaryRat
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
  rfl

noncomputable def smallStationaryLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) : RationalLaw (PaperStates r c) where
  mass := smallStationaryRat r c i₀ j₀
  nonnegative := fun x => by
    have h := (paperSmallChain r c i₀ j₀).positive x
    rw [←smallStationaryRat_cast] at h
    exact_mod_cast h.le
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum,smallStationaryRat_cast,Rat.cast_one]
    exact (paperSmallChain r c i₀ j₀).normalized

/-- This is the rational finite-walk distribution, rather than a bound
only on real observables of an abstract chain. -/
theorem smallWalkLaw_variation (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) (n : ℕ) :
    (variation (smallWalkLaw r c i₀ j₀ x n) (smallStationaryLaw r c i₀ j₀):ℝ) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
        Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160) := by
  let C := paperSmallChain r c i₀ j₀
  let δ := ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
    Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160)
  have hpoint (y : PaperStates r c) : |(C.kernel.power n).P x y-C.π y| ≤ C.π y*δ := by
    have h := paperSmallChain_point_mixing r c i₀ j₀ n x y
    change |C.iterate n (C.pointDensity y) x-1| ≤ δ at h
    rw [←C.kernel_power_density] at h
    calc
      _ = C.π y*|(C.kernel.power n).P x y/C.π y-1| := by
        calc
          _ = |C.π y*((C.kernel.power n).P x y/C.π y-1)| := by
            congr 1
            field_simp [(C.positive y).ne']
          _ = _ := by rw [abs_mul,abs_of_pos (C.positive y)]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (C.positive y).le
  have hsum := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hpoint y)
  rw [←Finset.sum_mul,C.normalized,one_mul] at hsum
  unfold variation
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat,
    smallWalkLaw_cast,smallStationaryLaw,smallStationaryRat_cast]
  change (∑ y,|(C.kernel.power n).P x y-C.π y|)/2 ≤ δ
  have hd : 0 ≤ δ := by dsimp only [δ]; positivity
  linarith

end ContingencyTables.SmallGraphProfiles

end OAI
