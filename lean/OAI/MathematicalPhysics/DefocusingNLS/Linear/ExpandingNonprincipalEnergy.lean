import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactEnergyError

namespace OAI

/-! # The actual nonprincipal quadratic form and its uniform bounds -/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance nonprincipalEnergyMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance nonprincipalEnergyProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def expandingNonprincipalEnergy (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (P : ℝ) (hP : 0 ≤ P)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ P)
    (f : FourierL2) : ℝ :=
  inner ℝ f (expandingLinearizedPotential a N L ha ha1 hN hL m q f) -
    ∑ j : Fin N → Fin 12,
      inner ℝ (expandingOrderedPhysicalEnergy a L N hL j f)
        (torusPrincipalPotential m (expandingUnitTorusFunction a N L q)
          (expandingUnitTorusFunction a N L q).continuous P hP hQB
          (expandingOrderedPhysicalEnergy a L N hL j f))

theorem expandingNonprincipalEnergy_smul (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (P : ℝ) (hP : 0 ≤ P)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ P)
    (c : ℝ) (f : FourierL2) :
    expandingNonprincipalEnergy a L N ha ha1 hN hL m q P hP hQB (c • f) =
      c ^ 2 * expandingNonprincipalEnergy a L N ha ha1 hN hL m q P hP hQB f := by
  unfold expandingNonprincipalEnergy
  simp only [ContinuousLinearMap.map_smul_of_tower, real_inner_smul_left, real_inner_smul_right]
  simp only [← mul_assoc, ← Finset.mul_sum]
  ring

theorem expandingNonprincipalEnergy_le (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (P : ℝ) (hP : 0 ≤ P)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ P)
    (D : ℝ) (hD : ‖expandingLinearizedPotential a N L ha ha1 hN hL m q‖ ≤ D)
    (f : FourierL2) :
    expandingNonprincipalEnergy a L N ha ha1 hN hL m q P hP hQB f ≤
      (D + (2 * (m : ℝ) + 1) * P) * ‖f‖ ^ 2 := by
  let B := (2 * (m : ℝ) + 1) * P
  let V := torusPrincipalPotential m (expandingUnitTorusFunction a N L q)
    (expandingUnitTorusFunction a N L q).continuous P hP hQB
  let U := expandingOrderedPhysicalEnergy a L N hL
  have hpair : inner ℝ f (expandingLinearizedPotential a N L ha ha1 hN hL m q f) ≤ D * ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖f‖ * ‖expandingLinearizedPotential a N L ha ha1 hN hL m q f‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * (D * ‖f‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ f).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg f))
      _ = _ := by ring
  have hneg (j : Fin N → Fin 12) : -inner ℝ (U j f) (V (U j f)) ≤ B * ‖U j f‖ ^ 2 := by
    calc
      _ ≤ |inner ℝ (U j f) (V (U j f))| := neg_le_abs _
      _ ≤ ‖U j f‖ * ‖V (U j f)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖U j f‖ * (B * ‖U j f‖) :=
        mul_le_mul_of_nonneg_left
          (torusPrincipalAction_norm_le m (expandingUnitTorusFunction a N L q)
            (expandingUnitTorusFunction a N L q).continuous P hP hQB (U j f)) (norm_nonneg _)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hneg j)
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, expandingOrderedPhysicalEnergy_norm_sq] at hsum
  have hhigh : ‖expandingHighEnergy a N L hL f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have he := expandingEnergy_norm_sq a N L hL f
    nlinarith [sq_nonneg ‖expandingLowEnergy a N L hL f‖]
  have htotal := hsum.trans (mul_le_mul_of_nonneg_left hhigh (show 0 ≤ B by dsimp [B]; positivity))
  change inner ℝ f _ - ∑ j, inner ℝ (U j f) (V (U j f)) ≤ _
  dsimp only [B] at htotal
  linarith

theorem exists_expandingLinearized_norm_bound (a k Q : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hQ : 0 ≤ Q) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (q : FourierL2), ‖q‖ ≤ Q →
      ‖expandingLinearizedPotential a k L ha ha1 hk hL m q‖ ≤ D := by
  obtain ⟨D, hD, hb⟩ := exists_expandingOddPower_two_jet_bound a k ha ha1 hk m Q hQ
  refine ⟨D, hD, fun L hL q hq => ?_⟩
  have he := hb L hL q hq 1 (by norm_num)
  simpa only [norm_iteratedFDeriv_one, expandingLinearizedPotential, norm_smul,
    norm_neg, Complex.norm_I, one_mul] using he

end DefocusingNLS

end OAI
