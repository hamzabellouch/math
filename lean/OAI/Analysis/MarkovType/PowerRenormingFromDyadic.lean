import OAI.Analysis.MarkovType.DyadicSmoothRenorming

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def dyadicPowerEquivalentNorm {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    EquivalentNorm X where
  p := dyadicPowerSeminorm hq.le hD
  lower := 1
  upper := T
  lower_pos := zero_lt_one
  upper_pos := lt_of_lt_of_le zero_lt_one hT
  lower_bound x := by
    simpa only [one_mul] using norm_le_dyadicPowerSeminorm hq.le hD x
  upper_bound x := dyadicPowerSeminorm_le_mul_norm hq.le hD
    (le_trans zero_le_one hT) le_rfl x

@[simp] theorem dyadicPowerEquivalentNorm_p {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    (dyadicPowerEquivalentNorm hq hT hD).p = dyadicPowerSeminorm hq.le hD := rfl

@[simp] theorem dyadicPowerEquivalentNorm_lower {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    (dyadicPowerEquivalentNorm hq hT hD).lower = 1 := rfl

@[simp] theorem dyadicPowerEquivalentNorm_upper {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    (dyadicPowerEquivalentNorm hq hT hD).upper = T := rfl

theorem dyadicPowerCoefficient_pos {q T : ℝ} (hT : 1 ≤ T) : 0 < T ^ q :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) q

theorem dyadicPowerEquivalentNorm_add_sub_le {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) (x y : X) :
    (((dyadicPowerEquivalentNorm hq hT hD).p (x + y)) ^ q +
      ((dyadicPowerEquivalentNorm hq hT hD).p (x - y)) ^ q) / 2 ≤
      ((dyadicPowerEquivalentNorm hq hT hD).p x) ^ q + T ^ q * ‖y‖ ^ q :=
  dyadicPowerSeminorm_add_sub_le hq.le hD x y

theorem dyadicPowerEquivalentNorm_symmetricPowerSmooth {q T : ℝ}
    (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    SymmetricPowerSmooth (dyadicPowerEquivalentNorm hq hT hD).p q (T ^ q) :=
  dyadicPowerSeminorm_symmetricPowerSmooth hq.le hD (dyadicPowerCoefficient_pos hT).le

theorem dyadicPowerEquivalentNorm_powerSmooth {q T : ℝ}
    (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    PowerSmooth (dyadicPowerEquivalentNorm hq hT hD).p q (T ^ q) :=
  (dyadicPowerEquivalentNorm_symmetricPowerSmooth hq hT hD).powerSmooth
    hq.le (dyadicPowerCoefficient_pos hT).le

theorem dyadicPowerEquivalentNorm_modulus_le {q T : ℝ}
    (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q))
    {t : ℝ} (ht : 0 ≤ t) :
    smoothnessModulus (dyadicPowerEquivalentNorm hq hT hD).p t ≤ T ^ q * t ^ q :=
  (dyadicPowerEquivalentNorm_powerSmooth hq hT hD).smoothnessModulus_le
    (dyadicPowerCoefficient_pos hT).le ht

theorem dyadicPowerEquivalentNorm_standardModulus_le [Nontrivial X] {q T : ℝ}
    (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q))
    {t : ℝ} (ht : 0 ≤ t) :
    sSup (smoothnessDeviations (dyadicPowerEquivalentNorm hq hT hD).p t) ≤
      T ^ q * t ^ q := by
  have heq := (dyadicPowerEquivalentNorm hq hT hD).smoothnessModulus_eq_standard t
  change smoothnessModulus (dyadicPowerEquivalentNorm hq hT hD).p t =
    sSup (smoothnessDeviations (dyadicPowerEquivalentNorm hq hT hD).p t) at heq
  rw [← heq]
  exact dyadicPowerEquivalentNorm_modulus_le hq hT hD ht

theorem dyadicPowerEquivalentNorm_uniformSmooth {q T : ℝ}
    (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    UniformSmooth (dyadicPowerEquivalentNorm hq hT hD).p :=
  (dyadicPowerEquivalentNorm_powerSmooth hq hT hD).uniformSmooth
    hq (dyadicPowerCoefficient_pos hT).le

theorem exists_powerSmooth_equivalentNorm_of_finiteDyadicType {q T : ℝ}
    (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    ∃ N : EquivalentNorm X,
      N.lower = 1 ∧ N.upper = T ∧ 0 < T ^ q ∧
      SymmetricPowerSmooth N.p q (T ^ q) ∧ PowerSmooth N.p q (T ^ q) ∧
      (∀ t : ℝ, 0 ≤ t → smoothnessModulus N.p t ≤ T ^ q * t ^ q) ∧
      UniformSmooth N.p := by
  refine ⟨dyadicPowerEquivalentNorm hq hT hD, rfl, rfl,
    dyadicPowerCoefficient_pos hT,
    dyadicPowerEquivalentNorm_symmetricPowerSmooth hq hT hD,
    dyadicPowerEquivalentNorm_powerSmooth hq hT hD, ?_,
    dyadicPowerEquivalentNorm_uniformSmooth hq hT hD⟩
  intro t ht
  exact dyadicPowerEquivalentNorm_modulus_le hq hT hD ht

end MarkovSuperreflexivity

end

end OAI
