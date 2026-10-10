import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
import OAI.NumberTheory.DirichletL.Moments.RetainedProfile

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentLattice CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeHeight
open CenteredMomentMask
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B → ∀ t : ℝ,
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * Z^ε * (1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hprofile⟩ := normPowerProfile_source_control a b ha pvSeminorms
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  let S := insert (0,0) T
  refine ⟨n,S,by simp [S],?_⟩
  intro Q
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  let A := D*mass*pvConstant*C
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  have hpv := pvConstant_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1+A,by positivity,?_⟩
  intro W hs Z hZ χ hnorm t
  have hTS : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro z hz
    exact Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hz)
  have hp := (hprofile W hs t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTS hC.le) (by positivity))
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
      (D*Z^ε)*(mass*(pvConstant*(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg hpv.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  calc
    _ ≤ _ := herr
    _ = A*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by dsimp [A]; ring
    _ ≤ (1+A)*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
      gcongr
      linarith

theorem retained_volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B →
      ∀ X : ℝ, ∀ hX : 0<X, ∀ hret : 1≤X*b, ∀ t : ℝ,
      volumeControl Q χ (CenteredMomentRetainedProfile.retainedProfile
        W a b ha hs (W.smooth ⊤) X hX hret t) ≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
  obtain ⟨n,S,hS,hbound⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨n,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩ := hbound Q
  refine ⟨(max 1 b)^(pvSeminorms.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs Z hZ χ hχ X hX hret t
  exact (CenteredMomentRetainedProfile.retained_volumeControl_le
    Q χ W a b ha hs (W.smooth ⊤) X hX hret t).trans
    ((mul_le_mul_of_nonneg_left (hCbound W hs Z hZ χ hχ t) (by positivity)).trans_eq (by ring))
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
