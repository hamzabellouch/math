import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDegree

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles CenteredMomentDetectorDictionary
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentHeckeVolume
open CenteredMomentMask QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma detectorSchwartz_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (detectorSchwartz reverse n σ t:ℝ→ℂ)⊆Set.Icc (1/4) (9/4) := by
  intro x hx
  change detectorSchwartz reverse n σ t x≠0 at hx
  rw [detectorSchwartz_apply] at hx
  exact detector_profile_support reverse n σ (orientedFrequency reverse t) hx

def detectorNormProfile (reverse : Bool) (n : ℕ) (σ t h : ℝ) : 𝓢(ℝ,ℂ) :=
  normPowerProfile (detectorSchwartz reverse n σ t) (1/4) (9/4) (by norm_num)
    (detectorSchwartz_support reverse n σ t) ((detectorSchwartz reverse n σ t).smooth ⊤) h

lemma orientedFrequency_add_height (reverse : Bool) (t h : ℝ) :
    orientedFrequency reverse (t+orientedFrequency reverse h)=orientedFrequency reverse t+h := by
  cases reverse <;> simp [orientedFrequency] ; ring

theorem detectorNormProfile_eq (reverse : Bool) (n : ℕ) (σ t h : ℝ) :
    detectorNormProfile reverse n σ t h=
      detectorSchwartz reverse n σ (t+orientedFrequency reverse h) := by
  ext x
  rw [detectorNormProfile,normPowerProfile_apply,detectorSchwartz_apply,detectorSchwartz_apply,
    orientedFrequency_add_height]
  unfold twistProfile
  by_cases hw : orientedProfile reverse ((logProfile^[n]) positiveAnnular) x=0
  · simp only [hw,zero_mul,mul_zero]
  · have hx : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4)
      ((oriented_detector_log_support reverse n) hw).1
    calc
      _=orientedProfile reverse ((logProfile^[n]) positiveAnnular) x*
          ((x:ℂ)^(Complex.I*h)*(x:ℂ)^(-HeckeDyadic.shift σ (orientedFrequency reverse t))) := by ring
      _=orientedProfile reverse ((logProfile^[n]) positiveAnnular) x*
          (x:ℂ)^(Complex.I*h-HeckeDyadic.shift σ (orientedFrequency reverse t)) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2; unfold HeckeDyadic.shift; push_cast; ring

theorem detectorNormProfile_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2 → ∀σ∈Set.Icc (0:ℝ) 1,∀t h : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorNormProfile reverse n σ t h)≤
        C*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=detectorSchwartz_uniform S
  refine ⟨J,C,hC,?_⟩
  intro reverse n hn σ hσ t h
  rw [detectorNormProfile_eq]
  apply (hbound reverse n hn σ hσ (t+orientedFrequency reverse h)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  have he : ‖orientedFrequency reverse h‖=‖h‖ := by cases reverse <;> simp [orientedFrequency]
  have hh:=norm_add_le t (orientedFrequency reverse h)
  rw [he] at hh
  linarith

theorem detector_volumeControl_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀χ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^B → ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h : ℝ,
      volumeControl Q χ (detectorNormProfile reverse n σ t h)≤C*Z^ε*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,A,hA,hprofile⟩:=detectorNormProfile_uniform pvSeminorms
  obtain ⟨D,hD,hdiv⟩:=polynomial_mask_divisor_bound ε B hε hB
  refine ⟨J,?_⟩
  intro Q
  let mass : ℝ:=Nat.card (O⧸Ideal.span {fixedPeriod Q})
  let K : ℝ:=D*mass*pvConstant*A
  have hmass : 0≤mass:=Nat.cast_nonneg _
  have hK : 0≤K:=by dsimp [K];exact mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hA.le
  refine ⟨1+K,by linarith,?_⟩
  intro Z hZ χ hχ reverse n hn σ hσ t h
  have herr : volumeControl Q χ (detectorNormProfile reverse n σ t h)≤
      (D*Z^ε)*(mass*(pvConstant*(A*(1+‖t‖+‖h‖)^J))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hχ)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hprofile reverse n hn σ hσ t h) pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · positivity
  calc
    _≤(D*Z^ε)*(mass*(pvConstant*(A*(1+‖t‖+‖h‖)^J))) := herr
    _=K*Z^ε*(1+‖t‖+‖h‖)^J := by dsimp [K];ring
    _≤(1+K)*Z^ε*(1+‖t‖+‖h‖)^J := by gcongr;linarith

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
