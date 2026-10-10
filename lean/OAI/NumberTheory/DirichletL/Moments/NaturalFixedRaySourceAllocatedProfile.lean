import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorProfile
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredMomentDetectorDictionary CenteredMomentAllocatedNaturalSource
open CenteredMomentRetainedProfile CenteredMomentLattice CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation QuadraticInitialBound EisensteinSchwartzPoisson

def detectorPlain (reverse : Bool) (n : ℕ) (σ t : ℝ) : Plain where
  W := detectorSchwartz reverse n σ t
  a := 1/4
  b := 9/4
  a_pos := by norm_num
  support := detectorSchwartz_support reverse n σ t
  smooth := (detectorSchwartz reverse n σ t).smooth ⊤

theorem detectorPlain_profile_apply (reverse : Bool) (n : ℕ) (σ t U : ℝ)
    (hU : 0<U) (h x : ℝ) :
    (detectorPlain reverse n σ t).profile U hU h x =
      if 1≤U*(9/4) then
        (x:ℂ)^(Complex.I*h)*detectorSchwartz reverse n σ t (clipDilation U*x)
      else 0 := by
  by_cases hr : 1≤U*(9/4)
  · have hr' : 1 ≤ U * (detectorPlain reverse n σ t).b := hr
    rw [Plain.profile_retained _ U hU h hr',retainedProfile_apply,ite_eq_left hr]
    rfl
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr),ite_eq_right hr]
    rfl

theorem detectorPlain_profile_support (reverse : Bool) (n : ℕ) (σ t U : ℝ)
    (hU : 0<U) (h : ℝ) :
    Function.support ((detectorPlain reverse n σ t).profile U hU h:ℝ→ℂ)⊆
      Set.Icc (1/9) (9/4) := by
  by_cases hr : 1≤U*(9/4)
  · rw [Plain.profile_retained _ U hU h hr]
    have hs:=retainedProfile_support _ _ _ (detectorPlain reverse n σ t).a_pos
      (detectorPlain reverse n σ t).support (detectorPlain reverse n σ t).smooth U hU hr h
    norm_num [detectorPlain] at hs ⊢
    exact hs
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr)]
    simp

theorem detectorPlain_profile_seminorm (S : Finset (ℕ×ℕ))
    (reverse : Bool) (n : ℕ) (σ t U : ℝ) (hU : 0<U) (h : ℝ) :
    S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((detectorPlain reverse n σ t).profile U hU h)≤
      (9/4:ℝ)^(S.sup Prod.snd)*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorNormProfile reverse n σ t h) := by
  by_cases hr : 1≤U*(9/4)
  · rw [Plain.profile_retained _ U hU h hr]
    have hc:=clipDilation_le (9/4) U hU hr
    norm_num at hc
    have hb:=normPowerProfile_dilated_finite (detectorSchwartz reverse n σ t)
      (1/4) (9/4) (9/4) (clipDilation U) (by norm_num) (by norm_num)
      (clipDilation_ge_one U hU) hc (detectorSchwartz_support reverse n σ t)
      ((detectorSchwartz reverse n σ t).smooth ⊤) h S
    simpa only [detectorPlain,retainedProfile,detectorNormProfile,
      max_eq_right (by norm_num : (1:ℝ)≤9/4)] using hb
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr),map_zero]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)

theorem detectorPlain_profile_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h U : ℝ,∀hU : 0<U,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((detectorPlain reverse n σ t).profile U hU h)≤
        C*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=detectorNormProfile_uniform S
  refine ⟨J,(9/4:ℝ)^(S.sup Prod.snd)*C,mul_pos (by positivity) hC,?_⟩
  intro reverse n hn σ hσ t h U hU
  exact (detectorPlain_profile_seminorm S reverse n σ t U hU h).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (hbound reverse n hn σ hσ t h) (show 0≤(9/4:ℝ)^(S.sup Prod.snd) by positivity)))

theorem detectorPlain_volumeControl_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal HeckeFamily.O,∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀χ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^B → ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h U : ℝ,∀hU : 0<U,
      volumeControl Q χ ((detectorPlain reverse n σ t).profile U hU h)≤
        C*Z^ε*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,hbound⟩:=detector_volumeControl_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q
  obtain ⟨C,hC,hbound⟩:=hbound Q
  refine ⟨(9/4:ℝ)^(pvSeminorms.sup Prod.snd)*C,mul_pos (by positivity) hC,?_⟩
  intro Z hZ χ hχ reverse n hn σ hσ t h U hU
  by_cases hr : 1≤U*(9/4)
  · rw [Plain.profile_retained _ U hU h hr]
    have hv:=retained_volumeControl_le Q χ (detectorSchwartz reverse n σ t) (1/4) (9/4)
      (by norm_num) (detectorSchwartz_support reverse n σ t)
      ((detectorSchwartz reverse n σ t).smooth ⊤) U hU hr h
    have hv' : volumeControl Q χ (retainedProfile (detectorPlain reverse n σ t).W
        (detectorPlain reverse n σ t).a (detectorPlain reverse n σ t).b
        (detectorPlain reverse n σ t).a_pos (detectorPlain reverse n σ t).support
        (detectorPlain reverse n σ t).smooth U hU hr h)≤
        (9/4:ℝ)^(pvSeminorms.sup Prod.snd)*volumeControl Q χ (detectorNormProfile reverse n σ t h) := by
      simpa only [detectorPlain,detectorNormProfile,max_eq_right (by norm_num : (1:ℝ)≤9/4)] using hv
    exact hv'.trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (hbound Z hZ χ hχ reverse n hn σ hσ t h)
      (show 0≤(9/4:ℝ)^(pvSeminorms.sup Prod.snd) by positivity)))
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr)]
    simp only [volumeControl,pvControl,map_zero,mul_zero]
    positivity

theorem allocated_detector_profiles_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀α : Type,∀_ : Fintype α,∀_ : DecidableEq α,
      ∀D : Ideal HeckeFamily.O,
      ∀a : CenteredMomentDivisorAllocation.Allocation D (Finset.univ : Finset (α⊕Fin 2)),
      ∀reverse : Fin 2→Bool,∀n : Fin 2→ℕ,(∀j,n j≤2) →
      ∀σ : Fin 2→ℝ,(∀j,σ j∈Set.Icc (0:ℝ) 1) →
      ∀t X : Fin 2→ℝ,∀hX : ∀j,0<X j,∀h : ℝ,∀j : Fin 2,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        ((detectorPlain (reverse j) (n j) (σ j) (t j)).profile
          (rawScale D a (X j) j) (rawScale_pos D a (X j) (hX j) j) h)≤
        C*(1+‖t 0‖+‖t 1‖+‖h‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=detectorPlain_profile_uniform S
  refine ⟨J,C,hC,?_⟩
  intro α _ _ D a reverse n hn σ hσ t X hX h j
  apply (hbound (reverse j) (n j) (hn j) (σ j) (hσ j) (t j) h
    (rawScale D a (X j) j) (rawScale_pos D a (X j) (hX j) j)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  fin_cases j <;> dsimp <;> linarith [abs_nonneg (t 0),abs_nonneg (t 1)]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
