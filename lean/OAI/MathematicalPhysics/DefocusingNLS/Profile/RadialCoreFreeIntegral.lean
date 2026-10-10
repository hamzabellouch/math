import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreComplex
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePropagation

namespace OAI

/-! The limiting real core yields the free integral initial-value problem with its actual data. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_integral_of_derivatives (b l u : ℝ) (hl : 0 < l)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hF₀ : F l=1) (hG₀ : G l=0)
    (hDE : ∀ r ∈ Ioo l u, HasDerivAt F (G r) r ∧ HasDerivAt G
      (-radialFreeCoefficient r*G r-(b : ℂ)*F r) r) :
    (∀ r ∈ Icc l u, F r=1+∫ t in l..r, G t) ∧
    (∀ r ∈ Icc l u, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t) := by
  have hforcing := (radialFreeField_continuousOn_curve b l u hl
    (fun t => (F t,G t)) (hF.prodMk hG)).snd
  constructor
  · intro r hr
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 hF.continuousOn
      (fun t ht => (hDE t ⟨ht.1,ht.2.trans_le hr.2⟩).1) (hG.intervalIntegrable l r)
    rw [hF₀] at he
    linear_combination -he
  · intro r hr
    have hi : IntervalIntegrable (fun t => -radialFreeCoefficient t*G t-(b : ℂ)*F t) volume l r :=
      ContinuousOn.intervalIntegrable_of_Icc hr.1
        (hforcing.mono (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 hG.continuousOn
      (fun t ht => (hDE t ⟨ht.1,ht.2.trans_le hr.2⟩).2) hi
    simpa only [hG₀,sub_zero] using he.symm

theorem radial_core_free_integral (R ρ b : ℝ) (hρ0 : (3 : ℝ) ≤ ρ) (hρR : ρ < R)
    (hRu : R ≤ (10/3 : ℝ)) (hwidth : R-ρ ≤ (1/1000 : ℝ))
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAP : ∀ r ∈ Icc 0 R, 0 < A r)
    (hcore : EqOn A (fun _ => 1) (Icc 0 ρ)) (hDρ : D ρ=0)
    (hAD : ∀ r ∈ Ioo ρ R, HasDerivAt A (D r) r)
    (hDE : ∀ r ∈ Ioo ρ R, HasDerivAt D
      (-11/r*D r-radialAmplitudePotential 6 b A r*A r) r) :
    ∃ F G : ℝ → ℂ, Continuous F ∧ Continuous G ∧
      (∀ r ∈ Icc ρ R, F r=1+∫ t in ρ..r, G t) ∧
      (∀ r ∈ Icc ρ R, G r=∫ t in ρ..r,
        -radialFreeCoefficient t*G t-(b : ℂ)*F t) ∧
      (∀ r ∈ Icc ρ R, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2) ∧
      (∀ r ∈ Icc ρ R, ‖F r‖=A r) := by
  obtain ⟨F,G,hFc,hGc,hF₀,hG₀,hder,hmod⟩ := radial_core_free_complex R ρ b (by linarith) hρR
    A D hA hD hAP hcore hDρ hAD hDE
  obtain ⟨hFI,hGI⟩ := radial_free_integral_of_derivatives b ρ R (by linarith) F G hFc hGc hF₀ hG₀ hder
  have hstate := radial_free_components_state b ρ R (by linarith) F G hFc hGc 1 0
    hFI (by simpa only [zero_add] using hGI)
  have hbound := radial_free_state_bound b ρ R hb hρ0 hRu hρR.le hwidth
    (fun t => (F t,G t)) (hFc.prodMk hGc) (1,0) hstate
  refine ⟨F,G,hFc,hGc,hFI,hGI,?_,hmod⟩
  intro r hr
  have hh : ‖(F r,G r)‖ ≤ 2 := by simpa using hbound r hr
  exact ⟨(norm_fst_le _).trans hh,(norm_snd_le _).trans hh⟩

end DefocusingNLS

end OAI
