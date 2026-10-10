import Mathlib
import OAI.Analysis.Conductivity.Scalarization.GeneralModeEndingScalarization
import OAI.Analysis.Conductivity.Fourier.TorusLeadingRealMode

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Real

lemma flatFourier_remove_mode {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B)
    (h₀ : Fin 2 → ℤ) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    flatFourier s a phase x=a h₀*flatPhaseMode s h₀ (phase h₀) x+
      flatFourier s (fun h => if h=h₀ then 0 else a h) phase x := by
  classical
  rw [flatFourier,(flatFourier_summable hs ha hx).tsum_eq_add_tsum_ite h₀]
  congr 1
  unfold flatFourier
  apply tsum_congr
  intro h
  split_ifs <;> simp_all

lemma torusRealContinuation_constant_of_no_modes {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) (hf : ∀ h : Fin 2 → ℤ,h≠0 → realTorusCoeff f h=0)
    {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=(mFourierCoeff f 0).re := by
  rw [torusRealContinuation_mean_free hs f hx]
  have ha : realTorusAmplitude f=0 := by
    ext h
    simp only [realTorusAmplitude,Pi.zero_apply]
    split_ifs with hh
    · rfl
    · rw [hf h hh,norm_zero]
  simp [ha,flatFourier]

theorem torusRealContinuation_leading_decomposition {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    (f : TorusL2) (hf : ∃ h : Fin 2 → ℤ,h≠0 ∧ realTorusCoeff f h≠0) :
    ∃ (h₀ : Fin 2 → ℤ) (L B g : ℝ) (b : (Fin 2 → ℤ) → ℝ),
      h₀≠0 ∧ 0<L ∧ 0≤B ∧ 0<g ∧
      (∀ h,|b h|≤B) ∧
      (∀ h,b h≠0 → torusRate s h₀+g≤torusRate s h) ∧
      ∀ x : Fin 3 → ℝ,0<x 0 →
        torusRealContinuation s f x=(mFourierCoeff f 0).re+
          L*(flatPhaseMode s h₀ (realTorusPhase f h₀) x+
            flatFourier s b (realTorusPhase f) x) := by
  classical
  let M : Set (Fin 2 → ℤ) := {h | h≠0 ∧ realTorusCoeff f h≠0}
  obtain ⟨h₀,hh₀,_,g,hg,hgap⟩ := torus_leading_rate_gap hs hres hf
    (show 0∉M by simp [M])
  change h₀≠0 ∧ realTorusCoeff f h₀≠0 at hh₀
  have hneg : -h₀≠0 := neg_ne_zero.mpr hh₀.1
  have hn : -h₀≠h₀ := by
    intro he
    apply hh₀.1
    ext i
    have hi := congrFun he i
    change -(h₀ i)=h₀ i at hi
    change h₀ i=0
    omega
  let L := 2*‖realTorusCoeff f h₀‖
  have hL : 0<L := mul_pos (by norm_num) (norm_pos_iff.mpr hh₀.2)
  let a' : (Fin 2 → ℤ) → ℝ := fun h => if h=h₀ then 0 else realTorusAmplitude f h
  let a'' : (Fin 2 → ℤ) → ℝ := fun h => if h= -h₀ then 0 else a' h
  let b : (Fin 2 → ℤ) → ℝ := fun h => a'' h/L
  have ha' (h) : |a' h|≤‖f‖ := by
    dsimp [a']; split_ifs
    · simp
    · exact realTorusAmplitude_bound f h
  have ha'' (h) : |a'' h|≤‖f‖ := by
    dsimp [a'']; split_ifs
    · simp
    · exact ha' h
  refine ⟨h₀,L,‖f‖/L,g,b,hh₀.1,hL,div_nonneg (norm_nonneg _) hL.le,hg,?_,?_,?_⟩
  · intro h
    dsimp [b]
    rw [abs_div,abs_of_pos hL]
    exact (div_le_div_iff_of_pos_right hL).mpr (ha'' h)
  · intro h hh
    have hz : h≠0 := by
      intro he
      apply hh
      simp [b,a'',a',realTorusAmplitude,he]
    have hd : realTorusCoeff f h≠0 := by
      intro he
      apply hh
      simp [b,a'',a',realTorusAmplitude,he]
    have he : h≠h₀ := by
      intro he
      apply hh
      simp [b,a'',a',he]
    have hn' : h≠-h₀ := by
      intro he
      apply hh
      simp [b,a'',he]
    exact hgap h ⟨hz,hd⟩ he hn'
  · intro x hx
    rw [torusRealContinuation_mean_free hs f hx,
      flatFourier_remove_mode hs (realTorusAmplitude_bound f) h₀ hx]
    change (mFourierCoeff f 0).re+(_+flatFourier s a' (realTorusPhase f) x)=_
    rw [flatFourier_remove_mode hs ha' (-h₀) hx]
    have he : realTorusAmplitude f h₀*flatPhaseMode s h₀ (realTorusPhase f h₀) x=
        ‖realTorusCoeff f h₀‖*flatPhaseMode s h₀ (realTorusPhase f h₀) x := by
      simp [realTorusAmplitude,hh₀.1]
    have hen : a' (-h₀)*flatPhaseMode s (-h₀) (realTorusPhase f (-h₀)) x=
        ‖realTorusCoeff f h₀‖*flatPhaseMode s h₀ (realTorusPhase f h₀) x := by
      simpa [a',hn,realTorusAmplitude,hneg,realTorusPhase] using realTorusCoeff_polar_neg s f h₀ x
    rw [he,hen]
    change _=(mFourierCoeff f 0).re+L*(_+flatFourier s (fun h => a'' h/L) _ x)
    rw [flatFourier_div_coefficients]
    rw [mul_add,mul_div_cancel₀ _ hL.ne']
    dsimp [L,a'']
    ring

end ScalarConductivity

end
end

end OAI
