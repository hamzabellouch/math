import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailLimit

namespace OAI

/-! A convergent family of the actual weighted exterior correction equations. -/

open Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_radialExterior_convergent_corrections
    (κ : ℝ) (ν : ℕ → ℂ) (ν₀ m : ℂ) (δ : ℝ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hδ : 0 ≤ δ) (hsmall : ‖m‖+2*δ < 1)
    (hκ : radialExteriorMatrixBound ν₀ < κ)
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, Continuous (f n))
    (r : ℕ → ℝ →ᵇ ℂ × ℂ) (r₀ : ℝ →ᵇ ℂ × ℂ) (hr : Tendsto r atTop (nhds r₀)) :
    ∃ v : ℕ → ℝ →ᵇ ℂ × ℂ, ∃ w : ℝ →ᵇ ℂ × ℂ,
      Tendsto v atTop (nhds w) ∧
      (∀ t, w t=radialExteriorTailIntegral κ (fun s => radialExteriorErrorMatrix ν₀ (w s)+r₀ s) t) ∧
      (∀ t, HasDerivAt (fun s => w s)
        (κ • w t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(w t).2)+
          radialExteriorErrorMatrix ν₀ (w t)+r₀ t) t) ∧
      ∀ᶠ n in atTop,
        ‖v n‖ ≤ ‖r n‖/(κ-(radialExteriorMatrixBound (ν n)+radialExteriorCutoffRate n m δ)) ∧
        (∀ t, v n t=radialExteriorTailIntegral κ
          (fun s => radialExteriorErrorField κ (ν n) (radialExteriorCutoffPower n m δ)
            (f n) (r n) s (v n s)) t) ∧
        ∀ t, HasDerivAt (fun s => v n s)
          (κ • v n t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v n t).2)+
            radialExteriorErrorField κ (ν n) (radialExteriorCutoffPower n m δ)
              (f n) (r n) t (v n t)) t := by
  classical
  have hκpos := (radialExteriorMatrixBound_pos ν₀).trans hκ
  let M := radialExteriorErrorField κ ν₀ (fun _ => 0) (fun _ => 0) r₀
  have hzeroLip : ∀ z u : ℂ, ‖(0 : ℂ)-0‖ ≤ (0 : ℝ)*‖z-u‖ := by simp
  obtain ⟨w,_,hw,hwd⟩ := exists_radialExterior_weighted_ODE κ
    (radialExteriorMatrixBound ν₀) ‖r₀‖ hκpos (radialExteriorMatrixBound_pos ν₀).le hκ
    (norm_nonneg _) M
    (radialExteriorErrorField_continuous κ ν₀ _ continuous_const _ continuous_const r₀)
    (fun t => by simpa only [M,radialExteriorErrorField_zero] using r₀.norm_coe_le_norm t)
    (by simpa only [add_zero] using
      radialExteriorErrorField_difference κ 0 (by norm_num) ν₀ _ hzeroLip (fun _ => 0) r₀)
  have hM : ∀ t z, M t z=radialExteriorErrorMatrix ν₀ z+r₀ t := by
    intro t z
    simp [M,radialExteriorErrorField,radialExteriorWeightedIncrement]
  simp only [hM] at hw hwd
  let L : ℕ → ℝ := fun n => radialExteriorMatrixBound (ν n)+radialExteriorCutoffRate n m δ
  have hvex : ∀ n, ∃ v : ℝ →ᵇ ℂ × ℂ, L n < κ →
      ‖v‖ ≤ ‖r n‖/(κ-L n) ∧
      (∀ t, v t=radialExteriorTailIntegral κ
        (fun s => radialExteriorErrorField κ (ν n) (radialExteriorCutoffPower n m δ)
          (f n) (r n) s (v s)) t) ∧
      ∀ t, HasDerivAt (fun s => v s)
        (κ • v t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2)+
          radialExteriorErrorField κ (ν n) (radialExteriorCutoffPower n m δ)
            (f n) (r n) t (v t)) t := by
    intro n
    by_cases hn : L n < κ
    · have hL0 : 0 ≤ L n := add_nonneg (radialExteriorMatrixBound_pos (ν n)).le
        (radialExteriorCutoffRate_nonneg n m δ)
      obtain ⟨v,hv,hi,hd⟩ := exists_radialExterior_weighted_ODE κ (L n) ‖r n‖ hκpos hL0 hn
        (norm_nonneg _) (radialExteriorErrorField κ (ν n) (radialExteriorCutoffPower n m δ) (f n) (r n))
        (radialExteriorErrorField_continuous κ (ν n) _ (radialExteriorCutoffPower_continuous n m δ)
          (f n) (hf n) (r n))
        (fun t => by rw [radialExteriorErrorField_zero]; exact (r n).norm_coe_le_norm t)
        (radialExteriorErrorField_difference κ _ (radialExteriorCutoffRate_nonneg n m δ)
          (ν n) _ (radialExteriorCutoffPower_difference n m δ hδ) (f n) (r n))
      exact ⟨v,fun _ => ⟨hv,hi,hd⟩⟩
    · exact ⟨0,fun h => (hn h).elim⟩
  choose v hv using hvex
  have hB : Tendsto (fun n => radialExteriorMatrixBound (ν n)) atTop
      (nhds (radialExteriorMatrixBound ν₀)) := by
    have hc : Continuous radialExteriorMatrixBound := by unfold radialExteriorMatrixBound; fun_prop
    exact hc.continuousAt.tendsto.comp hν
  have hL : Tendsto L atTop (nhds (radialExteriorMatrixBound ν₀)) := by
    simpa only [L,add_zero] using hB.add (radialExteriorCutoffRate_tendsto m δ hδ hsmall)
  have he : ∀ᶠ n in atTop, L n < κ := hL.eventually (gt_mem_nhds hκ)
  have hspec := he.mono (fun n hn => hv n hn)
  refine ⟨v,w,?_,hw,?_,hspec⟩
  · exact radialExterior_tail_fixedPoint_limit κ ν ν₀ m δ hν hδ hsmall hκ f hf r r₀ hr v w
      (hspec.mono (fun _ h => h.2.1)) hw
  · intro t
    simpa only [add_assoc] using hwd t

end DefocusingNLS

end OAI
