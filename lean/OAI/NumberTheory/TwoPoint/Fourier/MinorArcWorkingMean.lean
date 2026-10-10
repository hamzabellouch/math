import OAI.NumberTheory.TwoPoint.Fourier.MinorArcWorkingParameters

namespace OAI

/-! Minor arcs at the same parameter and prime bands as the major arcs.
The original outer logarithm remains fixed while the origin range varies. -/
namespace TwoPointCorrelations

open Filter Finset

theorem minor_arc_actual_working_mean :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter L H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∀ Y J : ℕ, h ≤ Y → 1 ≤ J →
    ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
    ∀ r : ℤ, ∀ q : ℕ, W ≤ (q:ℝ) → (q:ℝ) ≤ (h:ℝ)/W →
    ∀ α : ℝ, IsCoprime (q:ℤ) r → |α-(r:ℝ)/q| ≤ 1/(q:ℝ)^2 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
      C*(Y:ℝ)*h*(Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)) := by
  obtain ⟨C,hC,R₀,hminor⟩ := minor_arc_typical_working_bound
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp
    ((minor_arc_actual_working_parameters R₀).and mrt_working_prime_parameters)
  refine ⟨21*C,by positivity,W₀,?_⟩
  filter_upwards [major_arc_parameter_rate,eventually_ge_atTop (1:ℝ)] with L hrate hL
  intro H hH hLH hLL M hM
  dsimp only
  intro hWlarge Y J hhY hJ F hFm hFb r q hWq hqh α hcop happ
  let W := majorArcParameter L H M
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  obtain ⟨_,hWH,_,_⟩ := major_arc_parameter_bounds hL hLH hM
  obtain ⟨hwindow,hprime⟩ := hW₀ W hWlarge
  obtain ⟨hh,hW,hWh,hLh,hLLh,hcap,hprimes⟩ := hwindow H hH hLH hWH
  obtain ⟨hP,hPQ,hLP,_,_,_,_⟩ := hprime.2 H hH hLH hWH
  have hq : 2 ≤ q := by exact_mod_cast hprime.1.trans hWq
  have hm := hminor (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
    (fun _ _ _ hp => mrtPrimeBand_prime hp)
    (major_arc_actual_bands_disjoint hP hPQ (by linarith)) 1
    (mem_Icc.mpr ⟨le_rfl,hJ⟩) Y h hh hhY hLh hLLh W hW hcap hprimes
    F hFm hFb r q hq hWq hqh α hcop happ
  have hs := hrate (H:ℝ) M hLH hLL hM
  rw [mul_div_assoc] at hs
  have he : majorArcWorkingError W ≤
      21*(Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)) := by
    have hshort : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have herr : 0 ≤ L^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    linarith only [hs,hshort,herr]
  apply hm.trans
  have hp := mul_le_mul_of_nonneg_left he (show 0≤C*(Y:ℝ)*h by positivity)
  convert hp using 1
  ring

end TwoPointCorrelations

end OAI
