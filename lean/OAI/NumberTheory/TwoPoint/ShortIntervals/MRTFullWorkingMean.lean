import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTypicalWorkingMean
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingDensity
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTypicalRemoval

namespace OAI

/-! Remove the literal typical-factor restriction using its proved
uniform density, after the major/minor arc alternative is complete. -/
namespace TwoPointCorrelations

open Filter Finset

theorem mrt_full_actual_working_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
    ∀ X H : ℕ, X₀ ≤ X → 10 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter (Real.log X) H M
      let h := majorArcWorkingLength H W
      W₀ ≤ W → ∀ Y : ℕ, X ≤ Y → Y+h ≤ 2*X →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
        MRTDistanceLowerBound F X H M → ∀ α : ℝ,
        shortExponentialIntegral F Y h α ≤
        C*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C₁,hC₁,W₁,X₁,htypical⟩ := mrt_typical_actual_working_mean hprime hhigh
  obtain ⟨C₂,hC₂,W₂,X₂,hdensity⟩ := mrt_working_interval_density
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₃,hX₃⟩ := eventually_atTop.mp
    ((hlog.eventually major_arc_parameter_rate).and
      ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and
        (eventually_ge_atTop (max X₁ (max X₂ 2)))))
  refine ⟨C₁+42*C₂,by positivity,max W₁ W₂,X₃,?_⟩
  intro X H hX hH hHX hLH hLL M hM
  dsimp only
  intro hWlarge Y hXY hY F hF1 hFm hFb hd α
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  let E := Real.exp (-M/20)+mrtShortError X H
  obtain ⟨hrate,hLX,hXs⟩ := hX₃ X hX
  have hX₁ : X₁ ≤ X := (le_max_left _ _).trans hXs
  have hX₂ : X₂ ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hXs)
  have hXpos : 2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hXs)
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans hWlarge
  have hW₂ : W₂ ≤ W := (le_max_right _ _).trans hWlarge
  obtain ⟨hW,hWH,_,_⟩ := major_arc_parameter_bounds hLX hLH hM
  obtain ⟨J,hJ,hup,ht⟩ := htypical X H hX₁ hH hHX hLH hLL M hM hW₁
  have ht' := ht Y hXY hY F hF1 hFm hFb hd α
  have hu : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log X)/2) := by
    intro j hj
    have hh := Real.exp_le_exp.mpr (hup j hj)
    change Real.exp (Real.log (mrtBandUpper Q j)) ≤ _ at hh
    rwa [Real.exp_log (show 0 < mrtBandUpper Q j from Real.exp_pos _)] at hh
  let : NeZero (Y+h) := ⟨by omega⟩
  have hden := hdensity W hW₂ H (by omega) hLH hWH X hX₂ J hu 1 (Y+h) (by omega)
  have hk : majorArcWorkingError W ≤ 21*E := by
    have hh := hrate H M hLH hLL hM
    rw [mul_div_assoc] at hh
    have hshort : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have herr : 0 ≤ (Real.log X)^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    dsimp only [E,mrtShortError]
    linarith only [hh,hshort,herr]
  have hE : 0 ≤ E := by dsimp [E,mrtShortError]; positivity
  have hN : ((Y+h:ℕ):ℝ) ≤ 2*(Y:ℝ) := by
    have hh : h ≤ Y := (major_arc_working_length_le H W).trans (hHX.trans hXY)
    exact_mod_cast (show Y+h ≤ 2*Y by omega)
  have he : (h:ℝ)*(Y+h)*(C₂*majorArcWorkingError W) ≤ 42*C₂*(Y:ℝ)*h*E := by
    calc
      _ ≤ (h:ℝ)*(2*Y)*(C₂*majorArcWorkingError W) := by
        have hκ : 0 ≤ majorArcWorkingError W := mul_nonneg
          (by linarith [Real.log_nonneg hW]) (Real.rpow_nonneg (by linarith) _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add] using hN)
            (Nat.cast_nonneg h)) (mul_nonneg hC₂.le hκ)
      _ ≤ (h:ℝ)*(2*Y)*(C₂*(21*E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hC₂.le) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α+
        (h:ℝ)*(Y+h)*(C₂*majorArcWorkingError W) :=
      minor_arc_remove_typical _ _ F hFb Y h α _ hden
    _ ≤ C₁*(Y:ℝ)*h*E+42*C₂*(Y:ℝ)*h*E := add_le_add ht' he
    _ = _ := by dsimp only [E]; ring

end TwoPointCorrelations

end OAI
