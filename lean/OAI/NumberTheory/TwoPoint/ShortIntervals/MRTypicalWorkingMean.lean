import OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingMean
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcWorkingMean
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcAlternative

namespace OAI

/-! The rational major/minor alternative for the actual working bands.
The same finite family works for every additive frequency and every
allowed origin range. -/
namespace TwoPointCorrelations

open Filter Finset

theorem mrt_typical_actual_working_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
    ∀ X H : ℕ, X₀ ≤ X → 10 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter (Real.log X) H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∃ J : ℕ, 1 ≤ J ∧
        (∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ Real.sqrt (Real.log X)/2) ∧
      ∀ Y : ℕ, X ≤ Y → Y+h ≤ 2*X →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
        MRTDistanceLowerBound F X H M → ∀ α : ℝ,
        shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
        C*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C₁,hC₁,W₁,X₁,hmajor⟩ := major_arc_actual_working_mean hprime hhigh
  obtain ⟨C₂,hC₂,W₂,hminor⟩ := minor_arc_actual_working_mean
  obtain ⟨W₃,X₃,hpar⟩ := mrt_working_parameters
  obtain ⟨W₄,hpow⟩ := eventually_atTop.mp (major_arc_working_length_power 1)
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₄,hX₄⟩ := eventually_atTop.mp
    ((hlog.eventually hminor).and
      ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and
        (eventually_ge_atTop (max X₁ X₃))))
  refine ⟨C₁+C₂,by positivity,max W₁ (max W₂ (max W₃ W₄)),X₄,?_⟩
  intro X H hX hH hHX hLH hLL M hM
  dsimp only
  intro hWlarge
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  obtain ⟨hm,hLX,hXs⟩ := hX₄ X hX
  have hX₁ : X₁ ≤ X := (le_max_left _ _).trans hXs
  have hX₃ : X₃ ≤ X := (le_max_right _ _).trans hXs
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans hWlarge
  have hW₂ : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWlarge)
  have hW₃ : W₃ ≤ W := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hWlarge))
  have hW₄ : W₄ ≤ W := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hWlarge))
  obtain ⟨hW,hWH,hWX,_⟩ := major_arc_parameter_bounds hLX hLH hM
  have hW0 : 0 < W := by linarith
  have hWh : W ≤ (h:ℝ) := by
    simpa only [pow_one] using hpow W hW₄ H (by omega) hLH hWH
  obtain ⟨_,_,J,hJ,_,_,hup,hbands⟩ := hpar W hW₃ H (by omega) hLH hWH X hX₃ hWX
  refine ⟨J,hJ,hup,?_⟩
  intro Y hXY hY F hF1 hFm hFb hd α
  have hE : 0 ≤ Real.exp (-M/20)+mrtShortError X H := by
    unfold mrtShortError
    positivity
  obtain ⟨r,q,hq,hqh,hcop,happ,hsq⟩ := minor_arc_short_rational_approximation α h W hW0 hWh
  by_cases hqW : (q:ℝ) ≤ W
  · have hb : ∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n)) := by
      intro n hn hnX
      exact hbands n hn (by omega)
    have ha := hmajor X H hX₁ hH hHX hLH hLL M hM hW₁ Y hXY hY J hJ hb
      F hF1 hFm hFb hd r q hq hqW (α-(r:ℝ)/q) happ
    rw [show (r:ℝ)/q+(α-(r:ℝ)/q)=α by ring] at ha
    apply ha.trans
    have hh := mul_le_mul_of_nonneg_right (show C₁ ≤ C₁+C₂ from le_add_of_nonneg_right hC₂.le)
      (show 0≤(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) by positivity)
    convert hh using 1 <;> ring
  · have hWY : h ≤ Y := (major_arc_working_length_le H W).trans (hHX.trans hXY)
    have ha := hm H (by omega) hLH hLL M hM hW₂ Y J hWY hJ F hFm hFb
      r q (le_of_not_ge hqW) hqh α hcop hsq
    have ha' : shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
        C₂*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
      simpa only [mrtShortError,add_assoc] using ha
    apply ha'.trans
    have hh := mul_le_mul_of_nonneg_right (show C₂ ≤ C₁+C₂ from le_add_of_nonneg_left hC₁.le)
      (show 0≤(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) by positivity)
    convert hh using 1 <;> ring

end TwoPointCorrelations

end OAI
