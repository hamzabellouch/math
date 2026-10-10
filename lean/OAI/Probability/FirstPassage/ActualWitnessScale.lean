import OAI.Probability.FirstPassage.WitnessBorelCantelli

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter

lemma witness_scale_inequalities (b m₀ am ap η s L : ℝ) (hm : 0 < m₀)
    (hη : 0 < η) (hη1 : η ≤ 1) (hs : 2 ≤ s)
    (hS : max |m₀-((am+ap)/2)*b| |(am+ap)/2| / η ≤ s)
    (hD : ((η+2*|(am+ap)/2|+1)/m₀)*s ≤ L) :
    max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*s ∧
    η*s < 2*m₀*L-|(am+ap)/2| *(s+1) ∧
    3*η*s+2*|(am+ap)/2| *(s+1) < 100*(1+|am|+|ap|)*s := by
  have hstep := (div_le_iff₀ hη).mp hS
  have hD' := mul_le_mul_of_nonneg_left hD hm.le
  have he : m₀*((η+2*|(am+ap)/2|+1)/m₀*s)=(η+2*|(am+ap)/2|+1)*s := by field_simp
  rw [he] at hD'
  have hA : 2*|(am+ap)/2| ≤ |am|+|ap| := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    linarith [abs_add_le am ap]
  have hAs := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ s+1)
  have hηs := mul_le_mul_of_nonneg_right hη1 (by linarith : 0 ≤ s)
  have haS := mul_nonneg (abs_nonneg am) (by linarith : 0 ≤ s-1)
  have hapS := mul_nonneg (abs_nonneg ap) (by linarith : 0 ≤ s-1)
  have hmidS := mul_nonneg (abs_nonneg ((am+ap)/2)) (by linarith : 0 ≤ s-1)
  refine ⟨by nlinarith,?_,?_⟩ <;> nlinarith [abs_nonneg am,abs_nonneg ap,abs_nonneg ((am+ap)/2),mul_pos hη (by linarith : 0<s)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_witness_scale (henv : ExponentialEnvironment P τ) (b η : ℝ)
    (hb : |b| ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ k m : ℕ, 2 ≤ (2 : ℝ)^k ∧
      max |actualSourceTimeConstant (direction b)-
        ((extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2)*b|
        |(extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2| ≤ η*(2 : ℝ)^k ∧
      η*(2 : ℝ)^k < 2*actualSourceTimeConstant (direction b)*(2 : ℝ)^m-
        |(extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2| *((2 : ℝ)^k+1) ∧
      3*η*(2 : ℝ)^k+2*|(extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2| *((2 : ℝ)^k+1)
        < sourceCrossingK actualSourceTimeConstant b*(2 : ℝ)^k ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
        (is.map (spatialWitnessFamily b (actualSourceTimeConstant (direction b))
          (extremeSlope actualSourceTimeConstant b false) (extremeSlope actualSourceTimeConstant b true)
          (sourceCrossingK actualSourceTimeConstant b) η k m)) (fun e => τ e ω)} ≤
        (((1 : ℝ)/1024)^16)^is.length := by
  let μ := actualSourceTimeConstant
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  let a := (am+ap)/2
  let m₀ := μ (direction b)
  let q₀ : ℝ := ((1/1024)^16)/2
  have hq : 0 < q₀ := by dsimp [q₀]; positivity
  have hq1 : q₀ < 1 := by dsimp [q₀]; norm_num
  let S := max 2 (max |m₀-a*b| |a| / η)
  let D := (η+2*|a|+1)/m₀
  obtain ⟨k,hk,hs,hd,hBK⟩ := actual_spatial_witness_BK_scales henv b q₀ η hb hq hq1 hη 0 S D
  let m := characteristicExponent P τ μ b q₀ k
  have hpow : (characteristicLength P τ μ b q₀ k : ℝ)=(2 : ℝ)^m := by
    simp [characteristicLength,m]
  rw [hpow] at hd
  have hs2 : 2 ≤ (2 : ℝ)^k := (le_max_left _ _).trans hs
  have hsC : max |m₀-a*b| |a| / η ≤ (2 : ℝ)^k := (le_max_right _ _).trans hs
  obtain ⟨hstep,hscale₁,hscale₂⟩ := witness_scale_inequalities b m₀ am ap η ((2 : ℝ)^k) ((2 : ℝ)^m)
    (norm_direction_pos μ actualSourceTimeConstant_norm b) hη hη1 hs2 hsC hd
  refine ⟨k,m,hs2,hstep,hscale₁,hscale₂,?_⟩
  intro is
  have hh := hBK is
  have he : 2*q₀=((1 : ℝ)/1024)^16 := by dsimp [q₀]; ring
  rw [he] at hh
  exact hh

end PlanarFPP

end OAI
