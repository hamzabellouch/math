import OAI.Probability.GammaPassage.WitnessBorelCantelli
import OAI.Probability.GammaPassage.SpatialWitnessProbability

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open MeasureTheory Filter

/-- All three source deterministic inequalities follow from explicit scale
cutoffs. The crossing constant is the manuscript's 100(1+|a-|+|a+|). -/
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

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Construct one genuine characteristic scale satisfying both the deterministic
source constraints and actual spatial BK with an explicit entropy parameter. -/
theorem gamma_witness_scale (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b η : ℝ)
    (hb : |b| ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ k m : ℕ, 2 ≤ (2 : ℝ)^k ∧
      max |(gammaMeanNorm henv hshape hrate) (direction b)-
        ((extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2)*b|
        |(extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2| ≤ η*(2 : ℝ)^k ∧
      η*(2 : ℝ)^k < 2*(gammaMeanNorm henv hshape hrate) (direction b)*(2 : ℝ)^m-
        |(extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2| *((2 : ℝ)^k+1) ∧
      3*η*(2 : ℝ)^k+2*|(extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2| *((2 : ℝ)^k+1)
        < sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b*(2 : ℝ)^k ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
        (is.map (spatialWitnessFamily b ((gammaMeanNorm henv hshape hrate) (direction b))
          (extremeSlope (gammaMeanNorm henv hshape hrate) b false) (extremeSlope (gammaMeanNorm henv hshape hrate) b true)
          (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k m)) (fun e => τ e ω)} ≤
        (((1 : ℝ)/1024)^16)^is.length := by
  let μ := (gammaMeanNorm henv hshape hrate)
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  let a := (am+ap)/2
  let m₀ := μ (direction b)
  let q₀ : ℝ := ((1/1024)^16)/2
  have hq : 0 < q₀ := by dsimp [q₀]; positivity
  have hq1 : q₀ < 1 := by dsimp [q₀]; norm_num
  let S := max 2 (max |m₀-a*b| |a| / η)
  let D := (η+2*|a|+1)/m₀
  obtain ⟨k,hk,hs,hd,hBK⟩ := gamma_spatial_witness_BK_scales henv hshape hrate b q₀ η hb hq hq1 hη 0 S D
  let m := characteristicExponent P τ shape rate μ b q₀ k
  have hpow : (characteristicLength P τ shape rate μ b q₀ k : ℝ)=(2 : ℝ)^m := by
    simp [characteristicLength,m]
  rw [hpow] at hd
  have hs2 : 2 ≤ (2 : ℝ)^k := (le_max_left _ _).trans hs
  have hsC : max |m₀-a*b| |a| / η ≤ (2 : ℝ)^k := (le_max_right _ _).trans hs
  obtain ⟨hstep,hscale₁,hscale₂⟩ := witness_scale_inequalities b m₀ am ap η ((2 : ℝ)^k) ((2 : ℝ)^m)
    (norm_direction_pos μ (gammaMeanNorm_laws henv hshape hrate) b) hη hη1 hs2 hsC hd
  have hK : 100*(1+|am|+|ap|) ≤ sourceCrossingK shape rate μ b := by
    dsimp [am,ap]
    unfold sourceCrossingK
    nlinarith [abs_nonneg (coordinateAllowance shape rate)]
  have hscale₂Gamma := hscale₂.trans_le
    (mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ 2^k))
  refine ⟨k,m,hs2,hstep,hscale₁,hscale₂Gamma,?_⟩
  intro is
  have hh := hBK is
  have he : 2*q₀=((1 : ℝ)/1024)^16 := by dsimp [q₀]; ring
  rw [he] at hh
  exact hh

end GammaFPP.CrossingBridge

end OAI
