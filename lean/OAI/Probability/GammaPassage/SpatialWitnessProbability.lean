import OAI.Probability.GammaPassage.SpatialRareProbability
import OAI.Probability.GammaPassage.BKContinuous

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Actual spatial path witnesses obey BK for every finite list of indices,
including repeated indices and overlapping boxes. -/
theorem gamma_spatial_witness_BK (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b m₀ am ap K η p₀ : ℝ) (hp₀ : 0 ≤ p₀) (k m : ℕ)
    (hrare : ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b m₀ am ap K η k m ih} ≤ p₀)
    (is : List (ℤ×ℤ)) :
    P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ p₀^is.length := by
  let _ := henv.probability
  let S := spatialListSupport b k m is
  have hsingle (ih : ℤ×ℤ) : P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
      (fun e => τ e ω)} ≤ p₀ := by
    apply (measureReal_mono (μ := P) (s₂ := {ω | (fun e => τ e ω) ∈
      spatialRareEvent b m₀ am ap K η k m ih}) ?_).trans (hrare ih)
    rintro ω ⟨p,hp,_he,hg⟩
    exact spatialWitness_good_event b m₀ am ap K η k m ih p hp _ hg
  apply (GammaFPP.BK.gamma_strict_path_BK henv hshape hrate S (is.map (spatialWitnessFamily b m₀ am ap K η k m))).trans
  simp only [List.map_map]
  have hprod (js : List (ℤ×ℤ)) :
      (js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
        (fun e => τ e ω)})).prod ≤ p₀^js.length := by
    induction js with
    | nil => simp
    | cons i js ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
      calc
        _ ≤ p₀*(js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
          (fun e => τ e ω)})).prod := mul_le_mul_of_nonneg_right (hsingle i) (List.prod_nonneg (by intro a ha; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact measureReal_nonneg))
        _ ≤ p₀*p₀^js.length := mul_le_mul_of_nonneg_left ih hp₀
        _ = _ := by ring
  exact hprod is

/-- The finite-list bound with the rare-event probabilities supplied by the
actual model, at one common scale for every list of spatial indices. -/
theorem gamma_spatial_witness_BK_scales (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k : ℝ) ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths
        (spatialListSupport b k (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) is)
        (is.map (spatialWitnessFamily b ((gammaMeanNorm henv hshape hrate) (direction b))
          (extremeSlope (gammaMeanNorm henv hshape hrate) b false) (extremeSlope (gammaMeanNorm henv hshape hrate) b true)
          (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k
          (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k))) (fun e => τ e ω)} ≤
        (2*q₀)^is.length := by
  obtain ⟨k,hk,hs,hd,hrare⟩ := gamma_spatial_rare_scales henv hshape hrate b q₀ η hb hq hq1 hη N S D
  refine ⟨k,hk,hs,hd,?_⟩
  intro is
  exact gamma_spatial_witness_BK henv hshape hrate b _ _ _ _ η (2*q₀) (by positivity) k
    (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) hrare is

end GammaFPP.CrossingBridge

end OAI
