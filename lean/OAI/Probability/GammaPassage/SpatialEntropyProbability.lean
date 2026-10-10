import OAI.Probability.GammaPassage.SpatialBadPathCover
import OAI.Probability.GammaPassage.Environment

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open Set Finset MeasureTheory Filter
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Source wi:entropy-bound for actual bad paths, using the proved geometric
cover and a same-scale actual spatial BK bound. -/
theorem spatial_bad_path_probability (henv : GammaEnvironment shape rate P τ)
    (_hshape : 0 < shape) (_hrate : 0 < rate)
    (b m₀ am ap K η p₀ : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η) (hp₀ : 0 ≤ p₀)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ p₀^is.length)
    (N : ℕ) (hN : 4 ≤ N) :
    P.real {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N} ≤
      (196 : ℝ)^N*p₀^(N/16) := by
  let _ := henv.probability
  let codes := spatialItineraries 0 N ×ˢ compositionCover N (N/16)
  let E (code : List (ℤ×ℤ) × List ℕ) : Set Ω := {ω |
    (0::code.1).length=code.2.length ∧
    StrictDisjointPaths (spatialListSupport b k m (witnessLabels code.2 (0::code.1)))
      ((witnessLabels code.2 (0::code.1)).map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)}
  have hsub : {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N} ≤ᵐ[P]
      ⋃ code ∈ codes,E code := by
    filter_upwards [henv.ae_positive] with ω hp hbad
    obtain ⟨is,his,ns,hns,hlen,hD⟩ := spatial_bad_path_cover (fun e => τ e ω) (fun e => (hp e).le)
      b m₀ am ap K η hb ha hη hgap k m hs hstep hscale₁ hscale₂ N hN hbad
    exact mem_iUnion₂.mpr ⟨(is,ns),mem_product.mpr ⟨his,hns⟩,hlen,hD⟩
  have hE (code : List (ℤ×ℤ) × List ℕ) (hc : code ∈ codes) : P.real (E code) ≤ p₀^(N/16) := by
    have hcomp := (mem_compositionCover ..).mp (mem_product.mp hc).2
    by_cases hlen : (0::code.1).length=code.2.length
    · have hl := witnessLabels_length code.2 (0::code.1) hlen.symm
      rw [hcomp.2] at hl
      have hh := hBK (witnessLabels code.2 (0::code.1))
      rw [hl] at hh
      have hEC : E code ⊆ {ω | StrictDisjointPaths
          (spatialListSupport b k m (witnessLabels code.2 (0::code.1)))
          ((witnessLabels code.2 (0::code.1)).map (spatialWitnessFamily b m₀ am ap K η k m))
          (fun e => τ e ω)} := by
        intro ω hω
        exact hω.2
      exact (measureReal_mono (μ := P) hEC).trans hh
    · have he : E code=∅ := by
        ext ω
        exact ⟨fun h => (hlen h.1).elim,False.elim⟩
      rw [he,measureReal_empty]
      positivity
  have hcard : (codes.card : ℝ) ≤ (196 : ℝ)^N := by
    have hc : codes.card ≤ 196^N := by
      calc
        _ = (spatialItineraries 0 N).card*(compositionCover N (N/16)).card := card_product ..
        _ ≤ 49^N*4^N := Nat.mul_le_mul (spatialItineraries_card 0 N)
          (compositionCover_card N (N/16) (Nat.div_le_self ..))
        _ = 196^N := by rw [← mul_pow]; norm_num
    exact_mod_cast hc
  calc
    _ ≤ P.real (⋃ code ∈ codes,E code) := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
    _ ≤ ∑ code ∈ codes,P.real (E code) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _code ∈ codes,p₀^(N/16) := sum_le_sum hE
    _ = (codes.card : ℝ)*p₀^(N/16) := by simp
    _ ≤ (196 : ℝ)^N*p₀^(N/16) := mul_le_mul_of_nonneg_right hcard (by positivity)

end GammaFPP.CrossingBridge

end OAI
