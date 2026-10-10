import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedAnalyzedGlobal
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightedPair
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketScaling

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PlanarPacketFamily

theorem constructed_synthesis_global_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone d →
      (∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
      (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
      ∀ (raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (baseX baseZ rx r : ℝ) (q : ℕ),
      0 < rx → 0 < r → 1 ≤ q → (∀ j (_u : ι j), P.length j ≤ rx) → P.width ≤ r →
      (∀ j u, |P.centerX j u-baseX| ≤ rx) →
      (∀ j u, |P.centerZ j u-baseZ| ≤ r) →
      (∀ i y j u k x, ‖raw i j u k y x‖ ≤ P.constant*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*q) x *
          lineEnvelope (P.centerZ j u) P.width (2+2*q) y)) →
      (∀ i y j u k x, ‖deriv (raw i j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*q) x *
          lineEnvelope (P.centerZ j u) P.width (2+2*q) y)) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (raw i j u k y) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (raw i j u k y) ξ = 0) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => raw 0 j u k t x) y -
        (frequency k:ℂ)*Complex.I*raw 0 j u k y x) = raw 1 j u k y x) →
      (∀ i j u k, Continuous (fun z : ℝ × ℝ => raw i j u k z.1 z.2)) →
      (∀ j u k x y, DifferentiableAt ℝ (fun t => raw 0 j u k t x) y) →
      ∀ n : ℕ, 1 ≤ n →
      let C := topPairConstant P.constant q
      let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) 2
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
          (2*ENNReal.ofReal rx*ENNReal.ofReal (2*r))*ENNReal.ofReal ((4*Real.pi)^2) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w, |w| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval (P.mainCoefficient d v g)
            (fun j u k y x => raw 0 j u k y x) a b x (z+w)‖ ≤
              P.coefficientScale*(256^q*(24*K*(n:ℝ))*
                boxVariationWeight (packetBoxIndex baseX baseZ rx r x z)^(q-1)) := by
  obtain ⟨Ab,Am,hAb,hAm,hglobal⟩ := analyzed_global_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hd hPderiv hPlow hPhigh raw frequency baseX baseZ rx r q
    hrx hr hq hwidth hW hx hz hbound hdbound hlow hhigh hcov hcont hdiff n hn
  let synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ :=
    fun i j u k y => topWeightedPair (fun e => raw e j u k y) baseX rx baseZ r y q i
  have hlen (j : Fin N) (u : ι j) : P.length j ≤ rx := hwidth j u
  have hslow i y j u k ξ hξ : 𝓕 (synth i j u k y) ξ = 0 :=
    topWeightedPair_low (fun e => raw e j u k y) baseX rx baseZ r y q
      (lo*2^j.val) (hi*2^j.val) (fun e => hlow e y j u k) (fun e => hhigh e y j u k) i ξ hξ
  have hshigh i y j u k ξ hξ : 𝓕 (synth i j u k y) ξ = 0 :=
    topWeightedPair_high (fun e => raw e j u k y) baseX rx baseZ r y q
      (lo*2^j.val) (hi*2^j.val) (fun e => hlow e y j u k) (fun e => hhigh e y j u k) i ξ hξ
  have hscov y j u k x : (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
      (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x := by
    simpa [synth, topWeightedPair] using
      topWeightedWave_covariant (raw 0 j u k) (raw 1 j u k)
        baseX rx baseZ r y (frequency k) x q (hdiff j u k x y) (hcov y j u k x)
  have hscont j u k : Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2) := by
    simpa only [synth, topWeightedPair, ↓reduceIte] using
      topWeightedWave_jointContinuous (raw 0 j u k) baseX rx baseZ r q (hcont 0 j u k)
  have hsdiff j u k x y : DifferentiableAt ℝ (fun t => synth 0 j u k t x) y := by
    simpa only [synth, topWeightedPair, ↓reduceIte] using
      topWeightedWave_vertical_differentiable (raw 0 j u k) baseX rx baseZ r x y q (hdiff j u k x y)
  have hsD j u k : Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => synth 0 j u k t z.2) z.1 -
        (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2) := by
    simpa only [synth, topWeightedPair, ↓reduceIte] using
      topWeightedWave_covariant_continuous (raw 0 j u k) (raw 1 j u k)
        baseX rx baseZ r (frequency k) q hr (hcont 0 j u k) (hcont 1 j u k)
          (hdiff j u k) (fun x y => hcov y j u k x)
  obtain ⟨bad,hbad,harea,hpoint⟩ := hglobal N κ ι P d v hv g hg hg1 hPderiv hd hPlow hPhigh
    synth frequency (topPairConstant P.constant q) r (topPairConstant_pos _ _ P.constant_pos) hr
    (fun i y j u k x => topWeightedPair_bound (fun e => raw e j u k y)
      baseX rx baseZ r y (P.centerX j u) (P.length j) (P.centerZ j u) P.width P.constant q 3 2
      (P.length_pos j) hrx P.width_pos hr (hlen j u) hW (hx j u) (hz j u) P.constant_pos.le
      (fun e => hbound e y j u k) i x)
    (fun i y j u k x => topWeightedPair_derivative_bound (fun e => raw e j u k y)
      baseX rx baseZ r y (P.centerX j u) (P.length j) (P.centerZ j u) P.width P.constant q 3 2
      (P.length_pos j) hrx P.width_pos hr (hlen j u) hW (hx j u) (hz j u) P.constant_pos.le
      (fun e => hbound e y j u k) (fun e => hdbound e y j u k) i x)
    hslow hshigh hscov hscont hsdiff hsD
    (fun j u k y x => raw 0 j u k y x) baseX baseZ rx q hrx hq hwidth
    (by
      intro j u k y x
      simp only [synth, topWeightedPair, ↓reduceIte, topWeightedWave_apply])
    2 (by decide) n hn
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb x z w hw hout
  exact planarPacketInterval_denormalize_bound (P.mainCoefficient d v g)
    (fun j u k y x => raw 0 j u k y x) P.coefficientScale _
    P.coefficientScale_pos a b x (z+w) (hpoint a b hab hb x z w hw hout)

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
