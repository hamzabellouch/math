import OAI.Analysis.LipschitzHilbert.Trees.SourceScaledTopGood
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeRawData

namespace OAI

/-! Actual translated sheared lattice packets satisfy the simultaneous
top and covariant-derivative concentration estimate. Only the published
Lepingle input remains in the variation argument. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket

theorem source_lattice_concentration (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hcStar : 0 ≤ cStar) (hCEta : 0 ≤ CEta)
    (hgap : cStar < cEta*cb) (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
        (P : ∀ i, SourceLatticePacket (N i) κ (ι i)), (∀ i, (P i).constant ≤ L^p) →
      ∀ (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ), (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ i j u k ξ η, planarAngularFourier ((P i).physicalPacket (T i).slope j u k) (ξ,η) ≠ 0 →
        |ξ+((T i).slope+(P i).rowSlope j)*η| ≤ cStar/(P i).length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) →
      (∀ i j (_u : ι i j), cb*w/(P i).length j ≤ |(P i).rowSlope j| ∧
        |(P i).rowSlope j| ≤ Cb*w/(P i).length j) →
      (∀ i, SourceLatticeTopGeometry (P i) (T i) (L^a) D) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) ∧
        ∀ i lower upper, lower ≤ upper → upper ≤ N i → ∀ z shift,
          |shift| ≤ (T i).width → z ∉ bad →
          let F := fun x y => planarPacketInterval
            ((P i).family.mainCoefficient (cutoff i) (v i) (g i))
            (fun j u k t s => (P i).raw 0 j u k t s) lower upper x y
          ‖F z.1 ((z.2-(T i).slope*z.1)+shift)‖ +
            (T i).width*‖covariantSignal (P i).frequency (fun k t => F z.1 t k)
              ((z.2-(T i).slope*z.1)+shift)‖ ≤
                L^(2*p+3)*((T i).weight (L^a) (D:ℝ) z)^8 := by
  let lo := (cEta*cb-cStar)/(2*Real.pi)
  let hi := (CEta*Cb+cStar)/(2*Real.pi)
  have hlo : 0 < lo := div_pos (sub_pos.mpr hgap) (by positivity)
  have hhi : 0 ≤ hi := div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  obtain ⟨L0,hL0,hgood⟩ := PlanarPacketFamily.source_scaled_top_good hL hlo hhi
    J a p D hJ ha hp
  refine ⟨L0,hL0,?_⟩
  intro L hL τ κ _ _ N ι _ P hP cutoff v hv g hg hg1 hc T w hw hspectrum hselector G
  let S : ∀ i, SourceLatticeSpectralData (P i) := fun i => {
    referenceSlope := (T i).slope
    w := w
    cStar := cStar
    cEta := cEta
    CEta := CEta
    cb := cb
    Cb := Cb
    w_pos := hw
    cEta_pos := hcEta
    cb_nonneg := hcb
    Cb_nonneg := hCb
    spectrum := hspectrum i
    selector := hselector i }
  exact hgood L hL τ κ N ι (fun i => (P i).family) hP cutoff v hv g hg hg1 hc T
    (fun i => (P i).topLength) (fun i => (P i).topLength_pos)
    (fun i => (P i).topRawData (S i) (T i) (L^a) D (G i))
    (fun i => (P i).topCovariantData (S i) (T i) (L^a) D (G i))

end LipschitzHilbert.SourceLatticePacket

end

end OAI
