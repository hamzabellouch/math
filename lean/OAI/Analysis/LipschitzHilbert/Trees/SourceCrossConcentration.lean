import OAI.Analysis.LipschitzHilbert.Trees.SourcePolarizedInterval

namespace OAI

/-! The manuscript's cross-profile top concentration estimate follows
from the four genuine self-profile families, on one exceptional set. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket

theorem source_cross_concentration (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hcStar : 0 ≤ cStar) (hCEta : 0 ≤ CEta)
    (hgap : cStar < cEta * cb) (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
        (P : ∀ i, SourceLatticePacket (N i) κ (ι i)), (∀ i, (P i).constant ≤ L ^ p) →
      ∀ (alt : ∀ i j, ι i j → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ i j u k,
          planarProfileConstant (alt i j u k) (2 * (P i).order) ≤ (P i).profileBound)
        (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ),
      (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ i j u k ξ η, planarAngularFourier ((P i).physicalPacket (T i).slope j u k) (ξ, η) ≠ 0 →
        |ξ + ((T i).slope + (P i).rowSlope j) * η| ≤ cStar / (P i).length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta) →
      (∀ i j u k ξ η,
        planarAngularFourier (((P i).withProfile (alt i) (hAlt i)).physicalPacket
          (T i).slope j u k) (ξ, η) ≠ 0 →
        |ξ + ((T i).slope + (P i).rowSlope j) * η| ≤ cStar / (P i).length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta) →
      (∀ i j (_u : ι i j), cb * w / (P i).length j ≤ |(P i).rowSlope j| ∧
        |(P i).rowSlope j| ≤ Cb * w / (P i).length j) →
      (∀ i, SourceLatticeTopGeometry (P i) (T i) (L ^ a) D) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J * L) * (∑ i, (T i).area)) ∧
        ∀ i lower upper, lower ≤ upper → upper ≤ N i → ∀ z shift,
          |shift| ≤ (T i).width → z ∉ bad →
          let F := fun x y => planarPacketInterval
            ((P i).family.mainCoefficient (cutoff i) (v i) (g i))
            (fun j u k t s => ((P i).withProfile (alt i) (hAlt i)).raw 0 j u k t s) lower upper x y
          ‖F z.1 ((z.2 - (T i).slope * z.1) + shift)‖ +
            (T i).width * ‖covariantSignal (P i).frequency (fun k t => F z.1 t k)
              ((z.2 - (T i).slope * z.1) + shift)‖ ≤
                L ^ (2 * p + 5) * ((T i).weight (L ^ a) (D : ℝ) z) ^ 8 := by
  obtain ⟨L0, hL0, hgood⟩ := source_four_polarized_concentration hL
    cStar cEta CEta cb Cb hcEta hcb hCb hcStar hCEta hgap J a p D hJ ha hp
  refine ⟨L0, hL0, ?_⟩
  intro L hLL τ κ _ _ N ι _ P hP alt hAlt cutoff v hv g hg hg1 hcut T w hw hspectrum haltSpectrum hselector G
  obtain ⟨bad, hbad, harea, hpoint⟩ := hgood L hLL τ κ N ι P hP
    alt hAlt cutoff v hv g hg hg1 hcut T w hw hspectrum haltSpectrum hselector G
  refine ⟨bad, hbad, harea, ?_⟩
  intro i lower upper hlu hu z shift hshift hout
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hL0.trans hLL)
  have hs : (P i).scale ≠ 0 := by
    rw [(G i).scale_eq]
    exact ne_of_gt (mul_pos (by norm_num) (mul_pos (Real.rpow_pos_of_pos hLp _) (T i).width_pos))
  apply (P i).cross_interval_joint_bound (alt i) (hAlt i) hs
    (cutoff i) (v i) (hv i) (g i) (hg i) (hg1 i) lower upper
    z.1 ((z.2 - (T i).slope * z.1) + shift) (T i).width
    (L ^ (2 * p + 5) * ((T i).weight (L ^ a) (D : ℝ) z) ^ 8) (T i).width_pos.le
  intro phase
  exact hpoint i phase lower upper hlu hu z shift hshift hout

end LipschitzHilbert.SourceLatticePacket

end

end OAI
