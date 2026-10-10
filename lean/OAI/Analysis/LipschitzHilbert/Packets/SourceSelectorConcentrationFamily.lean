import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationSpectral
import OAI.Analysis.LipschitzHilbert.Estimates.TopThreshold

namespace OAI

/-! A single physical-plane exception controls both synthesis jets of
every top. The constants and polynomial threshold precede the family. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket

theorem source_frozen_jet_family_concentration (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb)
    (J a p : ℝ) (D : ℕ) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ top, Fin (N top) → Type) [∀ top j, Fintype (ι top j)]
        (P : ∀ top, SourceLatticePacket (N top) κ (ι top)),
      (∀ top, (P top).constant ≤ L^p) →
      ∀ (c : ∀ top j, ι top j → κ → ℂ) (hc : ∀ top j u k, ‖c top j u k‖ ≤ 1)
        (alt : ∀ top j, ι top j → κ → SchwartzMap (ℝ×ℝ) ℂ)
        (hAlt : ∀ top j u k,
          planarProfileConstant (alt top j u k) (2*(P top).order) ≤ (P top).profileBound)
        (d : ∀ top, Fin (N top) → ℝ) (v : τ → ℝ×ℝ → ℝ),
      (∀ top, Measurable (v top)) →
      ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) → (∀ top, Monotone (d top)) →
      ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ top j u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j (_u : ι top j), cb*w/(P top).length j ≤ |(P top).rowSlope j| ∧
        |(P top).rowSlope j| ≤ Cb*w/(P top).length j) →
      (∀ top, SourceLatticeTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top (i : Fin 2) lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ L^a*(T top).width → z ∉ bad →
          ‖planarPacketInterval (((P top).frozenProfile (c top) (hc top)).family.mainCoefficient
              (d top) (v top) (g top))
            (fun j u k y x => ((P top).withProfile (alt top) (hAlt top)).raw
              (i.castLE (by decide)) j u k y x)
            lower upper z.1 ((z.2-(T top).slope*z.1)+shift)‖ ≤
              L^(2*p+2)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Ab,Am,hAb,hAm,hgood⟩ := source_frozen_spectral_jet_neighborhood hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  obtain ⟨Lt,hLt,hthreshold⟩ := exists_top_threshold
    Ab Am (J+1) a p D hAb hAm (by linarith) ha hp
  refine ⟨max 2 Lt,le_max_left _ _,?_⟩
  intro L hLL τ κ _ _ N ι _ P hP c hc alt hAlt d v hv g hg hg1 hd
    T w hw hspectrum haltSpectrum hselector G
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hLL
  have hLtL : Lt ≤ L := (le_max_right _ _).trans hLL
  have hLpos : 0 < L := by linarith
  have hK : 0 < L^a := Real.rpow_pos_of_pos hLpos _
  choose bad hbad harea hpoint using fun top (i : Fin 2) =>
    hgood (N top) κ (ι top) (P top) (c top) (hc top) (alt top) (hAlt top)
      (d top) (v top) (hv top) (g top) (hg top) (hg1 top) (hd top) (T top)
      (L^a) w D hK hw (hspectrum top) (haltSpectrum top) (hselector top) (G top)
      i (J+1) L
  have hsum : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
  have hexp : 2*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
    have htwo : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc
      _ ≤ Real.exp L*Real.exp (-(J+1)*L) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨⋃ top, ⋃ i, bad top i,MeasurableSet.iUnion (fun top => MeasurableSet.iUnion (hbad top)),?_,?_⟩
  · calc
      _ ≤ ∑ top, ∑ i, (volume.prod volume) (bad top i) := by
        apply (measure_iUnion_le _).trans
        simp only [tsum_fintype]
        exact Finset.sum_le_sum fun top _ => by simpa only [tsum_fintype] using measure_iUnion_le (bad top)
      _ ≤ ∑ top, ∑ _i : Fin 2, ENNReal.ofReal (Real.exp (-(J+1)*L)*(T top).area) :=
        Finset.sum_le_sum fun top _ => Finset.sum_le_sum fun i _ => harea top i
      _ = ENNReal.ofReal ((2*Real.exp (-(J+1)*L))*(∑ top, (T top).area)) := by
        simp only [Fin.sum_univ_two]
        have hnonneg (top : τ) : 0 ≤ Real.exp (-(J+1)*L)*(T top).area :=
          mul_nonneg (Real.exp_pos _).le (T top).area_pos.le
        simp_rw [← ENNReal.ofReal_add (hnonneg _) (hnonneg _)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun top _ => add_nonneg (hnonneg top) (hnonneg top))]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hexp hsum)
  · intro top i lower upper hlu hu z shift hshift hout
    have hout' : z ∉ bad top i := fun h => hout (mem_iUnion.mpr ⟨top,mem_iUnion.mpr ⟨i,h⟩⟩)
    exact (hpoint top i lower upper hlu hu z shift hshift hout').trans
      (mul_le_mul_of_nonneg_right
        (hthreshold L hLtL (N top) κ (ι top) (P top).family (hP top)) (by positivity))

end LipschitzHilbert.SourceLatticePacket

end

end OAI
