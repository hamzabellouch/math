import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationMain
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorFamily
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationJoint
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledActiveCardTail

namespace OAI

/-! Original-selector top concentration. The frozen main part uses only
the active narrow labels; the angular error charges local multiplicity
before convolution. Both pieces retain the original analyzing
coefficients and arbitrary alternate synthesis profiles. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_source_selector_concentration (hL : LepingleInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (rate aWeight p Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
      (∀ top, (P top).absoluteConstant ≤ L^p) →
      (∀ top, 6+2*(8*D+1) ≤ (P top).order) →
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (T : τ → SlopeBox),
      (∀ top, SourceLabeledTopGeometry (P top) (T top) (L^aWeight) D) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => (T top).slope+(P top).rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ),
      (∀ top j l k, Measurable (b top j l k)) →
      (∀ top j l k s, ‖b top j l k s‖ ≤ 1) →
      (∀ top j l k s, b top j l k s ≠ 0 →
        |s-((T top).slope+(P top).rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b top j l k s-b top j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b top j l k s = 0) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
    ∀ (w : ℝ), 0 < w → (∀ top k, |(P top).frequency k| ≤ F/w) →
      (∀ top j l u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, (∃ k, b top j l k (T top).slope ≠ 0) →
        cb*w/(P top).length j ≤ |(P top).rowSlope j l| ∧
          |(P top).rowSlope j l| ≤ Cb*w/(P top).length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
      ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
        |shift| ≤ (T top).width → z ∉ bad →
        let V := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
          ((P top).physicalMultiplierCoefficient (T top).slope (b top) (v top) (g top))
          0 lower upper x y
        ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
          ‖covariantSignal (P top).frequency (fun k y => V z.1 y k)
            (z.2-(T top).slope*z.1+shift)‖ ≤
              L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  obtain ⟨Lt,_hLt,hmain⟩ := source_selector_main_concentration hL
    cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    (rate+1) aWeight p D ((2*K+1)*H) (by linarith) haWeight hp
  filter_upwards [eventually_selector_error_family_concentration
      (rate+1) aWeight p 1 Lip D K H J₀ (by linarith) haWeight hp (by norm_num) hLip,
    eventually_ge_atTop (max 3 Lt)] with L herror hlarge
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hlarge
  have hLpos : 0 < L := by linarith
  intro τ κ _ _ N Label Item _ P hP horder alt hAlt T G angle small wide radius E J
    hangle hsmall hsmall1 hwide hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv g hg hg1 w hw hfreq hspectrum haltSpectrum hselector hJ hE
  classical
  have hcard top j : ((P top).frozenActiveLabels (T top).slope (b top) j).card ≤ (2*K+1)*H :=
    (P top).frozenActiveLabels_card_local (T top).slope (b top) j
      (mul_pos (hangle top) (pow_pos (by norm_num) _)) (hlocal top j) hradius
      (fun l k hk => hsupport top j l k (T top).slope hk)
  obtain ⟨Bmain,hBmain,hAmain,hMpoint⟩ := hmain L ((le_max_right _ _).trans hlarge)
    τ κ N Label Item P hP b T (fun top j l k => hb1 top j l k _) hcard
    alt hAlt angle (fun top => (hangle top).le) v hv g hg hg1 w hw hfreq
    hspectrum haltSpectrum hselector G
  obtain ⟨Berror,hBerror,hAerror,hEpoint⟩ := herror τ κ N Label Item P hP horder
    alt hAlt T G angle small wide radius E J hangle hsmall hsmall1 hwide hwide1 hradius
    hlocal b hb hb1 hsupport hnear hfar v hv g hg hg1 hJ hE
  refine ⟨Bmain∪Berror,hBmain.union hBerror,?_,?_⟩
  · apply (measure_union_le _ _).trans
    apply (add_le_add hAmain hAerror).trans
    rw [← ENNReal.ofReal_add
      (mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun top _ => (T top).area_pos.le))
      (mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun top _ => (T top).area_pos.le))]
    apply ENNReal.ofReal_le_ofReal
    have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have hexp : 2*Real.exp (-(rate+1)*L) ≤ Real.exp (-rate*L) := by
      calc
        _ ≤ Real.exp L*Real.exp (-(rate+1)*L) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hs : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
    nlinarith [mul_le_mul_of_nonneg_right hexp hs]
  · intro top lower upper hlu hu z shift hshift hout
    dsimp only
    have hm := hMpoint top lower upper hlu hu z shift hshift
      (fun h => hout (Or.inl h))
    have he := hEpoint top lower upper z shift hshift (fun h => hout (Or.inr h))
    have hscale : (P top).scale ≠ 0 := by
      rw [(G top).scale_eq]
      exact ne_of_gt (mul_pos (by norm_num) (mul_pos (Real.rpow_pos_of_pos hLpos _) (T top).width_pos))
    have hj := (P top).selector_jointInterval_le (alt top) (hAlt top)
      (T top).slope (angle top) (b top) (hb top) (hb1 top) (v top) (hv top)
      (g top) (hg top) (hg1 top) hscale lower upper hlu (T top).width (T top).width_pos.le
      z.1 (z.2-(T top).slope*z.1+shift)
    apply hj.trans
    apply (add_le_add hm he).trans
    have hpowers : 2*L^(2*p+7) ≤ L^(2*p+8) := by
      calc
        _ ≤ L*L^(2*p+7) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hLpos.le _)
        _ = _ := by
          rw [show 2*p+8 = 1+(2*p+7) by ring,Real.rpow_add hLpos (1:ℝ) (2*p+7),Real.rpow_one]
    have hwpos := pow_nonneg ((T top).weight_pos
      (Real.rpow_pos_of_pos hLpos aWeight) (D:ℝ) z).le 8
    nlinarith [mul_le_mul_of_nonneg_right hpowers hwpos]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
