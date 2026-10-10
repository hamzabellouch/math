import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLabeledGeometry
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationMainSlots
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedConcentrationCentered
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMainSlots
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedConcentration

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem source_labeled_centered_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb)
    (J a p : ℝ) (D B : ℕ) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 3 ≤ L0 ∧ (B:ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top))
      (_hcard : ∀ top j, ((P top).labels j).card ≤ B),
      (∀ top, (P top).constant ≤ L^p) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ)
      (_hb : ∀ top j l k, ‖b top j l k (0:ℝ)‖ ≤ 1),
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (angle : τ → ℝ), (∀ top, 0 ≤ angle top) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
    ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ top j l u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j (l : (P top).labels j) (_u : Item top j l),
        cb*w/(P top).length j ≤ |(P top).rowSlope j l| ∧
          |(P top).rowSlope j l| ≤ Cb*w/(P top).length j) →
      (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
            ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
              (fun j l k _ => b top j l k 0) (v top) (g top)) 0 lower upper x y
          ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+
            (T top).width*‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+5)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Lt,hLt,hconc⟩ := SourceLatticePacket.source_frozen_centered_family_concentration_of_supported hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap (J+1) a p D (by linarith) ha hp
  refine ⟨max Lt B,hLt.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro L hLL τ κ _ _ N Label Item _ P hcard hP b hb alt hAlt angle hangle
    v hv g hg hg1 T w hw hspectrum haltSpectrum hselector G
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans hLL)
  have hBL : (B:ℝ) ≤ L := (le_max_right _ _).trans hLL
  let Item' := fun q : τ×Fin B => (P q.1).SlotItem (hcard q.1) q.2
  let P' := fun q : τ×Fin B => (P q.1).slotted (hcard q.1) q.2
  let alt' := fun q : τ×Fin B => (P q.1).slottedAlt (hcard q.1) (alt q.1) q.2
  let hAlt' := fun q : τ×Fin B =>
    (P q.1).slottedAlt_bound (hcard q.1) (alt q.1) (hAlt q.1) q.2
  let c := fun (q : τ×Fin B) j (u : Item' q j) k => b q.1 j u.1.1 k 0
  have hspec (q : τ×Fin B) := (P q.1).slotted_spectrum (hcard q.1) (T q.1).slope w cStar cEta CEta
    (hspectrum q.1) q.2
  have haltSpec : ∀ q j u k xi eta,
      planarAngularFourier (((P' q).withProfile (alt' q) (hAlt' q)).physicalPacket
        (T q.1).slope j u k) (xi,eta) ≠ 0 →
      |xi+((T q.1).slope+(P' q).rowSlope j)*eta| ≤ cStar/(P' q).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro q j u k xi eta hn
    rw [(P q.1).slotted_alt_physicalPacket (hcard q.1) (alt q.1) (hAlt q.1)] at hn
    simpa only [P',slotted_length,(P q.1).slotted_rowSlope (hcard q.1) q.2 j u] using
      haltSpectrum q.1 j u.1.1 u.1.2 k xi eta hn
  obtain ⟨bad,hbad,harea,hpoint⟩ := hconc L ((le_max_left _ _).trans hLL)
    (τ×Fin B) κ (fun q => N q.1) Item' P'
    (fun q => by simpa only [P',slotted_constant] using hP q.1)
    c (fun q j u k => hb q.1 j u.1.1 k) alt' hAlt'
    (fun q j => angle q.1*(2:ℝ)^j.val)
    (fun q j => mul_nonneg (hangle q.1) (pow_nonneg (by norm_num) _))
    (fun q => v q.1) (fun q => hv q.1) (fun q => g q.1) (fun q => hg q.1)
    (fun q => hg1 q.1)
    (fun q i j hij => mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) (hangle q.1))
    (fun q => T q.1) w hw hspec haltSpec
    (fun q => (P q.1).slotted_selector (hcard q.1) w cb Cb (hselector q.1) q.2)
    (fun q => (P q.1).slotted_supportedTopGeometry (hcard q.1) (G q.1) q.2)
  refine ⟨bad,hbad,harea.trans (ENNReal.ofReal_le_ofReal ?_),?_⟩
  · have hsum : (∑ q : τ×Fin B, (T q.1).area) = (B:ℝ)*(∑ top, (T top).area) := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← Finset.mul_sum]
    rw [hsum]
    have he : (B:ℝ) ≤ Real.exp L := hBL.trans (by linarith [Real.add_one_le_exp L])
    have hd : (B:ℝ)*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
      calc
        _ ≤ Real.exp L*Real.exp (-(J+1)*L) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hs : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
    nlinarith [mul_le_mul_of_nonneg_right hd hs]
  · intro top lower upper hlu hu z shift hshift hout
    dsimp only
    let Q := (P top).withProfile (alt top) (hAlt top)
    let coeff := (P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
      (fun j l k _ => b top j l k 0) (v top) (g top)
    let y := z.2-(T top).slope*z.1+shift
    let F := fun s : Fin B => (Q.slotted (hcard top) s).rawInterval
      (fun j u => coeff j u.1.1 u.1.2) 0 lower upper z.1
    have hF (s : Fin B) (yy : ℝ) :
        ((P' (top,s)).withProfile (alt' (top,s)) (hAlt' (top,s))).rawInterval
          (((P' (top,s)).frozenProfile (c (top,s))
            (fun j u k => hb top j u.1.1 k)).physicalCenteredCoefficient
            (T top).slope (T top).slope (fun j => angle top*(2:ℝ)^j.val) (v top) (g top))
          0 lower upper z.1 yy = F s yy :=
      (P top).frozenSlot_rawInterval (hcard top) (T top).slope (angle top)
        (fun j l k _ => b top j l k 0) (fun j l k => hb top j l k)
        (alt top) (hAlt top) (v top) (g top) s 0 lower upper z.1 yy
    have hb' (s : Fin B) : ‖F s y‖+(T top).width*
        ‖covariantSignal (P top).frequency (fun k yy => F s yy k) y‖ ≤
        L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 := by
      have h := hpoint (top,s) lower upper hlu hu z shift hshift hout
      let A := fun yy => ((P' (top,s)).withProfile (alt' (top,s)) (hAlt' (top,s))).rawInterval
        (((P' (top,s)).frozenProfile (c (top,s))
          (fun j u k => hb top j u.1.1 k)).physicalCenteredCoefficient
          (T top).slope (T top).slope (fun j => angle top*(2:ℝ)^j.val) (v top) (g top))
        0 lower upper z.1 yy
      have hf : A = F s := funext (hF s)
      change ‖A y‖+(T top).width*‖covariantSignal (P top).frequency (fun k yy => A yy k) y‖ ≤ _ at h
      rw [hf] at h
      exact h
    have hscale : Q.scale ≠ 0 := by
      change (P top).scale ≠ 0
      rw [(G top).scale_eq]
      exact ne_of_gt (mul_pos (by norm_num) (mul_pos (Real.rpow_pos_of_pos hLpos _) (T top).width_pos))
    have hs := Q.sum_slotted_rawInterval (hcard top) coeff 0 lower upper z.1 y
    have hd := Q.sum_slotted_covariant (hcard top) hscale coeff lower upper z.1 y
    have hn : ‖∑ s, F s y‖+(T top).width*
        ‖∑ s, covariantSignal (P top).frequency (fun k yy => F s yy k) y‖ ≤
        (B:ℝ)*(L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8) := by
      calc
        _ ≤ (∑ s, ‖F s y‖)+(T top).width*
            (∑ s, ‖covariantSignal (P top).frequency (fun k yy => F s yy k) y‖) :=
          add_le_add (norm_sum_le _ _) (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (T top).width_pos.le)
        _ = ∑ s, (‖F s y‖+(T top).width*
            ‖covariantSignal (P top).frequency (fun k yy => F s yy k) y‖) := by
          rw [Finset.sum_add_distrib,Finset.mul_sum]
        _ ≤ ∑ _s : Fin B, L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 :=
          Finset.sum_le_sum fun s _ => hb' s
        _ = _ := by simp
    rw [hs,hd] at hn
    apply hn.trans
    have hpowers : L*L^(2*p+4) = L^(2*p+5) := by
      rw [show 2*p+5 = 1+(2*p+4) by ring,Real.rpow_add hLpos (1:ℝ) (2*p+4),Real.rpow_one]
    calc
      _ = ((B:ℝ)*L^(2*p+4))*((T top).weight (L^a) (D:ℝ) z)^8 := by ring
      _ ≤ (L*L^(2*p+4))*((T top).weight (L^a) (D:ℝ) z)^8 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hLpos.le _)) (by positivity)
      _ = _ := by rw [hpowers]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
