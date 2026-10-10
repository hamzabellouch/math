import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationCenteredFamily
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedConcentrationFamily
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationCentered
import OAI.Analysis.LipschitzHilbert.Trees.SourcePolarizedInterval

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

private def centeredPhaseCutoff (t : ℝ) (d : Fin N → ℝ) (phase : Fin 3) : Fin N → ℝ :=
  if phase=0 then (fun j => t+d j) else if phase=1 then (fun j => d j-t) else fun _ => 0

private def centeredPhaseField (t : ℝ) (v : ℝ×ℝ → ℝ) (phase : Fin 3) : ℝ×ℝ → ℝ :=
  if phase=0 then (fun z => v (sourceReferenceToPhysical t z))
  else if phase=1 then (fun z => -v (sourceReferenceToPhysical t z)) else fun _ => 0

theorem source_frozen_centered_family_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb)
    (J a p : ℝ) (D : ℕ) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 3 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ top, Fin (N top) → Type) [∀ top j, Fintype (ι top j)]
        (P : ∀ top, SourceLatticePacket (N top) κ (ι top)),
      (∀ top, (P top).constant ≤ L^p) →
      ∀ (c : ∀ top j, ι top j → κ → ℂ) (hc : ∀ top j u k, ‖c top j u k‖ ≤ 1)
        (alt : ∀ top j, ι top j → κ → SchwartzMap (ℝ×ℝ) ℂ)
        (hAlt : ∀ top j u k,
          planarProfileConstant (alt top j u k) (2*(P top).order) ≤ (P top).profileBound)
        (d : ∀ top, Fin (N top) → ℝ), (∀ top j, 0 ≤ d top j) →
      ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
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
      (∀ top, SourceSupportedLatticeTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
            (((P top).frozenProfile (c top) (hc top)).physicalCenteredCoefficient
              (T top).slope (T top).slope (d top) (v top) (g top)) 0 lower upper x y
          ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+
            (T top).width*‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Lt,_hLt,hgood⟩ := source_frozen_jet_family_concentration_of_supported hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap (J+1) a p D (by linarith) ha hp
  refine ⟨max 3 Lt,le_max_left _ _,?_⟩
  intro L hLL τ κ _ _ N ι _ P hP c hc alt hAlt d hd v hv g hg hg1 hmono
    T w hw hspectrum haltSpectrum hselector G
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hLL
  have hLpos : 0 < L := by linarith
  have hK : 1 ≤ L^a := Real.one_le_rpow (by linarith) ha
  let cutoff := fun q : τ×Fin 3 => centeredPhaseCutoff (T q.1).slope (d q.1) q.2
  let field := fun q : τ×Fin 3 => centeredPhaseField (T q.1).slope (v q.1) q.2
  let test := fun q : τ×Fin 3 => fun z => g q.1 (sourceReferenceToPhysical (T q.1).slope z)
  have hfield q : Measurable (field q) := by
    rcases q with ⟨top,phase⟩
    fin_cases phase
    · exact (hv top).comp (sourceReferenceToPhysical (T top).slope).measurable
    · exact ((hv top).comp (sourceReferenceToPhysical (T top).slope).measurable).neg
    · exact measurable_const
  have htest q : Measurable (test q) :=
    (hg q.1).comp (sourceReferenceToPhysical (T q.1).slope).measurable
  have hcut q : Monotone (cutoff q) := by
    rcases q with ⟨top,phase⟩
    fin_cases phase
    · exact centered_upper_monotone (T top).slope (hmono top)
    · exact centered_lower_monotone (T top).slope (hmono top)
    · exact fun _ _ _ => le_rfl
  obtain ⟨bad,hbad,harea,hpoint⟩ := hgood L ((le_max_right _ _).trans hLL)
    (τ×Fin 3) κ (fun q => N q.1) (fun q => ι q.1) (fun q => P q.1) (fun q => hP q.1)
    (fun q => c q.1) (fun q => hc q.1) (fun q => alt q.1) (fun q => hAlt q.1)
    cutoff field hfield test htest (fun q z => hg1 q.1 _) hcut
    (fun q => T q.1) w hw (fun q => hspectrum q.1) (fun q => haltSpectrum q.1)
    (fun q => hselector q.1) (fun q => G q.1)
  refine ⟨bad,hbad,?_,?_⟩
  · have hexp : 3*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
      have hthree : 3 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
      calc
        _ ≤ Real.exp L*Real.exp (-(J+1)*L) :=
          mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hsum : (∑ q : τ×Fin 3, (T q.1).area) = 3*(∑ top, (T top).area) := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_three]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum] at harea
    exact harea.trans (ENNReal.ofReal_le_ofReal (by
      have hS : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
      nlinarith [mul_le_mul_of_nonneg_right hexp hS]))
  · intro top lower upper hlu hu z shift hshift hout
    let Q := (P top).withProfile (alt top) (hAlt top)
    let coeff := ((P top).frozenProfile (c top) (hc top)).physicalCenteredCoefficient
      (T top).slope (T top).slope (d top) (v top) (g top)
    let y := z.2-(T top).slope*z.1+shift
    let bound := L^(2*p+2)*((T top).weight (L^a) (D:ℝ) z)^8
    have hshift' : |shift| ≤ L^a*(T top).width :=
      hshift.trans (le_mul_of_one_le_left (T top).width_pos.le hK)
    have hphase (phase : Fin 3) (i : Fin 2) :
        ‖Q.rawInterval
          (((P top).frozenProfile (c top) (hc top)).physicalCoefficient (T top).slope
            (cutoff (top,phase))
            (if phase=0 then v top else if phase=1 then fun z => -v top z else fun _ => 0)
            (g top)) (i.castLE (by decide)) lower upper z.1 y‖ ≤ bound := by
      rw [(P top).frozen_physical_rawInterval_eq_reference (c top) (hc top) (alt top) (hAlt top)]
      have h := hpoint (top,phase) i lower upper hlu hu z shift hshift' hout
      fin_cases phase <;> simpa [Q,rawInterval,cutoff,field,test,centeredPhaseCutoff,centeredPhaseField,y,bound] using h
    have hjet (i : Fin 2) : ‖Q.rawInterval coeff (i.castLE (by decide)) lower upper z.1 y‖ ≤ 3*bound := by
      rw [(P top).frozen_centered_rawInterval_eq (c top) (hc top) (alt top) (hAlt top)
        (T top).slope (d top) (hd top) (v top) (hv top) (g top) (hg top) (hg1 top)]
      apply (norm_sub_le _ _).trans
      apply (add_le_add (norm_add_le _ _) le_rfl).trans
      have h0 := hphase 0 i
      have h1 := hphase 1 i
      have h2 := hphase 2 i
      simp [cutoff,centeredPhaseCutoff] at h0 h1 h2
      linarith
    have hcov := Q.rawInterval_scaled_covariant coeff lower upper z.1 y
    have hcovnorm := congrArg norm hcov
    rw [norm_smul,Real.norm_eq_abs] at hcovnorm
    have hscale : (T top).width ≤ |Q.scale| := by
      change (T top).width ≤ |(P top).scale|
      rw [(G top).scale_eq,abs_of_pos (mul_pos (by norm_num : (0:ℝ) < 4)
        (mul_pos (Real.rpow_pos_of_pos hLpos a) (T top).width_pos))]
      nlinarith [(T top).width_pos]
    have hderiv : (T top).width*‖covariantSignal (P top).frequency
        (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ ≤ 3*bound := by
      calc
        _ ≤ |Q.scale| * ‖covariantSignal Q.frequency
          (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ :=
          mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
        _ = ‖Q.rawInterval coeff 1 lower upper z.1 y‖ := hcovnorm
        _ ≤ _ := hjet 1
    have hpoly : 6*bound ≤ L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 := by
      have hp2 : 6 ≤ L^2 := by nlinarith
      have hbnonneg : 0 ≤ bound := by dsimp [bound]; positivity
      calc
        _ ≤ L^2*bound := mul_le_mul_of_nonneg_right hp2 hbnonneg
        _ = _ := by
          dsimp [bound]
          rw [← mul_assoc,← Real.rpow_natCast L 2,← Real.rpow_add hLpos]
          congr 2
          ring
    exact (add_le_add (hjet 0) hderiv).trans (by linarith)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
