import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniformReverseDisparity
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossPairingBound
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReverseCost

namespace OAI

/-! Uniform reverse-disparity control of the distinct-profile form.
All constants are chosen before the finite translated lattice. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_uniform_cross_reverse_disparity (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (bound : ℝ), 1≤bound → P.profileBound≤bound → P.referenceEnvelopeConstant≤bound →
    ∀
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width)  ,
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ),
      Measurable f → (∀ z, ‖f z‖≤1) → Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (F E : Set (ℝ×ℝ)), MeasurableSet F → (volume.prod volume) F≠∞ →
      MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉F → f z=0) → (∀ z, z∉E → g z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      Integrable (fun z => inner ℂ
        (∑ q∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z q)
        (f z) ∂volume.prod volume‖≤
        (d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper*(2*bound)^4)*
          Real.sqrt ((volume.prod volume).real F*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real F)^(9/20:ℝ) := by
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_reverse_disparity hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅
    bound hb hprofile habsolute alt hAlt hSpectrum hMargin hBin
    f g hfm hf1 hgm hg1 F E hF hFfin hE hEfin hfs hgs u hu
  have hf := (bounded_supported_input f hfm hf1 F hF hFfin hfs).1
  have hg := (bounded_supported_input g hgm hg1 E hE hEfin hgs).1
  let weight := Real.sqrt ((volume.prod volume).real F*(volume.prod volume).real E)*
    ((volume.prod volume).real E/(volume.prod volume).real F)^(9/20:ℝ)
  have hw : 0≤weight := by dsimp only [weight]; positivity
  let C := d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper*(2*bound)^4
  have h := P.cross_pairing_bound alt hAlt initial d.selector d.measurable d.bounded
    u hu g f hgm hg1 hf (C*weight) (by
    intro c hc
    let Q := P.polarize alt hAlt c hc
    let dp := d.polarize alt hAlt c hc hSpectrum hMargin hBin
    have hrev := hAll N κ Label Item Q initial dp heq₁ heq₂ heq₃ heq₄ heq₅
      f hfm hf1 F hF hFfin hfs E hE hEfin u hu
    have hcost : dp.reverseModelCost CD CS CT CZ ordinaryDensityUpper≤C := by
      have hprofileQ : Q.profileBound≤2*bound :=
        mul_le_mul_of_nonneg_left hprofile (by norm_num)
      have habsoluteEq : Q.referenceEnvelopeConstant=2*P.referenceEnvelopeConstant := by
        dsimp only [Q,polarize,referenceEnvelopeConstant]
        ring
      have habsoluteQ : Q.referenceEnvelopeConstant≤2*bound := by
        rw [habsoluteEq]
        exact mul_le_mul_of_nonneg_left habsolute (by norm_num)
      exact dp.reverseModelCost_le_quartic CD CS CT CZ ordinaryDensityUpper (2*bound)
        hCS.le hCZ.le (by linarith) hprofileQ habsoluteQ
    have hselector : dp.selector=d.selector := rfl
    have hi : IntegrableOn (Q.ordinaryForwardSum initial d.selector u f) E (volume.prod volume) := hrev.1
    have hp := (Q.ordinary_adjoint_pairing_bound initial d.selector d.measurable d.bounded
      u hu f g hf hg hgm hg1 E hE hgs hi).2
    apply hp.trans
    calc
      _ ≤ dp.reverseModelCost CD CS CT CZ ordinaryDensityUpper*weight := by
        simpa only [weight,ordinaryForwardSum,hselector,mul_assoc] using hrev.2
      _ ≤ C*weight := mul_le_mul_of_nonneg_right hcost hw)
  refine ⟨h.1,?_⟩
  simpa only [C,weight,mul_assoc] using h.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
