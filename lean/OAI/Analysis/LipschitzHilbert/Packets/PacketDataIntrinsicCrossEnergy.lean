import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniformCrossEnergy
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataJetControl

namespace OAI

/-! The actual cross-profile energy is independent of the auxiliary
jet scale. Its polynomial exponent is fixed before the mask exponent. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_cross_energy (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
    ∀ (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width), ∀ L p : ℝ, 2≤L → 0≤p → d.unitModelCost CD CS CT≤L →
    ordinaryDensityUpper^(1/4:ℝ)≤L → (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∫ z, ‖∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q‖^2
        ∂volume.prod volume)≤(L^(3*p+6))^2*(volume.prod volume).real E := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_uniform_cross_energy hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofile S hS g hg hg1 E hE hEfin hgs u hu
  let Q := P.withJetControl 0 1 (by norm_num) (by simp)
  let dq := d.withJetControl 0 1 (by norm_num) (by simp)
  have hb : P.profileBound≤(2^P.order*P.profileBound)*3^(2*P.order) := by
    have h₂ : (1:ℝ)≤2^P.order := one_le_pow₀ (by norm_num)
    have h₃ : (1:ℝ)≤3^(2*P.order) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 2^P.order*P.profileBound := le_mul_of_one_le_left P.profileBound_pos.le h₂
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by norm_num) _) P.profileBound_pos.le) h₃
  have hprofileQ : Q.profileBound≤L^p := hb.trans hprofile
  have habsoluteQ : Q.referenceEnvelopeConstant≤L^p := by
    simpa only [Q,referenceEnvelopeConstant,PacketLatticeData.withJetControl,one_pow,mul_one] using hprofile
  have h := hAll N κ Label Item Q initial dq heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofileQ habsoluteQ
    S hS g hg hg1 E hE hEfin hgs u hu
  change (∫ z, ‖∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q‖^2
    ∂volume.prod volume)≤(L^(3*p+6))^2*(volume.prod volume).real E at h
  have he (z : ℝ×ℝ) (q : P.PacketIndex) :
      Q.crossPacketValue alt hAlt 0 d.selector u g z q=
        P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    P.withJetControl_crossPacketValue 0 1 (by norm_num) (by simp)
      alt hAlt 0 d.selector u g z q
  simpa only [he] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI
