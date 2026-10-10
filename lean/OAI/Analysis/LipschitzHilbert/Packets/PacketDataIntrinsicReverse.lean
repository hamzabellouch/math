import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniformCrossReverse
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataJetControl

namespace OAI

/-! Reverse disparity with the intrinsic profile budget. The auxiliary
jet parameters are reset before the estimate, and the literal physical
form is transported back unchanged. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_cross_reverse_disparity (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (bound : ℝ), 1≤bound → (2^P.order*P.profileBound)*3^(2*P.order)≤bound →
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
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_cross_reverse_disparity hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ bound hb hbudget
    alt hAlt hSpectrum hMargin hBin f g hfm hf1 hgm hg1 F E hF hFfin hE hEfin hfs hgs u hu
  let Q := P.withJetControl 0 1 (by norm_num) (by simp)
  let dq := d.withJetControl 0 1 (by norm_num) (by simp)
  have hprofile : Q.profileBound≤bound := by
    change P.profileBound≤bound
    have h₂ : (1:ℝ)≤2^P.order := one_le_pow₀ (by norm_num)
    have h₃ : (1:ℝ)≤3^(2*P.order) := one_le_pow₀ (by norm_num)
    apply le_trans _ hbudget
    calc
      _ ≤ 2^P.order*P.profileBound := le_mul_of_one_le_left P.profileBound_pos.le h₂
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg (pow_nonneg (by norm_num) _) P.profileBound_pos.le) h₃
  have habsolute : Q.referenceEnvelopeConstant≤bound := by
    simpa only [Q,referenceEnvelopeConstant,PacketLatticeData.withJetControl,one_pow,mul_one] using hbudget
  have h := hAll N κ Label Item Q initial dq heq₁ heq₂ heq₃ heq₄ heq₅ bound hb
    hprofile habsolute alt hAlt hSpectrum hMargin hBin f g hfm hf1 hgm hg1
    F E hF hFfin hE hEfin hfs hgs u hu
  have he (z : ℝ×ℝ) :
      inner ℂ (∑ a∈initial, Q.crossPacketValue alt hAlt 0 d.selector u g z a) (f z)=
      inner ℂ (∑ a∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z a) (f z) := by
    exact congrArg (fun v => inner ℂ v (f z)) (Finset.sum_congr rfl (fun a _ =>
      P.withJetControl_crossPacketValue 0 1 (by norm_num) (by simp)
        alt hAlt 0 d.selector u g z a))
  change Integrable (fun z => inner ℂ
      (∑ a∈initial, Q.crossPacketValue alt hAlt 0 d.selector u g z a) (f z))
      (volume.prod volume) ∧
    ‖∫ z, inner ℂ (∑ a∈initial, Q.crossPacketValue alt hAlt 0 d.selector u g z a)
      (f z) ∂volume.prod volume‖≤
      (d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper*(2*bound)^4)*
        Real.sqrt ((volume.prod volume).real F*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real F)^(9/20:ℝ) at h
  simpa only [he] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI
