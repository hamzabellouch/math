import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossPairingBound
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataIntrinsicCrossEnergy

namespace OAI

/-! The distinct-profile bilinear density estimate, with uniform
polynomial cost and no dependence on the auxiliary jet normalization. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_density_pairing (hL : LepingleInput)
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
    (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F →
      (volume.prod volume) E≠∞ → (volume.prod volume) F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → ∀ eta : ℝ, 0<eta →
      (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤eta) →
      Integrable (fun z => inner ℂ
        (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume‖≤L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_ordinary_model_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hprofile S hS g f hgm hfm hgb hfb
    E F hE hF hEfin hFfin hgs hfs u hu eta heta hdensity
  let Q := P.withJetControl 0 1 (by norm_num) (by simp)
  let dq := d.withJetControl 0 1 (by norm_num) (by simp)
  have hLp : 0<L := by linarith
  have hLone : 1≤L := by linarith
  have hb : P.profileBound≤(2^P.order*P.profileBound)*3^(2*P.order) := by
    have h₂ : (1:ℝ)≤2^P.order := one_le_pow₀ (by norm_num)
    have h₃ : (1:ℝ)≤3^(2*P.order) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 2^P.order*P.profileBound := le_mul_of_one_le_left P.profileBound_pos.le h₂
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by norm_num) _) P.profileBound_pos.le) h₃
  have hbase : Q.referenceEnvelopeConstant≤L^p := by
    simpa only [Q,referenceEnvelopeConstant,PacketLatticeData.withJetControl,one_pow,mul_one] using hprofile
  have hscale : 2*L^p≤L^(p+1) := by
    rw [Real.rpow_add hLp,Real.rpow_one]
    nlinarith [Real.rpow_nonneg hLp.le p]
  obtain ⟨hf,hfenergy⟩ := bounded_supported_input f hfm hfb F hF hFfin hfs
  have hg := (bounded_supported_input g hgm hgb E hE hEfin hgs).1
  have hFor (c : ℂ) (hc : ‖c‖=1) :
      ‖∫ z, inner ℂ ((Q.polarize alt hAlt c hc).ordinaryAdjointSum S d.selector u g z) (f z)
        ∂volume.prod volume‖≤L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) := by
    let R := Q.polarize alt hAlt c hc
    let dr := OrdinaryModelConfig.polarize (P:=Q) alt hAlt dq c hc hSpectrum hMargin hBin
    have hpr : R.profileBound≤L^(p+1) :=
      (mul_le_mul_of_nonneg_left (hb.trans hprofile) (by norm_num : (0:ℝ)≤2)).trans hscale
    have harEq : R.referenceEnvelopeConstant=2*Q.referenceEnvelopeConstant := by
      dsimp only [R,polarize,referenceEnvelopeConstant]
      ring
    have har : R.referenceEnvelopeConstant≤L^(p+1) := by
      rw [harEq]
      exact (mul_le_mul_of_nonneg_left hbase (by norm_num : (0:ℝ)≤2)).trans hscale
    have hcost := dr.modelCost_le_rpow CD CS CT L L (p+1) hCS.le hLone le_rfl
      (by linarith) hunit hpr har
    have hcost' : dr.modelCost CD CS CT≤L^(3*p+4) := by
      convert hcost using 1
      congr 1
      ring
    have hm := hAll N κ Label Item R initial dr heq₁ heq₂ heq₃ heq₄ heq₅
      S hS f hf E hE hEfin u hu eta heta hdensity
    change IntegrableOn (R.ordinaryForwardSum S d.selector u f) E (volume.prod volume) ∧
      (∫ z in E, ‖R.ordinaryForwardSum S d.selector u f z‖ ∂volume.prod volume)≤
      dr.modelCost CD CS CT*Real.sqrt (∫ z, ‖f z‖^2 ∂volume.prod volume)*
        Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) at hm
    have ha := R.ordinary_adjoint_pairing_bound S d.selector d.measurable d.bounded
      u hu f g hf hg hgm hgb E hE hgs hm.1
    apply ha.2.trans (hm.2.trans ?_)
    gcongr
  have h := Q.cross_pairing_bound alt hAlt S d.selector d.measurable d.bounded u hu
    g f hgm hgb hf _ hFor
  have he (z : ℝ×ℝ) (q : P.PacketIndex) :
      Q.crossPacketValue alt hAlt 0 d.selector u g z q=
        P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    P.withJetControl_crossPacketValue 0 1 (by norm_num) (by simp)
      alt hAlt 0 d.selector u g z q
  have hsum (z : ℝ×ℝ) : (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q)=
      ∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    Finset.sum_congr rfl (fun q _ => he z q)
  have hpair (z : ℝ×ℝ) :
      inner ℂ (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)=
      inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z) :=
    congrArg (fun v => inner ℂ v (f z)) (hsum z)
  refine ⟨h.1.congr (Filter.Eventually.of_forall hpair),?_⟩
  have hi : (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
      ∂volume.prod volume)=
      ∫ z, inner ℂ (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => (hpair z).symm))
  rw [hi]
  exact h.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
