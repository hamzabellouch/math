import OAI.Analysis.LipschitzHilbert.Packets.PacketDataIntrinsicDensityPairing

namespace OAI

/-! The basic finite packet bound follows from the intrinsic density
estimate and the universal density upper bound. No field regularity is needed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_basic_pairing (hL : LepingleInput)
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
    ordinaryDensityUpper^(1/4:ℝ)≤L →
    (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F →
      (volume.prod volume) E≠∞ → (volume.prod volume) F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      Integrable (fun z => inner ℂ
        (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume‖≤L^(3*p+5)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_intrinsic_density_pairing hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofile S hS g f hgm hfm hgb hfb
    E F hE hF hEfin hFfin hgs hfs u hu
  have hUpos : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
  have hden (q : P.PacketIndex) (_hq : q∈S) :
      P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤ordinaryDensityUpper :=
    ((P.densityTile 0 d.cell q).density_le P.topLength d.w P.width d.tau d.grid E u).trans
      (le_max_right _ _)
  have h := hAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hprofile S hS g f hgm hfm hgb hfb
    E F hE hF hEfin hFfin hgs hfs u hu ordinaryDensityUpper hUpos hden
  refine ⟨h.1,h.2.trans ?_⟩
  have hLp : 0<L := by linarith
  calc
    _ ≤ (L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
        Real.sqrt ((volume.prod volume).real E))*L :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    _ = _ := by
      have he : L^(3*p+5)=L^(3*p+4)*L := by
        rw [show 3*p+5=(3*p+4)+1 by ring,Real.rpow_add hLp,Real.rpow_one]
      rw [he]
      ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
