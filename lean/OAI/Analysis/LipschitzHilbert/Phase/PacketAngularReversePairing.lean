import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularPartition
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataIntrinsicReverse
import OAI.Analysis.LipschitzHilbert.Estimates.OrdinaryModelConstructionCost

namespace OAI

/-! Construct and recombine the three angular models for the reverse
estimate. The fixed cost is independent of all finite packet data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_angular_reverse_pairing (hVariation : LepingleInput)
    (cStar cEta CEta cb Cv radius : ℝ) (M : ℕ)
    (hcStar : 0≤cStar) (hcEta : 0<cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0<cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta<cb/4) (hr : 0≤radius)
    (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
    (num : OrdinaryModelNumerics cStar cEta cb radius) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex),
    ∀ w F : ℝ, 0<w → w≤P.width → 0≤F → 207≤P.order →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j → ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
    ∀ bound : ℝ, 1≤bound → (2^P.order*P.profileBound)*3^(2*P.order)≤bound →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
    ∀ u : ℝ×ℝ → ℝ, Measurable u →
      Integrable (fun z => inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z)
        ∂volume.prod volume‖≤3*((num.reverseUnitCost M CD CS CT CZ*(2*bound)^4)*
          Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := by
  have hsep : cStar<cEta*cb := by
    have h : cStar/cEta<cb := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hcEta).mp h
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hreverse⟩ := exists_intrinsic_cross_reverse_disparity hVariation
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hsep
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P S w F hw hW hF horder hfreq hlocal spectrum bin
    alt hAlt altSpectrum altBin b hb hb1 haway hradius hnear bound hbound hprofile
    g f hgm hfm hgb hfb E Fset hE hFset hEfin hFfin hgs hfs u hu
  classical
  obtain ⟨tag,cell,hcover⟩ := P.exists_angular_assignment w cStar cEta cb radius
    hw hcStar hcEta hcb.le hr hcoverSmall
  let d := fun gamma => angularModelConfig P S cStar cEta CEta cb Cv w F radius M
    hcStar hcEta hCEta hCv hcb hcbQuarter hsmall num hw hW hF hr horder hfreq hlocal
    tag cell hcover spectrum bin b hb hb1 haway hradius hnear gamma
  let V := fun (gamma : DyadicLineGrid.GridChoice) (z : ℝ×ℝ) =>
    ∑ a∈P.angularPackets S tag gamma,
      P.crossPacketValue alt hAlt 0 (P.angularSelector tag gamma b) u g z a
  let B := (num.reverseUnitCost M CD CS CT CZ*(2*bound)^4)*
    Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
    ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)
  have hpiece (gamma : DyadicLineGrid.GridChoice) :
      Integrable (fun z => inner ℂ (V gamma z) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (V gamma z) (f z) ∂volume.prod volume‖≤B := by
    have hMargin : ∀ a∈P.angularPackets S tag gamma, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 a.1 a.2.1 a.2.2 k) (xi,et)≠0 →
        Icc (-xi/et-cb*(w/P.length a.1)) (-xi/et+cb*(w/P.length a.1))⊆
          scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1) := by
      intro a ha k xi et hs
      have heq := (Finset.mem_filter.mp ha).2
      have hspec := altSpectrum a.1 a.2.1 a.2.2 k xi et hs
      simpa only [heq] using (hcover a.1 a.2.1).2 xi et hspec.2.1 hspec.1
    have h := hreverse N κ Label Item P (P.angularPackets S tag gamma) (d gamma)
      rfl rfl rfl rfl rfl bound hbound hprofile alt hAlt altSpectrum hMargin
      (fun a _ k xi et hs => altBin a.1 a.2.1 a.2.2 k xi et hs)
      f g hfm hfb hgm hgb Fset E hFset hFfin hE hEfin hfs hgs u hu
    rw [OrdinaryModelConfig.unitReverseModelCost_of_numeric_fields (d gamma) cStar cEta cb radius
      num M CD CS CT CZ rfl rfl rfl rfl rfl rfl rfl rfl rfl] at h
    exact h
  have hsum (z : ℝ×ℝ) : inner ℂ (∑ gamma, V gamma z) (f z)=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z) :=
    congrArg (fun v => inner ℂ v (f z)) (P.sum_crossPacketValue_angularPartition alt hAlt S tag b 0 u g z)
  have hsint : Integrable (fun z => ∑ gamma, inner ℂ (V gamma z) (f z)) (volume.prod volume) :=
    integrable_finsetSum _ (fun gamma _ => (hpiece gamma).1)
  have heq (z : ℝ×ℝ) : (∑ gamma, inner ℂ (V gamma z) (f z))=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z) := by
    rw [←sum_inner]; exact hsum z
  refine ⟨hsint.congr (Filter.Eventually.of_forall heq),?_⟩
  rw [←integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_finsetSum _ (fun gamma _ => (hpiece gamma).1)]
  calc
    _ ≤ ∑ gamma : DyadicLineGrid.GridChoice,
        ‖∫ z, inner ℂ (V gamma z) (f z) ∂volume.prod volume‖ := norm_sum_le _ _
    _ ≤ ∑ _gamma : DyadicLineGrid.GridChoice, B :=
      Finset.sum_le_sum (fun gamma _ => (hpiece gamma).2)
    _ = 3*B := by simp only [Finset.sum_const,Finset.card_univ,DyadicLineGrid.gridChoice_card,nsmul_eq_mul,Nat.cast_ofNat]

end LipschitzHilbert.PacketLatticeData

end

end OAI
