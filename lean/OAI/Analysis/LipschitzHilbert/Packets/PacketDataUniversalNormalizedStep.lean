import OAI.Analysis.LipschitzHilbert.Packets.PacketDataNormalizedRemovalStep

namespace OAI

/-! The removal constants are chosen before the packet lattice, its
size, and its scale-dependent geometric parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_universal_normalized_removal_step (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
    ∀ (energyNorm : ℝ), 0<energyNorm →
      energyNorm^2=(∫ z, ‖g z‖^2 ∂volume.prod volume) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
      0<(volume.prod volume).real E →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (gamma : ℝ), 0<gamma → ∀ (k : ℤ) (S : Finset P.PacketIndex), S⊆initial →
      (∀ T : SlopeBox, T.width=P.width → T.length≤d.tau →
        P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) S T≤
          (Real.sqrt 2*modelSizeThreshold energyNorm ((volume.prod volume).real E) k)^2*T.area) →
      (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤min gamma (2*(2:ℝ)^k)) →
    ∃ T : Finset P.PacketIndex, T⊆S ∧
      (∀ q∈T, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤min gamma ((2:ℝ)^k)) ∧
      (∀ U : SlopeBox, U.width=P.width → U.length≤d.tau →
        P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) T U≤
          (modelSizeThreshold energyNorm ((volume.prod volume).real E) k)^2*U.area) ∧
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => (∑ q∈S, V q z)-(∑ q∈T, V q z)) E (volume.prod volume) ∧
      (∫ z in E, ‖(∑ q∈S, V q z)-(∑ q∈T, V q z)‖ ∂volume.prod volume)≤
        d.stepConstant CD CS CT*energyNorm*Real.sqrt ((volume.prod volume).real E)*
          ordinaryThresholdWeight gamma ((2:ℝ)^k) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hStep⟩ := exists_ordinary_removal_step hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d h₁ h₂ h₃ h₄ h₅
  rw [←h₁,←h₂,←h₃,←h₄,←h₅] at hStep
  intro g hg energyNorm hN henergy E hE hEfin harea u hu gamma hgamma k S hS hsize hden
  let area := (volume.prod volume).real E
  let eta := (2:ℝ)^k
  let sigma := modelSizeThreshold energyNorm area k
  let density := min gamma (2*eta)
  have heta : 0<eta := zpow_pos (by norm_num) k
  have hsigma : 0<sigma := modelSizeThreshold_pos hN harea k
  have hdensity : 0≤density := le_min hgamma.le (by positivity)
  obtain ⟨T,hTS,hTD,hsizeT,hI,hBound⟩ := hStep N κ Label Item P d.M d.Q d.gap d.packGap d.R d.K d.D0
    d.w d.tau sigma (Real.sqrt 2) d.epsilon d.A d.margin d.F d.radius d.Lip eta density
    hsigma (Real.sqrt_nonneg 2) d.hepsilon heta hdensity d.hLip d.hw d.hW d.hF d.hfreq
    d.hgap d.hpack d.hmargin d.hA d.hQ d.hQnear d.hR d.horder d.hD0 d.htime d.hwide d.hK d.hlocal
    d.cell d.grid g hg (P.ordinaryCoefficient g) rfl S hsize
    (fun q hq => d.hrow q (hS hq)) (fun q hq => d.heps q (hS hq)) d.spectrum
    (fun q hq => d.margin_spectrum q (hS hq)) (fun q hq => d.bin q (hS hq))
    d.selector d.measurable d.bounded d.away d.support d.radius_bound d.near E hE hEfin u hu hden
  refine ⟨T,hTS,fun q hq => le_min ((hden q (hTS hq)).trans (min_le_left _ _)) (hTD q hq),hsizeT,hI,?_⟩
  let A := 625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip
  let B := (((4*d.D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip
  have hB : 0≤B := mul_nonneg (Nat.cast_nonneg _) (P.referenceTreeConstant_nonneg _ _ _ _ d.hLip)
  have hscale : sigma^2*area=eta*(∫ z, ‖g z‖^2 ∂volume.prod volume) := by
    rw [←henergy]
    exact modelSizeThreshold_identity energyNorm area harea k
  have hn := combine_ordinary_removal_budgets A B (d.sizeAreaConstant CS) (Real.sqrt 2)
    sigma density eta area (∫ z, ‖g z‖^2 ∂volume.prod volume)
    hB (d.sizeAreaConstant_nonneg CS) (Real.sqrt_nonneg 2) hsigma hdensity heta harea.le hscale
  apply hBound.trans
  have hnormalized : sigma*area/Real.sqrt eta=energyNorm*Real.sqrt area :=
    modelSizeThreshold_normalized energyNorm area harea k
  rw [hnormalized] at hn
  change A*(Real.sqrt 2*sigma)*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
    B*(Real.sqrt 2*sigma)*density*((d.sizeAreaConstant CS/sigma^2)*
      (∫ z, ‖g z‖^2 ∂volume.prod volume))≤_
  convert hn using 1
  dsimp only [OrdinaryModelConfig.stepConstant,A,B,ordinaryThresholdWeight,density,eta,area]
  ring


end LipschitzHilbert.PacketLatticeData

end

end OAI
