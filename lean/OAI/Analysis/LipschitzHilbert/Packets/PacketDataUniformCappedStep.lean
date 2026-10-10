import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniformBoundedSize
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCappedRemovalStep
import OAI.Analysis.LipschitzHilbert.Trees.SourceCappedStepArithmetic

namespace OAI

/-! Uniform dyadic removal: all non-geometric constants are chosen before
the translated packet lattice and finite collection. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def boundedSizeCost (d : OrdinaryModelConfig P initial) (CZ : ℝ) : ℝ :=
  1+((3*d.M:ℕ):ℝ)*CZ*P.referenceEnvelopeConstant^2

def reverseStepCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+(2*(625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip)+
    (((4*d.D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip*
      d.sizeAreaConstant CS)*
    max (Real.sqrt (d.boundedSizeCost CZ)) (Real.sqrt 2)*max U 2

end OrdinaryModelConfig

theorem exists_uniform_normalized_capped_step (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (densityUpper : ℝ), 1≤densityUpper →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
      Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (energyNorm : ℝ), 0<energyNorm →
      energyNorm^2=(∫ z, ‖g z‖^2 ∂volume.prod volume) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
      0<(volume.prod volume).real E →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (gamma : ℝ), 0<gamma → gamma≤densityUpper → ∀ (k : ℤ) (S : Finset P.PacketIndex), S⊆initial →
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
        d.reverseStepCost CD CS CT CZ densityUpper*((volume.prod volume).real E)*
          reverseThresholdWeight (((volume.prod volume).real E)/energyNorm^2) ((2:ℝ)^k) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hStep⟩ := exists_ordinary_capped_removal_step hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  obtain ⟨CZ,hCZ,hBoundedAll⟩ := exists_uniform_bounded_unsigned_size
    cStar cEta CEta cb hcEta hcb.le hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ densityUpper hUpper
  have hBounded := hBoundedAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄
  rw [←heq₁,←heq₂,←heq₃,←heq₄,←heq₅] at hStep
  let Z := d.boundedSizeCost CZ
  have hZ : 0<Z := by dsimp [Z,OrdinaryModelConfig.boundedSizeCost]; positivity
  let A := 625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip
  let B := (((4*d.D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip
  let Q := d.sizeAreaConstant CS
  let K := max (Real.sqrt Z) (Real.sqrt 2)
  let U := max densityUpper 2
  let C := (2*A+B*Q)*K*U
  have hA : 0≤A := by
    dsimp only [A]
    exact mul_nonneg (by positivity) (P.referenceTreeConstant_nonneg _ _ _ _ d.hLip)
  have hB : 0≤B := mul_nonneg (Nat.cast_nonneg _) (P.referenceTreeConstant_nonneg _ _ _ _ d.hLip)
  have hQ : 0≤Q := d.sizeAreaConstant_nonneg CS
  have hK : 0≤K := (Real.sqrt_nonneg Z).trans (le_max_left _ _)
  have hU : 0≤U := (zero_le_one.trans hUpper).trans (le_max_left _ _)
  intro g hg hgm hgb energyNorm hN henergy E hE hEfin harea u hu gamma hgamma hgammaU k S hS hsize hden
  let area := (volume.prod volume).real E
  let eta := (2:ℝ)^k
  let sigma := modelSizeThreshold energyNorm area k
  let density := min gamma (2*eta)
  let cap := min (Real.sqrt Z) (Real.sqrt 2*sigma)
  have heta : 0<eta := zpow_pos (by norm_num) k
  have hsigma : 0<sigma := modelSizeThreshold_pos hN harea k
  have hdensity : 0≤density := le_min hgamma.le (by positivity)
  have hcap : 0≤cap := le_min (Real.sqrt_nonneg Z) (by positivity)
  have hsizeCap (T : SlopeBox) (hwT : T.width=P.width) (htT : T.length≤d.tau) :
      P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) S T≤cap^2*T.area := by
    by_cases hsmall : Real.sqrt Z≤Real.sqrt 2*sigma
    · dsimp only [cap]
      rw [min_eq_left hsmall,Real.sq_sqrt hZ.le]
      have hz := (P.unsignedSizeTestEnergy_mono d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) hS T).trans
        (hBounded g 1 zero_le_one hgm hgb T hwT htT)
      simpa only [one_pow,mul_one,Z,OrdinaryModelConfig.boundedSizeCost] using hz
    · dsimp only [cap]
      rw [min_eq_right (le_of_not_ge hsmall)]
      exact hsize T hwT htT
  obtain ⟨T,hTS,hTD,hsizeT,hI,hBound⟩ := hStep N κ Label Item P d.M d.Q d.gap d.packGap d.R d.K d.D0
    d.w d.tau sigma (Real.sqrt 2) d.epsilon d.A d.margin d.F d.radius d.Lip eta density cap
    hsigma (Real.sqrt_nonneg 2) hcap d.hepsilon heta hdensity d.hLip d.hw d.hW d.hF d.hfreq
    d.hgap d.hpack d.hmargin d.hA d.hQ d.hQnear d.hR d.horder d.hD0 d.htime d.hwide d.hK d.hlocal
    d.cell d.grid g hg (P.ordinaryCoefficient g) rfl S hsize hsizeCap
    (fun q hq => d.hrow q (hS hq)) (fun q hq => d.heps q (hS hq)) d.spectrum
    (fun q hq => d.margin_spectrum q (hS hq)) (fun q hq => d.bin q (hS hq))
    d.selector d.measurable d.bounded d.away d.support d.radius_bound d.near E hE hEfin u hu hden
  refine ⟨T,hTS,fun q hq => le_min ((hden q (hTS hq)).trans (min_le_left _ _)) (hTD q hq),hsizeT,hI,?_⟩
  have hscale : sigma^2*area=eta*(∫ z, ‖g z‖^2 ∂volume.prod volume) := by
    rw [←henergy]
    exact modelSizeThreshold_identity energyNorm area harea k
  have hn := combine_capped_removal_budgets A B Q cap sigma density eta area
    (∫ z, ‖g z‖^2 ∂volume.prod volume) hB hQ hcap hsigma hdensity heta harea.le hscale
  have hcBound : cap≤K*min 1 (Real.sqrt (eta/(area/energyNorm^2))) := by
    calc
      cap ≤ K*min 1 sigma := min_scaled_le (Real.sqrt Z) (Real.sqrt 2) sigma hsigma.le
      _ = _ := by
        have he : sigma=Real.sqrt (eta/(area/energyNorm^2)) := modelSizeThreshold_eq_sqrt_ratio hN harea k
        rw [he]
  have hdBound : density≤U*min 1 eta :=
    (min_le_min hgammaU le_rfl).trans (min_scaled_le densityUpper 2 eta heta.le)
  have hw := capped_density_weight_le cap density eta (area/energyNorm^2) K U
    heta hK hdensity hcBound hdBound
  have hwNonneg : 0≤reverseThresholdWeight (area/energyNorm^2) eta := by
    dsimp only [reverseThresholdWeight]
    positivity
  apply hBound.trans
  change A*cap*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
    B*cap*density*((Q/sigma^2)*(∫ z, ‖g z‖^2 ∂volume.prod volume))≤_
  calc
    _ ≤ (2*A+B*Q)*cap*density*(1+eta^(-(1/20:ℝ)))*area/eta := hn
    _ = ((2*A+B*Q)*area)*(cap*density*(1+eta^(-(1/20:ℝ)))/eta) := by ring
    _ ≤ ((2*A+B*Q)*area)*(K*U*reverseThresholdWeight (area/energyNorm^2) eta) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = C*area*reverseThresholdWeight (area/energyNorm^2) eta := by dsimp only [C]; ring
    _ ≤ (1+C)*area*reverseThresholdWeight (area/energyNorm^2) eta :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C≤1+C) harea.le) hwNonneg

end LipschitzHilbert.PacketLatticeData

end

end OAI
