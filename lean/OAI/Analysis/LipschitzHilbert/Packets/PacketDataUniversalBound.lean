import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelBound
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniversalNormalizedStep

namespace OAI

/-! A quantitative ordinary model estimate with analytic constants
chosen before every lattice and an explicit geometric cost. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_universal_ordinary_model_bound (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ densityUpper : ℝ, 1≤densityUpper →
    ∀ (packets : Finset P.PacketIndex), packets⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
    ∀ (energyNorm : ℝ), 0<energyNorm →
      energyNorm^2=(∫ z, ‖g z‖^2 ∂volume.prod volume) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
      0<(volume.prod volume).real E →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (gamma : ℝ), 0<gamma → gamma≤densityUpper →
      (∀ q∈packets, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤gamma) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => ∑ q∈packets, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈packets, V q z‖ ∂volume.prod volume)≤
          (1+(8*densityUpper/(1-ordinaryThresholdRatio))*d.stepConstant CD CS CT)*
            energyNorm*Real.sqrt ((volume.prod volume).real E)*gamma^(1/4:ℝ) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_normalized_removal_step hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d h₁ h₂ h₃ h₄ h₅ densityUpper hUpper
  have hStep := hAll N κ Label Item P initial d h₁ h₂ h₃ h₄ h₅
  let A := d.stepConstant CD CS CT
  let G := 8*densityUpper/(1-ordinaryThresholdRatio)
  have hA : 0≤A := d.stepConstant_nonneg CD CS CT
  intro packets hpackets g hg energyNorm hN henergy E hE hEfin harea u hu gamma hgamma hgammaUpper hden V
  let area := (volume.prod volume).real E
  let State := fun (k : ℤ) (S : Finset P.PacketIndex) => S⊆initial ∧
    (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤min gamma ((2:ℝ)^k)) ∧
    (∀ U : SlopeBox, U.width=P.width → U.length≤d.tau →
      P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) S U≤
        (modelSizeThreshold energyNorm area k)^2*U.area)
  let v := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
    P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
      P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
  let L := A*energyNorm*Real.sqrt area
  let B := fun k : ℤ => L*ordinaryThresholdWeight gamma ((2:ℝ)^(k-1))
  have hLnonneg : 0≤L := by dsimp only [L]; positivity
  have step (k : ℤ) (S : Finset P.PacketIndex) (hS : State k S) :
      ∃ T, T⊆S ∧ State (k-1) T ∧
        IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume) ∧
        (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤B k := by
    have hsize (U : SlopeBox) (hwU : U.width=P.width) (htU : U.length≤d.tau) := hS.2.2 U hwU htU
    simp only [modelSizeThreshold_successive energyNorm area harea k] at hsize
    have hpow : 2*(2:ℝ)^(k-1)=(2:ℝ)^k := by
      rw [zpow_sub₀ (by norm_num),zpow_one]
      ring
    obtain ⟨T,hTS,hTD,hTZ,hI,hBound⟩ := hStep g hg energyNorm hN henergy E hE hEfin harea
      u hu gamma hgamma (k-1) S hS.1 hsize (by simpa only [hpow] using hS.2.1)
    exact ⟨T,hTS,⟨hTS.trans hS.1,hTD,hTZ⟩,hI,hBound⟩
  obtain ⟨s0,hs0,hsize0⟩ := P.exists_finite_unsigned_size_bound d.w d.cb d.cell d.grid
    (P.ordinaryCoefficient g) packets
  obtain ⟨k0,hk0⟩ := exists_dyadic_upper_level (max densityUpper (s0^2*area/energyNorm^2))
  have hInitial : State k0 packets := by
    refine ⟨hpackets,?_,?_⟩
    · intro q hq
      exact le_min (hden q hq) ((hden q hq).trans
        (hgammaUpper.trans ((le_max_left _ _).trans hk0.le)))
    · intro U hwU htU
      have hratio : s0^2*area/energyNorm^2<(2:ℝ)^k0 := (le_max_right _ _).trans_lt hk0
      have hprod := (div_lt_iff₀ (sq_pos_of_pos hN)).mp hratio
      have hid := modelSizeThreshold_identity energyNorm area harea k0
      have hs : s0^2≤(modelSizeThreshold energyNorm area k0)^2 := by nlinarith
      exact (hsize0 U hwU).trans (mul_le_mul_of_nonneg_right hs U.area_pos.le)
  obtain ⟨kend,hend⟩ := exists_dyadic_zero_detection packets
    (P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u)
  let n := (k0-min k0 kend).toNat
  have hn : (n:ℤ)=k0-min k0 kend := Int.toNat_of_nonneg (sub_nonneg.mpr (min_le_left _ _))
  have hlast : k0-(n:ℤ)≤kend := by rw [hn]; omega
  obtain ⟨T,hT,hState,hI,hBound⟩ := iterate_finite_removal v E State B step n k0 packets hInitial
  have hzeroDensity (q : P.PacketIndex) (hq : q∈T) :
      P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤0 :=
    hend q (hT hq) (((hState.2.1 q hq).trans (min_le_right _ _)).trans
      (zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hlast))
  have hzero : finitePacketSum v T=ᵐ[(volume.prod volume).restrict E] 0 :=
    P.packet_sum_zero_of_density_zero T d.cell d.grid d.w d.tau
      (fun q hq => d.hlength q (hpackets (hT hq))) (fun q hq => d.hrow q (hpackets (hT hq))) E hE u hu
      hzeroDensity (P.ordinaryCoefficient g) d.selector d.support
  let indices := (Finset.range n).image (fun i : ℕ => k0-(i:ℤ)-1)
  have hindices : (∑ j∈indices, ordinaryThresholdWeight gamma ((2:ℝ)^j))=
      ∑ i∈Finset.range n, ordinaryThresholdWeight gamma ((2:ℝ)^(k0-(i:ℤ)-1)) := by
    apply Finset.sum_image (g:=fun i : ℕ => k0-(i:ℤ)-1)
    intro i _ j _ hij
    change k0-(i:ℤ)-1=k0-(j:ℤ)-1 at hij
    omega
  have hsum : (∑ i∈Finset.range n, B (k0-(i:ℤ)))≤L*(G*gamma^(1/4:ℝ)) := by
    change (∑ i∈Finset.range n, L*ordinaryThresholdWeight gamma ((2:ℝ)^((k0-(i:ℤ))-1)))≤_
    rw [←Finset.mul_sum,←hindices]
    exact mul_le_mul_of_nonneg_left (ordinaryThreshold_finite_sum_bounded hgamma hUpper hgammaUpper indices) hLnonneg
  obtain ⟨hFull,hFullBound⟩ := finite_removal_zero_remainder v E packets T hI hzero _ (hBound.trans hsum)
  refine ⟨hFull,hFullBound.trans ?_⟩
  change L*(G*gamma^(1/4:ℝ))≤(1+G*A)*energyNorm*Real.sqrt area*gamma^(1/4:ℝ)
  calc
    _ = (G*A)*(energyNorm*Real.sqrt area*gamma^(1/4:ℝ)) := by dsimp only [L]; ring
    _ ≤ (1+G*A)*(energyNorm*Real.sqrt area*gamma^(1/4:ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
