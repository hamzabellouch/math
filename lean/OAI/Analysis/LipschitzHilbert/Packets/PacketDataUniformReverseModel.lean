import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniformCappedStep
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataFiniteSizeBound
import OAI.Analysis.LipschitzHilbert.Trees.SourceFiniteThresholdLevels
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataZeroDensity
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteRemovalIteration

namespace OAI

/-! Uniform reverse estimate from actual finite removals. The four input
constants are independent of packet count, translation and the scale interval. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem reverseStepCost_pos (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) :
    0<d.reverseStepCost CD CS CT CZ U := by
  have hD := P.referenceTreeConstant_nonneg CD ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hT := P.referenceTreeConstant_nonneg CT ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hS := d.sizeAreaConstant_nonneg CS
  have hU : 0<max U 2 := lt_max_of_lt_right (by norm_num)
  have hK : 0≤max (Real.sqrt (d.boundedSizeCost CZ)) (Real.sqrt 2) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  unfold reverseStepCost
  positivity

def reverseModelCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+(8/(1-reverseThresholdRatio))*d.reverseStepCost CD CS CT CZ U

theorem reverseModelCost_pos (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) :
    0<d.reverseModelCost CD CS CT CZ U := by
  have hA := d.reverseStepCost_pos CD CS CT CZ U
  have hG : 0<8/(1-reverseThresholdRatio) :=
    div_pos (by norm_num) (sub_pos.mpr reverseThresholdRatio_lt_one)
  unfold reverseModelCost
  positivity

end OrdinaryModelConfig

theorem exists_uniform_reverse_model_bound (hL : LepingleInput)
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
    ∀ (gamma : ℝ), 0<gamma → gamma≤densityUpper →
      (∀ q∈initial, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤gamma) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => ∑ q∈initial, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈initial, V q z‖ ∂volume.prod volume)≤
          d.reverseModelCost CD CS CT CZ densityUpper*((volume.prod volume).real E)*
            (((volume.prod volume).real E)/energyNorm^2)^(-(1/20:ℝ)) := by
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_normalized_capped_step hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ densityUpper hUpper
  have hStep := hAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄ heq₅ densityUpper hUpper
  let A := d.reverseStepCost CD CS CT CZ densityUpper
  have hApos : 0<A := d.reverseStepCost_pos CD CS CT CZ densityUpper
  let G := 8/(1-reverseThresholdRatio)
  have hA : 0≤A := hApos.le
  have hG : 0<G := div_pos (by positivity) (sub_pos.mpr reverseThresholdRatio_lt_one)
  intro g hg hgm hgb energyNorm hN henergy E hE hEfin harea u hu gamma hgamma hgammaUpper hden V
  let area := (volume.prod volume).real E
  let State := fun (k : ℤ) (S : Finset P.PacketIndex) => S⊆initial ∧
    (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤min gamma ((2:ℝ)^k)) ∧
    (∀ U : SlopeBox, U.width=P.width → U.length≤d.tau →
      P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) S U≤
        (modelSizeThreshold energyNorm area k)^2*U.area)
  let v := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
    P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
      P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
  let ratio := area/energyNorm^2
  have hratioPos : 0<ratio := div_pos harea (sq_pos_of_pos hN)
  let L := A*area
  let B := fun k : ℤ => L*reverseThresholdWeight ratio ((2:ℝ)^(k-1))
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
    obtain ⟨T,hTS,hTD,hTZ,hI,hBound⟩ := hStep g hg hgm hgb energyNorm hN henergy E hE hEfin harea
      u hu gamma hgamma hgammaUpper (k-1) S hS.1 hsize (by simpa only [hpow] using hS.2.1)
    exact ⟨T,hTS,⟨hTS.trans hS.1,hTD,hTZ⟩,hI,hBound⟩
  obtain ⟨s0,hs0,hsize0⟩ := P.exists_finite_unsigned_size_bound d.w d.cb d.cell d.grid
    (P.ordinaryCoefficient g) initial
  obtain ⟨k0,hk0⟩ := exists_dyadic_upper_level (max densityUpper (s0^2*area/energyNorm^2))
  have hInitial : State k0 initial := by
    refine ⟨Finset.Subset.refl _,?_,?_⟩
    · intro q hq
      exact le_min (hden q hq) ((hden q hq).trans
        (hgammaUpper.trans ((le_max_left _ _).trans hk0.le)))
    · intro U hwU htU
      have hratio : s0^2*area/energyNorm^2<(2:ℝ)^k0 := (le_max_right _ _).trans_lt hk0
      have hprod := (div_lt_iff₀ (sq_pos_of_pos hN)).mp hratio
      have hid := modelSizeThreshold_identity energyNorm area harea k0
      have hs : s0^2≤(modelSizeThreshold energyNorm area k0)^2 := by nlinarith
      exact (hsize0 U hwU).trans (mul_le_mul_of_nonneg_right hs U.area_pos.le)
  obtain ⟨kend,hend⟩ := exists_dyadic_zero_detection initial
    (P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u)
  let n := (k0-min k0 kend).toNat
  have hn : (n:ℤ)=k0-min k0 kend := Int.toNat_of_nonneg (sub_nonneg.mpr (min_le_left _ _))
  have hlast : k0-(n:ℤ)≤kend := by rw [hn]; omega
  obtain ⟨T,hT,hState,hI,hBound⟩ := iterate_finite_removal v E State B step n k0 initial hInitial
  have hzeroDensity (q : P.PacketIndex) (hq : q∈T) :
      P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤0 :=
    hend q (hT hq) (((hState.2.1 q hq).trans (min_le_right _ _)).trans
      (zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hlast))
  have hzero : finitePacketSum v T=ᵐ[(volume.prod volume).restrict E] 0 :=
    P.packet_sum_zero_of_density_zero T d.cell d.grid d.w d.tau
      (fun q hq => d.hlength q (hT hq)) (fun q hq => d.hrow q (hT hq)) E hE u hu
      hzeroDensity (P.ordinaryCoefficient g) d.selector d.support
  let indices := (Finset.range n).image (fun i : ℕ => k0-(i:ℤ)-1)
  have hindices : (∑ j∈indices, reverseThresholdWeight ratio ((2:ℝ)^j))=
      ∑ i∈Finset.range n, reverseThresholdWeight ratio ((2:ℝ)^(k0-(i:ℤ)-1)) := by
    apply Finset.sum_image (g:=fun i : ℕ => k0-(i:ℤ)-1)
    intro i _ j _ hij
    change k0-(i:ℤ)-1=k0-(j:ℤ)-1 at hij
    omega
  have hsum : (∑ i∈Finset.range n, B (k0-(i:ℤ)))≤L*(G*ratio^(-(1/20:ℝ))) := by
    change (∑ i∈Finset.range n, L*reverseThresholdWeight ratio ((2:ℝ)^((k0-(i:ℤ))-1)))≤_
    rw [←Finset.mul_sum,←hindices]
    exact mul_le_mul_of_nonneg_left (reverseThreshold_finite_sum hratioPos indices) hLnonneg
  obtain ⟨hFull,hFullBound⟩ := finite_removal_zero_remainder v E initial T hI hzero _ (hBound.trans hsum)
  refine ⟨hFull,hFullBound.trans ?_⟩
  change L*(G*ratio^(-(1/20:ℝ)))≤(1+G*A)*area*ratio^(-(1/20:ℝ))
  calc
    _ = (G*A)*(area*ratio^(-(1/20:ℝ))) := by dsimp only [L]; ring
    _ ≤ (1+G*A)*(area*ratio^(-(1/20:ℝ))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
