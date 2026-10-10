import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniversalEstimate

namespace OAI

/-! Polynomial dependence of the explicit model cost on the two packet
adaptation bounds. All remaining factors involve fixed geometric data. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

 def ordinaryTreeUnitCost (C : ℝ) (B K : ℕ) (Lip : ℝ) : ℝ :=
  27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203+
  Real.sqrt (C*(B:ℝ))+
  32^106*(B:ℝ)*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
    (32*2^203)*9*transverseTailConstant

 def selectedNearUnitCost (gap M Q : ℕ) : ℝ :=
  ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*Real.pi^2)

 def selectedFarUnitCost (cb D C : ℝ) (packGap M Q : ℕ) : ℝ :=
  (4*D)^2*256*(82944*SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q)^2*
    1296*Real.pi^2*(((3*M:ℕ):ℝ)*C)

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceTreeConstant_le_unit (P : PacketLatticeData N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip bound : ℝ) (hLip : 0≤Lip)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    P.referenceTreeConstant C B K Lip≤ordinaryTreeUnitCost C B K Lip*bound := by
  have ht := transverseTailConstant_nonneg
  dsimp only [referenceTreeConstant,ordinaryTreeUnitCost]
  calc
    _ ≤ 27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*bound+
      Real.sqrt (C*(B:ℝ))*bound+
      32^106*(B:ℝ)*bound*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
        (32*2^203)*9*transverseTailConstant := by gcongr
    _ = _ := by ring

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def unitSizeAreaCost (d : OrdinaryModelConfig P initial) (CS : ℝ) : ℝ :=
  4*(selectedNearUnitCost d.gap d.M d.Q+
    2*Real.sqrt (2*selectedFarUnitCost d.cb (Real.sqrt 2) CS d.packGap d.M d.Q))

def unitStepCost (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  Real.sqrt 2*(2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip)+
    (((4*d.D0+1)^2:ℕ):ℝ)*ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip*d.unitSizeAreaCost CS)

def unitModelCost (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*d.unitStepCost CD CS CT

theorem sizeAreaConstant_le_unit (d : OrdinaryModelConfig P initial) (CS bound : ℝ)
    (hCS : 0≤CS)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    d.sizeAreaConstant CS≤d.unitSizeAreaCost CS*bound^2 := by
  have hp := P.profileBound_pos.le
  have ha := P.referenceEnvelopeConstant_pos.le
  let U := selectedFarUnitCost d.cb (Real.sqrt 2) CS d.packGap d.M d.Q
  have hU : 0≤U := by dsimp only [U,selectedFarUnitCost]; positivity
  have heFar : selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q=
      U*P.profileBound^2*P.referenceEnvelopeConstant^2 := by
    dsimp only [selectedFarConstant,U,selectedFarUnitCost]
    ring
  have hFar : 2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q≤(2*U)*(bound^2)^2 := by
    rw [heFar]
    calc
      _ ≤ 2*(U*bound^2*bound^2) := by gcongr
      _ = _ := by ring
  have hNear : selectedNearConstant P d.gap d.M d.Q≤selectedNearUnitCost d.gap d.M d.Q*bound^2 := by
    dsimp only [selectedNearConstant,selectedNearUnitCost]
    calc
      _ = (((2*d.gap+1:ℕ):ℝ)*(((2*d.Q+1)*d.M:ℕ):ℝ)*((4*Real.pi)^2*Real.pi^2))*P.profileBound^2 := by ring
      _ ≤ _ := by gcongr
  have hSqrt : Real.sqrt (2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q)≤
      Real.sqrt (2*U)*bound^2 := by
    calc
      _ ≤ Real.sqrt ((2*U)*(bound^2)^2) := Real.sqrt_le_sqrt hFar
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0≤2*U),Real.sqrt_sq (sq_nonneg bound)]
  calc
    _ ≤ 4*(selectedNearUnitCost d.gap d.M d.Q*bound^2+2*(Real.sqrt (2*U)*bound^2)) := by
      dsimp only [sizeAreaConstant]
      gcongr
    _ = _ := by dsimp only [unitSizeAreaCost,U]; ring

theorem unitStepCost_nonneg (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) :
    0≤d.unitStepCost CD CS CT := by
  have ht := transverseTailConstant_nonneg
  have hLip := d.hLip
  dsimp only [unitStepCost,unitSizeAreaCost,ordinaryTreeUnitCost,selectedNearUnitCost]
  positivity

theorem modelCost_le_cubic (d : OrdinaryModelConfig P initial) (CD CS CT bound : ℝ)
    (hCS : 0≤CS) (hbound : 1≤bound)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    d.modelCost CD CS CT≤d.unitModelCost CD CS CT*bound^3 := by
  let td := ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip
  let tt := ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip
  let sz := d.unitSizeAreaCost CS
  let sp := (((4*d.D0+1)^2:ℕ):ℝ)
  have ht := transverseTailConstant_nonneg
  have hLip := d.hLip
  have htd : 0≤td := by dsimp only [td,ordinaryTreeUnitCost]; positivity
  have htt : 0≤tt := by dsimp only [tt,ordinaryTreeUnitCost]; positivity
  have hsz : 0≤sz := by dsimp only [sz,unitSizeAreaCost,selectedNearUnitCost]; positivity
  have hsp : 0≤sp := Nat.cast_nonneg _
  have htdb := P.referenceTreeConstant_le_unit CD ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hprofile habsolute
  have httb := P.referenceTreeConstant_le_unit CT ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hprofile habsolute
  have hsizeNonneg := d.sizeAreaConstant_nonneg CS
  have hszb := d.sizeAreaConstant_le_unit CS bound hCS hprofile habsolute
  have hb3 : bound≤bound^3 := by
    have h := mul_nonneg (sub_nonneg.mpr hbound)
      (by positivity : 0≤bound^2+bound)
    nlinarith
  have hstep : d.stepConstant CD CS CT≤d.unitStepCost CD CS CT*bound^3 := by
    calc
      _ ≤ Real.sqrt 2*(2*(625*densityRadiusConstant^2*(td*bound))+
          sp*(tt*bound)*(sz*bound^2)) := by
        dsimp only [stepConstant]
        gcongr
      _ = Real.sqrt 2*((2*625*densityRadiusConstant^2*td)*bound+(sp*tt*sz)*bound^3) := by ring
      _ ≤ Real.sqrt 2*((2*625*densityRadiusConstant^2*td)*bound^3+(sp*tt*sz)*bound^3) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hb3 (by positivity)) le_rfl) (Real.sqrt_nonneg 2)
      _ = _ := by dsimp only [unitStepCost,td,tt,sz,sp]; ring
  have hG : 0≤8*ordinaryDensityUpper/(1-ordinaryThresholdRatio) := by
    have hU : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
    have hr := sub_pos.mpr ordinaryThresholdRatio_lt_one
    positivity
  calc
    _ ≤ 1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*(d.unitStepCost CD CS CT*bound^3) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep hG)
    _ ≤ bound^3+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*(d.unitStepCost CD CS CT*bound^3) :=
      add_le_add (hbound.trans hb3) le_rfl
    _ = _ := by dsimp only [unitModelCost]; ring

theorem modelCost_le_rpow (d : OrdinaryModelConfig P initial) (CD CS CT K L p : ℝ)
    (hCS : 0≤CS) (hL : 1≤L) (hKL : K≤L) (hp : 0≤p)
    (hunit : d.unitModelCost CD CS CT≤K)
    (hprofile : P.profileBound≤L^p) (habsolute : P.referenceEnvelopeConstant≤L^p) :
    d.modelCost CD CS CT≤L^(3*p+1) := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hpow : 1≤L^p := Real.one_le_rpow hL hp
  have hc := d.modelCost_le_cubic CD CS CT (L^p) hCS hpow hprofile habsolute
  have he : (L^p)^3=L^(3*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
    congr 1
    norm_num
    ring
  calc
    _ ≤ d.unitModelCost CD CS CT*(L^p)^3 := hc
    _ ≤ K*(L^p)^3 := mul_le_mul_of_nonneg_right hunit (by positivity)
    _ ≤ L*(L^p)^3 := mul_le_mul_of_nonneg_right hKL (by positivity)
    _ = L^(1:ℝ)*L^(3*p) := by rw [he,Real.rpow_one]
    _ = _ := by rw [←Real.rpow_add hLp]; congr 1; ring

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
