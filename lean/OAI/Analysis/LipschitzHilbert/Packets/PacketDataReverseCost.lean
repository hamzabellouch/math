import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniformReverseModel
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelCostPolynomial

namespace OAI

/-! Polynomial dependence of the reverse estimate on packet adaptation.
Its remaining constants use only the fixed geometric parameters. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def reverseCoreUnitCost (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip)+
    (((4*d.D0+1)^2:ℕ):ℝ)*ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip*
      d.unitSizeAreaCost CS

def unitReverseStepCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+d.reverseCoreUnitCost CD CS CT*
    max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*max U 2

def unitReverseModelCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+(8/(1-reverseThresholdRatio))*d.unitReverseStepCost CD CS CT CZ U

theorem reverseStepCost_le_quartic (d : OrdinaryModelConfig P initial)
    (CD CS CT CZ U bound : ℝ) (hCS : 0≤CS) (hCZ : 0≤CZ) (hb : 1≤bound)
    (hp : P.profileBound≤bound) (ha : P.referenceEnvelopeConstant≤bound) :
    d.reverseStepCost CD CS CT CZ U≤d.unitReverseStepCost CD CS CT CZ U*bound^4 := by
  have hbp : 0≤bound := zero_le_one.trans hb
  have hb2 : 1≤bound^2 := one_le_pow₀ hb
  have hb4 : 1≤bound^4 := one_le_pow₀ hb
  have hz : d.boundedSizeCost CZ≤(1+((3*d.M:ℕ):ℝ)*CZ)*bound^2 := by
    unfold boundedSizeCost
    calc
      _ ≤ bound^2+((3*d.M:ℕ):ℝ)*CZ*bound^2 := by
        gcongr
        exact P.referenceEnvelopeConstant_pos.le
      _ = _ := by ring
  have hsqrt : Real.sqrt (d.boundedSizeCost CZ)≤
      Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)*bound := by
    apply (Real.sqrt_le_sqrt hz).trans_eq
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hbp]
  have hk : max (Real.sqrt (d.boundedSizeCost CZ)) (Real.sqrt 2)≤
      max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*bound := by
    rw [max_mul_of_nonneg _ _ hbp]
    exact max_le_max hsqrt (le_mul_of_one_le_right (Real.sqrt_nonneg _) hb)
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
  have htdb := P.referenceTreeConstant_le_unit CD ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hp ha
  have httb := P.referenceTreeConstant_le_unit CT ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hp ha
  have hsize := d.sizeAreaConstant_nonneg CS
  have hszb := d.sizeAreaConstant_le_unit CS bound hCS hp ha
  have hb3 : bound≤bound^3 := by
    have h := mul_nonneg (sub_nonneg.mpr hb) (by positivity : 0≤bound^2+bound)
    nlinarith
  have hcore :
      2*(625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip)+
        sp*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip*d.sizeAreaConstant CS≤
      d.reverseCoreUnitCost CD CS CT*bound^3 := by
    calc
      _ ≤ 2*(625*densityRadiusConstant^2*(td*bound))+sp*(tt*bound)*(sz*bound^2) := by
        gcongr
      _ = (2*625*densityRadiusConstant^2*td)*bound+(sp*tt*sz)*bound^3 := by ring
      _ ≤ (2*625*densityRadiusConstant^2*td)*bound^3+(sp*tt*sz)*bound^3 :=
        add_le_add (mul_le_mul_of_nonneg_left hb3 (by positivity)) le_rfl
      _ = _ := by dsimp only [reverseCoreUnitCost,td,tt,sz,sp]; ring
  have hD := P.referenceTreeConstant_nonneg CD ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hT := P.referenceTreeConstant_nonneg CT ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hU : 0≤max U 2 := le_max_of_le_right (by norm_num)
  have hcore0 : 0≤d.reverseCoreUnitCost CD CS CT := by
    change 0≤2*(625*densityRadiusConstant^2*td)+sp*tt*sz
    positivity
  unfold reverseStepCost unitReverseStepCost
  calc
    _ ≤ 1+(d.reverseCoreUnitCost CD CS CT*bound^3)*
        (max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*bound)*max U 2 := by
      gcongr
    _ ≤ bound^4+(d.reverseCoreUnitCost CD CS CT*bound^3)*
        (max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*bound)*max U 2 :=
      add_le_add hb4 le_rfl
    _ = _ := by ring

theorem reverseModelCost_le_quartic (d : OrdinaryModelConfig P initial)
    (CD CS CT CZ U bound : ℝ) (hCS : 0≤CS) (hCZ : 0≤CZ) (hb : 1≤bound)
    (hp : P.profileBound≤bound) (ha : P.referenceEnvelopeConstant≤bound) :
    d.reverseModelCost CD CS CT CZ U≤d.unitReverseModelCost CD CS CT CZ U*bound^4 := by
  have hG : 0≤8/(1-reverseThresholdRatio) :=
    (div_pos (by norm_num) (sub_pos.mpr reverseThresholdRatio_lt_one)).le
  have hstep := d.reverseStepCost_le_quartic CD CS CT CZ U bound hCS hCZ hb hp ha
  unfold reverseModelCost unitReverseModelCost
  calc
    _ ≤ 1+(8/(1-reverseThresholdRatio))*(d.unitReverseStepCost CD CS CT CZ U*bound^4) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep hG)
    _ ≤ bound^4+(8/(1-reverseThresholdRatio))*(d.unitReverseStepCost CD CS CT CZ U*bound^4) :=
      add_le_add (one_le_pow₀ hb) le_rfl
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig

end

end OAI
