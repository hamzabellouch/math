import OAI.Analysis.LipschitzHilbert.Estimates.OrdinaryModelConstruction
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelCostPolynomial
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReverseCost

namespace OAI

/-! The cost of the constructed ordinary models is a fixed number.
In particular it has no dependence on the finite lattice or translation. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

def OrdinaryModelNumerics.modelUnitCost {cStar cEta cb radius : ℝ}
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT : ℝ) : ℝ :=
  1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*
    (Real.sqrt 2*(2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD (3*M) num.K 1)+
      ((21^2:ℕ):ℝ)*ordinaryTreeUnitCost CT (3*M) num.K 1*
        (4*(selectedNearUnitCost num.gap M 1+
          2*Real.sqrt (2*selectedFarUnitCost cb (Real.sqrt 2) CS num.packGap M 1)))))

theorem OrdinaryModelConfig.unitModelCost_of_numeric_fields
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}
    (d : OrdinaryModelConfig P initial) (cStar cEta cb radius : ℝ)
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT : ℝ)
    (hcb : d.cb=cb) (hM : d.M=M) (hQ : d.Q=1) (hR : d.R=1)
    (hgap : d.gap=num.gap) (hpack : d.packGap=num.packGap)
    (hK : d.K=num.K) (hD0 : d.D0=5) (hLip : d.Lip=1) :
    d.unitModelCost CD CS CT=num.modelUnitCost M CD CS CT := by
  simp only [OrdinaryModelConfig.unitModelCost,OrdinaryModelConfig.unitStepCost,
    OrdinaryModelConfig.unitSizeAreaCost,hcb,hM,hQ,hR,hgap,hpack,hK,hD0,hLip]
  rfl

def OrdinaryModelNumerics.reverseUnitCost {cStar cEta cb radius : ℝ}
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT CZ : ℝ) : ℝ :=
  1+(8/(1-reverseThresholdRatio))*
    (1+(2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD (3*M) num.K 1)+
      ((21^2:ℕ):ℝ)*ordinaryTreeUnitCost CT (3*M) num.K 1*
        (4*(selectedNearUnitCost num.gap M 1+
          2*Real.sqrt (2*selectedFarUnitCost cb (Real.sqrt 2) CS num.packGap M 1))))*
      max (Real.sqrt (1+((3*M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*max ordinaryDensityUpper 2)

theorem OrdinaryModelConfig.unitReverseModelCost_of_numeric_fields
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}
    (d : OrdinaryModelConfig P initial) (cStar cEta cb radius : ℝ)
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT CZ : ℝ)
    (hcb : d.cb=cb) (hM : d.M=M) (hQ : d.Q=1) (hR : d.R=1)
    (hgap : d.gap=num.gap) (hpack : d.packGap=num.packGap)
    (hK : d.K=num.K) (hD0 : d.D0=5) (hLip : d.Lip=1) :
    d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper=num.reverseUnitCost M CD CS CT CZ := by
  simp only [OrdinaryModelConfig.unitReverseModelCost,OrdinaryModelConfig.unitReverseStepCost,
    OrdinaryModelConfig.reverseCoreUnitCost,OrdinaryModelConfig.unitSizeAreaCost,
    hcb,hM,hQ,hR,hgap,hpack,hK,hD0,hLip]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
