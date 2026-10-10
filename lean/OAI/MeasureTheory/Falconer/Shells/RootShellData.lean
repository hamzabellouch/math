import OAI.MeasureTheory.Falconer.Estimates.RootFiniteSeparation
import OAI.MeasureTheory.Falconer.Measures.RootNormalizedCoefficients

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

structure RootShellData where
  left : RootEndpointData
  right : RootEndpointData
  N : ℕ
  sig : ℝ
  U : DyadicSquare
  V : DyadicSquare

namespace RootShellData

noncomputable def indices (d : RootShellData) := rootMaskIndices d.left d.right
noncomputable def endpointLeft (d : RootShellData) (k : RootMaskIndex → ℕ) := rootLeftSymbol d.left d.N d.sig k
noncomputable def endpointRight (d : RootShellData) (k : RootMaskIndex → ℕ) := rootRightSymbol d.right d.N d.sig k
noncomputable def coefficient (d : RootShellData) (j : ℕ) (b : ℂ × (RootMaskIndex → ℕ)) :=
  rootAbsorbedCoefficient d.left d.right d.N d.sig j b
noncomputable def mainF (d : RootShellData) (n : ℕ) := rootNormalizedF d.left d.right d.N d.sig n d.U d.V
noncomputable def measure (d : RootShellData) := rootWeightedDistance d.left d.right d.N d.sig
noncomputable def cost (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) :=
  rootSpatialLeibnizCost δ L hδ hL d.left d.right j

theorem endpointLeft_measurable (d : RootShellData) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => d.endpointLeft k z.1 z.2) :=
  rootLeftSymbol_measurable d.left d.N d.sig k

theorem endpointRight_measurable (d : RootShellData) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => d.endpointRight k z.1 z.2) :=
  rootRightSymbol_measurable d.right d.N d.sig k

theorem endpointLeft_norm (d : RootShellData) (hd : 0 < d.left.Q.side) (j : ℕ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j d.indices) (x : Plane) (dir : UnitCircle) :
    ‖d.endpointLeft b.2 x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  rootLeftSymbol_norm d.left d.right hd d.N j d.sig hb x dir

theorem endpointRight_norm (d : RootShellData) (he : 0 < d.right.Q.side) (j : ℕ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j d.indices) (x : Plane) (dir : UnitCircle) :
    ‖d.endpointRight b.2 x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  rootRightSymbol_norm d.left d.right he d.N j d.sig hb x dir

theorem coefficient_norm (d : RootShellData) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) (j : ℕ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j d.indices) :
    ‖d.coefficient j b‖ ≤ ‖b.1‖ := rootAbsorbedCoefficient_norm d.left d.right d.N j hsig hL₁ hL₂ hb

end RootShellData

end PlanarFalconer

end OAI
