import OAI.NumberTheory.Ostmann.Tree.CycleLocalMajorantsCoefficients
import OAI.NumberTheory.Ostmann.Tree.IndependentUniformBound
import OAI.NumberTheory.Ostmann.Tree.QuartetFactorization

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Ostmann.FiniteField QuartetFactorization CycleQuartet
variable {p : ℕ} [Fact p.Prime] {k b : ℕ}
local instance treeMajorantFintype : Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _
local instance treeMajorantDecEq : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

def treeMajorant (P : LeafPartition (k+2) b)
    (c : BalancedSelection P.label (quartetCut k).label)
    (T : Diagram (ZMod p) (k+2)) (g : ZMod p → ℂ) (y : Leaves k → (ZMod p)ˣ) : ℝ :=
  constrainedMajorant (fun _ : Leaves k => Equiv.refl (MulChar (ZMod p) ℂ))
    (fun v ρ (u : (ZMod p)ˣ) => localMajorant P c (bottomParameters k T.parameters) g v ρ u) y

theorem treeMajorant_nonneg (P : LeafPartition (k+2) b)
    (c : BalancedSelection P.label (quartetCut k).label)
    (T : Diagram (ZMod p) (k+2)) (g : ZMod p → ℂ) (y : Leaves k → (ZMod p)ˣ) :
    0≤treeMajorant P c T g y :=
  constrainedMajorant_nonneg (fun _ : Leaves k => Equiv.refl (MulChar (ZMod p) ℂ))
    (fun v ρ (u : (ZMod p)ˣ) => localMajorant P c (bottomParameters k T.parameters) g v ρ u)
    (fun v ρ u => localMajorant_nonneg P c (bottomParameters k T.parameters) g v ρ u) y

theorem treeMajorant_mean (P : LeafPartition (k+2) b)
    (c : BalancedSelection P.label (quartetCut k).label)
    (T : Diagram (ZMod p) (k+2)) (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    Density.average (treeMajorant P c T g)≤(25600*treeError g)*(256:ℝ)^(2^k) := by
  obtain ⟨j,hj⟩ := cycleQuartets_nonempty P c
  have hsmall (ρ : MulChar (ZMod p) ℂ) :
      Density.average (fun u : (ZMod p)ˣ => localMajorant P c (bottomParameters k T.parameters) g j ρ u)≤
      25600*treeError g := localMajorant_mean_small P c _ g j hj ρ hg0 hg
  have hmass (v : Leaves k) :
      (∑ ρ : MulChar (ZMod p) ℂ,Density.average
        (fun u : (ZMod p)ˣ => localMajorant P c (bottomParameters k T.parameters) g v ρ u))≤256 :=
    localMajorant_mean_total P c _ g v hg0 hg
  have h := constrainedMajorant_average_uniform (A:=fun _ : Leaves k => (ZMod p)ˣ)
    (fun _ : Leaves k => Equiv.refl (MulChar (ZMod p) ℂ))
    (fun v ρ (u : (ZMod p)ˣ) => localMajorant P c (bottomParameters k T.parameters) g v ρ u)
    (fun v ρ u => localMajorant_nonneg P c _ g v ρ u)
    j (25600*treeError g) 256 (mul_nonneg (by norm_num) (treeError_nonneg g)) (by norm_num)
    hsmall hmass
  unfold treeMajorant
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using h

def treeProjectionConstant (k : ℕ) : ℝ :=
  ((2^(2^k-1):ℕ):ℝ)*25600*(256:ℝ)^(2^k)

theorem treeProjectionConstant_nonneg (k : ℕ) : 0≤treeProjectionConstant k := by
  unfold treeProjectionConstant
  positivity

end
end Ostmann.Tree

end OAI
