import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEndpointPorts

namespace OAI

/-! Eightfold lane spacing leaves room for the buffered endpoint arms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaSpacedLaneColor {C : ℕ} (c : Fin C) : Fin (8*(C+6)) := ⟨8*(c.val+3),by omega⟩

theorem qmaSpacedLaneColor_injective (C : ℕ) : Function.Injective (@qmaSpacedLaneColor C) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [qmaSpacedLaneColor] at hh
  omega

theorem qmaSpacedEndpoint {C : ℕ} (p : ℕ × ℕ) (c : Fin C) :
    qmaLanePoint (qmaSpacedLaneColor c) p =
      qmaBufferedCellPoint C p (8*(c.val+3),8*(c.val+3)) := by
  apply Prod.ext <;> dsimp [qmaSpacedLaneColor,qmaLanePoint,qmaBufferedCellPoint]

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def spacedColor (e : M.Term) : Fin (8*(9*B+9)) :=
  qmaSpacedLaneColor ((M.laneColor e).castAdd 3)

def spacedSupport (e : M.Term) (z : ℕ × ℕ) : Prop :=
  qmaLaneSupport (M.spacedColor e) (qmaFineGridNat (M.routeLeft e))
    (qmaFineGridNat (M.routeRight e)) z

theorem spacedColor_eq {e f : M.Term} (h : M.spacedColor e = M.spacedColor f) :
    M.laneColor e = M.laneColor f := by
  have hc := qmaSpacedLaneColor_injective (9*B+3) h
  apply Fin.ext
  exact congrArg (fun c : Fin (9*B+3) => c.val) hc

theorem spaced_color_disjoint (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    (hcolor : M.spacedColor e = M.spacedColor f) :
    Disjoint {z | M.spacedSupport e z} {z | M.spacedSupport f z} := by
  have hc := M.spacedColor_eq hcolor
  have hd := M.routes_of_color_disjoint hA hef ((qmaGridColorEquiv B).injective hc)
  have hs : Disjoint
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e)) z}
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft f)) (qmaFineGridNat (M.routeRight f)) z} := by
    apply Set.disjoint_left.mpr
    intro z he hf
    obtain ⟨u,hu,huz⟩ := (qmaFineRouteSites_nat _ _ z).mp he
    obtain ⟨v,hv,hvz⟩ := (qmaFineRouteSites_nat _ _ z).mp hf
    have huv := qmaFineGridNat_injective (huz.trans hvz.symm)
    subst v
    exact Finset.disjoint_left.mp hd hu hv
  change Disjoint {z | qmaLaneSupport (M.spacedColor e) _ _ z}
    {z | qmaLaneSupport (M.spacedColor f) _ _ z}
  rw [← hcolor]
  exact qmaLaneSupport_disjoint _ hs

theorem spaced_length (e : M.Term) :
    qmaManhattanLength (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeLeft e)))
      (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeRight e))) ≤
        8*(9*B+9)*(3*A+2) := by
  rw [qmaLane_length]
  exact Nat.mul_le_mul_left _ (M.routeLength_bound e)

theorem spaced_crossing_not_vertex (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (he : M.spacedSupport e z) (hf : M.spacedSupport f z)
    (g : M.Term) (p : ℕ × ℕ) : z ≠ qmaLanePoint (M.spacedColor g) p := by
  have hc : M.spacedColor e ≠ M.spacedColor f := fun h =>
    Set.disjoint_left.mp (M.spaced_color_disjoint hA hef h) he hf
  exact qmaLaneSupport_crossing_not_vertex hc he hf _ p

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
