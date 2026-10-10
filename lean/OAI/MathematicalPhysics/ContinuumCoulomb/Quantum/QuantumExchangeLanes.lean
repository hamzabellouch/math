import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLaneSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeRoutes

namespace OAI

/-! Separated lanes for the actual spatial exchange family. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGridColorEquiv (B : ℕ) : (Fin 3 × Fin 3 × Fin B) ≃ Fin (9*B) :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by omega))

theorem qmaFineGridNat_injective {rows width A : ℕ} :
    Function.Injective (@qmaFineGridNat rows width A) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem qmaFineRouteSites_nat {rows width A : ℕ} (p q : QMAFineGrid rows width A) (z : ℕ × ℕ) :
    qmaManhattanSupport (qmaFineGridNat p) (qmaFineGridNat q) z ↔
      ∃ w ∈ qmaFineRouteSites p q, qmaFineGridNat w = z := by
  constructor
  · intro hz
    obtain ⟨k,hk,he⟩ := qmaManhattanSupport_point hz
    refine ⟨qmaFineRoute p q ⟨k,by omega⟩,?_,?_⟩
    · exact Finset.mem_image.mpr ⟨⟨k,by omega⟩,Finset.mem_univ _,rfl⟩
    · exact he
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hw
    exact qmaManhattanPoint_support _ _ k.val (by omega)

theorem qmaLane_length {C : ℕ} (c : Fin C) (p q : ℕ × ℕ) :
    qmaManhattanLength (qmaLanePoint c p) (qmaLanePoint c q) = C*qmaManhattanLength p q := by
  simp only [qmaManhattanLength,qmaLanePoint,Nat.dist_add_add_right,Nat.dist_mul_left,Nat.mul_add]

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def laneColor (e : M.Term) : Fin (9*B) := qmaGridColorEquiv B (M.termSlots.color e)
def laneSupport (e : M.Term) (z : ℕ × ℕ) : Prop :=
  qmaLaneSupport (M.laneColor e) (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e)) z

theorem lane_length (e : M.Term) :
    qmaManhattanLength (qmaLanePoint (M.laneColor e) (qmaFineGridNat (M.routeLeft e)))
      (qmaLanePoint (M.laneColor e) (qmaFineGridNat (M.routeRight e))) ≤ 9*B*(3*A+2) := by
  rw [qmaLane_length]
  exact Nat.mul_le_mul_left _ (M.routeLength_bound e)

theorem lane_color_disjoint (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    (hcolor : M.laneColor e = M.laneColor f) :
    Disjoint {z | M.laneSupport e z} {z | M.laneSupport f z} := by
  have hc : M.termSlots.color e = M.termSlots.color f :=
    (qmaGridColorEquiv B).injective hcolor
  have hd := M.routes_of_color_disjoint hA hef hc
  have hsupport : Disjoint
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e)) z}
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft f)) (qmaFineGridNat (M.routeRight f)) z} := by
    apply Set.disjoint_left.mpr
    intro z he hf
    obtain ⟨u,hu,huz⟩ := (qmaFineRouteSites_nat _ _ z).mp he
    obtain ⟨v,hv,hvz⟩ := (qmaFineRouteSites_nat _ _ z).mp hf
    have huv := qmaFineGridNat_injective (huz.trans hvz.symm)
    subst v
    exact Finset.disjoint_left.mp hd hu hv
  change Disjoint {z | qmaLaneSupport (M.laneColor e) _ _ z}
    {z | qmaLaneSupport (M.laneColor f) _ _ z}
  rw [← hcolor]
  exact qmaLaneSupport_disjoint _ hsupport

theorem lane_intersection_colors (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (he : M.laneSupport e z) (hf : M.laneSupport f z) : M.laneColor e ≠ M.laneColor f :=
  fun hc => Set.disjoint_left.mp (M.lane_color_disjoint hA hef hc) he hf

theorem lane_intersection_not_vertex (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (he : M.laneSupport e z) (hf : M.laneSupport f z)
    (g : M.Term) (p : ℕ × ℕ) : z ≠ qmaLanePoint (M.laneColor g) p :=
  qmaLaneSupport_crossing_not_vertex (M.lane_intersection_colors hA hef he hf) he hf _ p

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
