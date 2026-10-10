import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeLanes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPatchSeparation

namespace OAI

/-! Polynomially many isolated crossings, with a constant bound along each route. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem lane_color_at_point (hA : 0 < A) {e f : M.Term} {z : ℕ × ℕ}
    (he : M.laneSupport e z) (hf : M.laneSupport f z)
    (hcolor : M.laneColor e = M.laneColor f) : e = f := by
  by_contra hne
  exact Set.disjoint_left.mp (M.lane_color_disjoint hA hne hcolor) he hf

theorem lane_crossing_unique (hA : 0 < A) {e f g : M.Term} (hef : e ≠ f) {z : ℕ × ℕ}
    (he : M.laneSupport e z) (hf : M.laneSupport f z) (hg : M.laneSupport g z) : g = e ∨ g = f := by
  have hg' := hg
  have hcolor := M.lane_intersection_colors hA hef he hf
  rcases qmaLaneSupport_transverse hcolor he hf with ⟨eh,fv⟩ | ⟨ev,fh⟩
  · rcases hg' with ⟨gh,_⟩ | ⟨gv,_⟩
    · exact Or.inl (M.lane_color_at_point hA hg he
        (qmaHorizontalLane_color gh eh))
    · exact Or.inr (M.lane_color_at_point hA hg hf
        (qmaVerticalLane_color gv fv))
  · rcases hg' with ⟨gh,_⟩ | ⟨gv,_⟩
    · exact Or.inr (M.lane_color_at_point hA hg hf
        (qmaHorizontalLane_color gh fh))
    · exact Or.inl (M.lane_color_at_point hA hg he
        (qmaVerticalLane_color gv ev))

def crossingCandidates (e f : M.Term) : Finset (ℕ × ℕ) :=
  { (9*B*(qmaFineGridNat (M.routeRight f)).1+(M.laneColor f).val,
      9*B*(qmaFineGridNat (M.routeLeft e)).2+(M.laneColor e).val),
    (9*B*(qmaFineGridNat (M.routeRight e)).1+(M.laneColor e).val,
      9*B*(qmaFineGridNat (M.routeLeft f)).2+(M.laneColor f).val) }

def crossings : Finset (ℕ × ℕ) := Finset.univ.biUnion fun p : M.Term × M.Term =>
  (M.crossingCandidates p.1 p.2).filter (fun z => p.1 ≠ p.2 ∧ M.laneSupport p.1 z ∧ M.laneSupport p.2 z)

theorem mem_crossings (hA : 0 < A) (z : ℕ × ℕ) :
    z ∈ M.crossings ↔ ∃ e f, e ≠ f ∧ M.laneSupport e z ∧ M.laneSupport f z := by
  constructor
  · intro hz
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hz
    exact ⟨p.1,p.2,(Finset.mem_filter.mp hp).2⟩
  · rintro ⟨e,f,hef,he,hf⟩
    refine Finset.mem_biUnion.mpr ⟨(e,f),Finset.mem_univ _,Finset.mem_filter.mpr ⟨?_,hef,he,hf⟩⟩
    have h := qmaLaneSupport_two_crossings (M.lane_intersection_colors hA hef he hf) he hf
    simpa only [crossingCandidates,Finset.mem_insert,Finset.mem_singleton] using h

theorem crossings_card : M.crossings.card ≤ 2*(Fintype.card M.Term)^2 := by
  unfold crossings
  refine Finset.card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _p : M.Term × M.Term, 2 := Finset.sum_le_sum (fun p _ =>
      (Finset.card_filter_le _ _).trans (Finset.card_le_two))
    _ = _ := by simp [pow_two,Nat.mul_comm]

def routeCrossings (e : M.Term) : Finset (ℕ × ℕ) := M.crossings.filter (M.laneSupport e)

theorem routeCrossings_card (e : M.Term) : (M.routeCrossings e).card ≤ 9*B*(3*A+2)+1 := by
  let p := qmaLanePoint (M.laneColor e) (qmaFineGridNat (M.routeLeft e))
  let q := qmaLanePoint (M.laneColor e) (qmaFineGridNat (M.routeRight e))
  have hsub : M.routeCrossings e ⊆ Finset.univ.image (qmaManhattanRoute p q) := by
    intro z hz
    have hs := (Finset.mem_filter.mp hz).2
    obtain ⟨k,hk⟩ := (qmaManhattanRoute_range p q z).mpr hs
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hk⟩
  calc
    _ ≤ (Finset.univ.image (qmaManhattanRoute p q)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin (qmaManhattanLength p q+1))).card := Finset.card_image_le
    _ = qmaManhattanLength p q+1 := by simp
    _ ≤ _ := Nat.add_le_add_right (M.lane_length e) 1

theorem crossing_not_vertex (hA : 0 < A) {z : ℕ × ℕ} (hz : z ∈ M.crossings)
    (e : M.Term) (p : ℕ × ℕ) : z ≠ qmaLanePoint (M.laneColor e) p := by
  obtain ⟨f,g,hfg,hf,hg⟩ := (M.mem_crossings hA z).mp hz
  exact M.lane_intersection_not_vertex hA hfg hf hg e p

theorem crossing_boxes_disjoint {p q : ℕ × ℕ} (_hp : p ∈ M.crossings) (_hq : q ∈ M.crossings)
    (hpq : p ≠ q) : Disjoint (qmaPatchBox p) (qmaPatchBox q) := qmaPatchBox_disjoint hpq

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
