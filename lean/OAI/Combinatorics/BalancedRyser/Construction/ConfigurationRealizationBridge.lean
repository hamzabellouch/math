import OAI.Combinatorics.BalancedRyser.Construction.ConfigurationHypergraph
import OAI.Combinatorics.BalancedRyser.Construction.ConstructionRepresentationLemmas

namespace OAI

namespace Balanced.Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

noncomputable def blockLabelDirectionEquiv :
    {b : BlockLabel F // b ∈ C.blockLabels} ≃
      (d : Direction F) × {b // b ∈ C.labelsInDirection d} := by
  classical
  refine {
    toFun := fun b => ⟨blockDirection b.val,
      ⟨b.val, Finset.mem_filter.mpr ⟨b.property, rfl⟩⟩⟩
    invFun := fun db => ⟨db.2.val, (Finset.mem_filter.mp db.2.property).1⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro b
    rfl
  · rintro ⟨d, b, hb⟩
    have hd : blockDirection b = d := (Finset.mem_filter.mp hb).2
    subst d
    rfl

theorem Represents.realization
    {H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1)}
    (h : C.Represents H) : Nonempty (ConfigurationRealization C H) := by
  rcases h with ⟨eD, eL, eP, hinc⟩
  refine ⟨{
    directionEquiv := eD
    labelEquiv := (C.blockLabelDirectionEquiv).trans (encodeLabel eD eL)
    edgeEquiv := eP
    label_direction := ?_
    incidence := ?_
  }⟩
  · intro b
    rfl
  · intro p b
    exact hinc p (blockDirection b.val)
      ⟨b.val, Finset.mem_filter.mpr ⟨b.property, rfl⟩⟩

theorem constructedHypergraph_realization (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) {ρ : ℝ} {B : ℕ}
    (hρ : ρ < 1) (hO : C.Occupancy ρ B)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    Nonempty (ConfigurationRealization C (C.constructedHypergraph hV hC hq)) :=
  (C.constructedHypergraph_represents hV hC hq hρ hO hsize).realization C

end Balanced.Configuration

end OAI
