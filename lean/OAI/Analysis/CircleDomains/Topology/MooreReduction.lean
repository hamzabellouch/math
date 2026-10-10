import OAI.Analysis.CircleDomains.Selection.CollapseRelation
import OAI.Analysis.CircleDomains.Selection.Nonseparation
import Mathlib.Topology.Compactification.OnePoint.Sphere

namespace OAI

/-!
# The published Moore input and its application

Published input: R. L. Moore, *Concerning upper semi-continuous collections
of continua*, Trans. Amer. Math. Soc. 27 (1925), 416–428.
The proposition `MooreSphereDecomposition` is the closed-equivalence-relation
form of the sphere decomposition theorem needed in §2 of the Koebe manuscript.
It is an explicit hypothesis, not a global axiom.  The application below
verifies its hypotheses for complementary components and proves the dust
conclusion separately.
-/

open Set Topology

namespace CircleDomainRigidity

/-- The precise topological published input.  Singleton classes are allowed;
every other class is connected and has connected nonempty complement. -/
def MooreSphereDecomposition : Prop :=
  ∀ r : Setoid Sphere,
    IsClosed {p : Sphere × Sphere | r.r p.1 p.2} →
    (∀ x, {y | r.r x y} = {x} ∨
      (IsConnected {y | r.r x y} ∧ IsConnected {y | r.r x y}ᶜ)) →
    ∃ π : Sphere → Sphere, Continuous π ∧ Function.Surjective π ∧
      ∀ x y, π x = π y ↔ r.r x y

/-- The equivalence relation collapsing exactly the complementary components. -/
def componentSetoid (G : Set Sphere) : Setoid Sphere where
  r x y := x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | ⟨hx, hxy⟩
      · exact Or.inl h.symm
      · refine Or.inr ⟨connectedComponentIn_subset _ _ hxy, ?_⟩
        rw [← connectedComponentIn_eq hxy]
        exact mem_connectedComponentIn hx
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hxy⟩
      · exact hyz
      rcases hyz with rfl | ⟨_, hyz⟩
      · exact Or.inr ⟨hx, hxy⟩
      · refine Or.inr ⟨hx, ?_⟩
        rw [connectedComponentIn_eq hxy]
        exact hyz }

private theorem componentSetoid_class_of_mem {G : Set Sphere} {x : Sphere} (hx : x ∈ G) :
    {y | (componentSetoid G).r x y} = {x} := by
  ext y
  constructor
  · rintro (h | ⟨hx', _⟩)
    · exact h.symm
    · exact (hx' hx).elim
  · intro h
    exact Or.inl h.symm

private theorem componentSetoid_class_of_notMem {G : Set Sphere} {x : Sphere} (hx : x ∉ G) :
    {y | (componentSetoid G).r x y} = connectedComponentIn Gᶜ x := by
  ext y
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h ▸ mem_connectedComponentIn hx
    · exact h
  · exact fun h => Or.inr ⟨hx, h⟩

private theorem locallyConnected_sphere : LocallyConnectedSpace Sphere := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let : LocallyConnectedSpace S :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
  let e : Sphere ≃ₜ S := onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)
  exact e.locallyConnectedSpace

/-- The component quotient in §2, conditional solely on the named published
Moore theorem.  Its total-disconnectedness conclusion is proved here. -/
theorem componentSphereQuotient_of_moore (hMoore : MooreSphereDecomposition)
    {G : Set Sphere} (hopen : IsOpen G) (hconn : IsConnected G) :
    ∃ π : Sphere → Sphere, Continuous π ∧ IsClosedMap π ∧ Function.Surjective π ∧
      (∀ x y, π x = π y ↔
        x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) ∧
      IsTotallyDisconnected (π '' G)ᶜ := by
  let : LocallyConnectedSpace Sphere := locallyConnected_sphere
  have hclosed : IsClosed {p : Sphere × Sphere | (componentSetoid G).r p.1 p.2} :=
    isClosed_componentCollapseRelation hopen.isClosed_compl
  have hclasses (x : Sphere) : {y | (componentSetoid G).r x y} = {x} ∨
      (IsConnected {y | (componentSetoid G).r x y} ∧
        IsConnected {y | (componentSetoid G).r x y}ᶜ) := by
    by_cases hx : x ∈ G
    · exact Or.inl (componentSetoid_class_of_mem hx)
    · right
      rw [componentSetoid_class_of_notMem hx]
      exact ⟨isConnected_connectedComponentIn_iff.mpr hx,
        nonseparating_complementaryComponent hopen hconn hx⟩
  obtain ⟨π, hc, hs, hr⟩ := hMoore (componentSetoid G) hclosed hclasses
  have hcl : IsClosedMap π := hc.isClosedMap
  exact ⟨π, hc, hcl, hs, hr,
    totallyDisconnected_of_component_collapse G hopen π hc hcl hs hr⟩

end CircleDomainRigidity

end OAI
