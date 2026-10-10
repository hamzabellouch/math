import OAI.Combinatorics.Ryser.Construction.AmbientDeletionSurvivors
import OAI.Combinatorics.Ryser.Construction.CoordinateCompatibility
import OAI.Combinatorics.Ryser.Construction.GadgetGood

namespace OAI

noncomputable section

open scoped Classical

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

theorem ambientSelectedSurvivors_projection_ne
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (x : Point F) (hx : x ∈ ambientSelectedSurvivors σ u v huv a K b choice)
    (i : ConfigurationGroup σ) (w : Point k) (hw : w ∈ retainedPoints a)
    (d : Direction F) (hd : d ∈ alteredDirections σ (groupPlacement σ u v huv i)) :
    projection d x ≠
      projection d (placedPoint σ (groupPlacement σ u v huv i) (b i (choice i)) w) := by
  intro hproj
  let ell := lineThrough d
    (placedPoint σ (groupPlacement σ u v huv i) (b i (choice i)) w)
  have hell : ell ∈ ambientSelectedLines σ u v huv a K b choice := by
    apply (mem_ambientSelectedLines σ u v huv a K b choice ell).mpr
    refine ⟨i, ?_⟩
    apply (mem_deletedLines σ (groupPlacement σ u v huv i) (b i (choice i)) a ell).mpr
    exact ⟨hd, w, hw, rfl⟩
  exact (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mp hx ell hell hproj

theorem DeletionSeparated.retained_projection_ne
    {G : Type*} [Fintype G] [DecidableEq G]
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i j : G) (hij : i ≠ j) (w : Point k) (hw : w ∈ retainedPoints a)
    (z : Point k) (d : Direction F) (hd : d ∈ alteredDirections σ (M i)) :
    projection d (placedPoint σ (M i) (b i) w) ≠
      projection d (placedPoint σ (M j) (b j) z) := by
  have hz : placedPoint σ (M j) (b j) z ∈ placedSubplane σ (M j) (b j) :=
    (mem_placedSubplane_iff σ (M j) (b j) _).mpr ⟨z, rfl⟩
  have hw' : placedPoint σ (M i) (b i) w ∈
      (retainedPoints a).image (placedPoint σ (M i) (b i)) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  exact (hsep j i (Ne.symm hij) _ hz _ hw' d hd).symm

def ambientSelectedConfiguration
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    ConfigurationData k F (ConfigurationGroup σ) :=
  placedConfiguration σ (groupPlacement σ u v huv) (fun i => b i (choice i))
    (retainedPoints a) (ambientSelectedSurvivors σ u v huv a K b choice)

theorem ambientSelectedHypergraph_intersecting
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hsep : DeletionSeparated σ (groupPlacement σ u v huv)
      (fun i => b i (choice i)) a) :
    Intersecting (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) := by
  apply placedHypergraph_intersecting σ (groupPlacement σ u v huv)
    (fun i => b i (choice i)) (retainedPoints a)
    (ambientSelectedSurvivors σ u v huv a K b choice) hcop
  · intro x hx i w hw d hd
    exact ambientSelectedSurvivors_projection_ne σ u v huv a K b choice x hx i w hw d hd
  · intro i j hij w hw z _ d hd
    exact DeletionSeparated.retained_projection_ne σ (groupPlacement σ u v huv)
      (fun i => b i (choice i)) a hsep i j hij w hw z d hd

theorem ambientSelectedHypergraph_nonempty
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (ha : GoodGadget a) :
    (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)).Nonempty := by
  exact hypergraph_nonempty (ambientSelectedConfiguration σ u v huv a K b choice)
    none ha.retained_nonempty

theorem ambientSelectedHypergraph_partite
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    PartiteUniform (vertexPart (ambientSelectedConfiguration σ u v huv a K b choice))
      (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) :=
  hypergraph_partite (ambientSelectedConfiguration σ u v huv a K b choice)

theorem ambientSelectedHypergraph_uniform
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    Uniform (Fintype.card F + 1)
      (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) :=
  hypergraph_uniform (ambientSelectedConfiguration σ u v huv a K b choice)

theorem ambientSelectedHypergraph_rPartiteUniform
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    RPartiteUniform (Fintype.card F + 1)
      (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) :=
  hypergraph_rPartiteUniform (ambientSelectedConfiguration σ u v huv a K b choice)

theorem ambientSelectedHypergraph_properties
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (ha : GoodGadget a)
    (hsep : DeletionSeparated σ (groupPlacement σ u v huv)
      (fun i => b i (choice i)) a) :
    (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)).Nonempty ∧
      Intersecting (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) ∧
      RPartiteUniform (Fintype.card F + 1)
        (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) :=
  ⟨ambientSelectedHypergraph_nonempty σ u v huv a K b choice ha,
    ambientSelectedHypergraph_intersecting σ u v huv a K b choice hcop hsep,
    ambientSelectedHypergraph_rPartiteUniform σ u v huv a K b choice⟩

end RyserCoveringCounterexample.Construction

end

end OAI
