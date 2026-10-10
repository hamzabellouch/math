import OAI.Geometry.PeriodicTiling.ConstraintCycles
import OAI.Geometry.PeriodicTiling.ActivationTiles

namespace OAI

noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def testTiles : Finset (Finset (Ambient E)) := by
  classical
  exact {kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪
    seedConstraintTiles E ∪ Finset.univ.image (ordinaryActivationTile E) ∪
    Finset.univ.image (seedActivationTile E)

theorem mem_testTiles_iff (F : Finset (Ambient E)) :
    F ∈ testTiles E ↔ F = kernelTile E ∨ F ∈ dependenceTiles E ∨
      F ∈ wordConstraintTiles E ∨ F ∈ seedConstraintTiles E ∨
      (∃ n : Column p, ordinaryActivationTile E n = F) ∨
      (∃ t : Fin 2, seedActivationTile E t = F) := by
  classical
  simp only [testTiles, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and, or_assoc]

theorem kernelTile_mem_testTiles : kernelTile E ∈ testTiles E :=
  (mem_testTiles_iff E _).mpr (Or.inl rfl)

theorem dependenceTiles_subset_testTiles : dependenceTiles E ⊆ testTiles E := by
  intro F hF
  exact (mem_testTiles_iff E F).mpr (Or.inr (Or.inl hF))

theorem wordConstraintTiles_subset_testTiles : wordConstraintTiles E ⊆ testTiles E := by
  intro F hF
  exact (mem_testTiles_iff E F).mpr (Or.inr (Or.inr (Or.inl hF)))

theorem seedConstraintTiles_subset_testTiles : seedConstraintTiles E ⊆ testTiles E := by
  intro F hF
  exact (mem_testTiles_iff E F).mpr (Or.inr (Or.inr (Or.inr (Or.inl hF))))

theorem ordinaryActivationTile_mem_testTiles (n : Column p) :
    ordinaryActivationTile E n ∈ testTiles E :=
  (mem_testTiles_iff E _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))

theorem seedActivationTile_mem_testTiles (t : Fin 2) :
    seedActivationTile E t ∈ testTiles E :=
  (mem_testTiles_iff E _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, rfl⟩)))))

theorem testTiles_nonempty : (testTiles E).Nonempty :=
  ⟨kernelTile E, kernelTile_mem_testTiles E⟩

theorem nonempty_of_mem_testTiles {F : Finset (Ambient E)}
    (hF : F ∈ testTiles E) : F.Nonempty := by
  classical
  rcases (mem_testTiles_iff E F).mp hF with rfl | hF | hF | hF | ⟨n, rfl⟩ | ⟨t, rfl⟩
  · exact kernelTile_nonempty E
  · obtain ⟨d, _hd, rfl⟩ := Finset.mem_image.mp hF
    exact invarianceTile_nonempty E (dependenceChannel d) (dependenceShift E d)
  · exact nonempty_of_mem_wordConstraintTiles E hF
  · exact nonempty_of_mem_seedConstraintTiles E hF
  · exact ordinaryActivationTile_nonempty E n
  · exact seedActivationTile_nonempty E t

def Solves (A : Set (Ambient E)) : Prop :=
  ∀ F ∈ testTiles E, Tiles F A

theorem solves_iff (A : Set (Ambient E)) : Solves E A ↔
    Tiles (kernelTile E) A ∧
    (∀ F ∈ dependenceTiles E, Tiles F A) ∧
    (∀ F ∈ wordConstraintTiles E, Tiles F A) ∧
    (∀ F ∈ seedConstraintTiles E, Tiles F A) ∧
    (∀ n, Tiles (ordinaryActivationTile E n) A) ∧
    (∀ t, Tiles (seedActivationTile E t) A) := by
  constructor
  · intro h
    exact ⟨h _ (kernelTile_mem_testTiles E),
      fun F hF => h F (dependenceTiles_subset_testTiles E hF),
      fun F hF => h F (wordConstraintTiles_subset_testTiles E hF),
      fun F hF => h F (seedConstraintTiles_subset_testTiles E hF),
      fun n => h _ (ordinaryActivationTile_mem_testTiles E n),
      fun t => h _ (seedActivationTile_mem_testTiles E t)⟩
  · rintro ⟨hg, hd, hw, hs, ha, hb⟩ F hF
    rcases (mem_testTiles_iff E F).mp hF with rfl | hF | hF | hF | ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exact hg
    · exact hd F hF
    · exact hw F hF
    · exact hs F hF
    · exact ha n
    · exact hb t

abbrev TestIndex := ↥(testTiles E)

def testTile (i : TestIndex E) : Finset (Ambient E) := i.val

theorem testTile_nonempty (i : TestIndex E) : (testTile E i).Nonempty :=
  nonempty_of_mem_testTiles E i.property

instance testIndex_nonempty : Nonempty (TestIndex E) :=
  ⟨⟨kernelTile E, kernelTile_mem_testTiles E⟩⟩

theorem solves_iff_index (A : Set (Ambient E)) :
    Solves E A ↔ ∀ i : TestIndex E, Tiles (testTile E i) A := by
  constructor
  · intro h i
    exact h i.val i.property
  · intro h F hF
    exact h ⟨F, hF⟩

theorem exists_graph_of_solves {A : Set (Ambient E)} (hA : Solves E A) :
    ∃ o : GraphOutputs E, graph o = A :=
  (kernelTile_iff_graph E A).mp (hA _ (kernelTile_mem_testTiles E))

end PeriodicTilingThree

end

end OAI
