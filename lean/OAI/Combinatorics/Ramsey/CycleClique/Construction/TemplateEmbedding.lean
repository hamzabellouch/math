import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsideTemplate

namespace OAI

/-! Finite extension templates preserve their three numerical parameters
when transported to the counterexample graph. -/

namespace CycleClique.Construction.OutsideTemplate

variable {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
variable {Q₀ : Finset W} {Q : Finset V} {x y : W} {f : W → V}

def embed (T : OutsideTemplate H Q₀ x y) (f : W → V) (hf : Function.Injective f)
    (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    OutsideTemplate G Q (f x) (f y) where
  rest := T.rest.embed f hf hQ hG
  left := T.left.map f
  right := T.right.map f
  nodup := by
    simpa only [RawPathSystem.embed, ← List.map_flatten, List.map_append,
      List.map_cons] using T.nodup.map hf
  left_path := by
    simpa using List.isChain_map_of_isChain f (fun _ _ h => hG h) T.left_path
  right_path := List.isChain_map_of_isChain f (fun _ _ h => hG h) T.right_path
  start := by
    have he : T.left.map f ++ [f x] = (T.left ++ [x]).map f := by simp
    rw [he, List.head?_map]
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hv
    exact (hQ w).mpr (T.start w hw)
  finish := by
    change ∀ v ∈ ((y :: T.right).map f).getLast?, v ∈ Q
    rw [List.getLast?_map]
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hv
    exact (hQ w).mpr (T.finish w hw)
  left_steps := by
    simpa only [List.map_append, List.map_cons, List.map_nil] using
      List.isChain_map_of_isChain f (fun _ _ hn (hh : _ ∧ _) =>
      hn ⟨(hQ _).mp hh.1, (hQ _).mp hh.2⟩) T.left_steps
  right_steps := List.isChain_map_of_isChain f (fun _ _ hn (hh : _ ∧ _) =>
    hn ⟨(hQ _).mp hh.1, (hQ _).mp hh.2⟩) T.right_steps

@[simp] theorem embed_oldVertices (T : OutsideTemplate H Q₀ x y)
    (hf : Function.Injective f) (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (T.embed f hf hQ hG).oldVertices = T.oldVertices.map f := by
  simp only [oldVertices, embed, RawPathSystem.embed, ← List.map_flatten,
    List.map_append, List.map_cons]

@[simp] theorem embed_amount (T : OutsideTemplate H Q₀ x y)
    (hf : Function.Injective f) (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (T.embed f hf hQ hG).amount = T.amount := by
  unfold amount
  rw [embed_oldVertices, chainOutsideCount_map hQ]

@[simp] theorem embed_incidentBound (T : OutsideTemplate H Q₀ x y)
    (hf : Function.Injective f) (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (T.embed f hf hQ hG).incidentBound = T.incidentBound := by
  unfold incidentBound
  rw [embed_oldVertices, chainCliqueCount_map hQ]

@[simp] theorem embed_assignedCount (T : OutsideTemplate H Q₀ x y)
    (hf : Function.Injective f) (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (T.embed f hf hQ hG).assignedCount = T.assignedCount := by
  unfold assignedCount
  rw [show (T.embed f hf hQ hG).rest = T.rest.embed f hf hQ hG from rfl,
    RawPathSystem.embed_assignedCount]
  have he : (T.embed f hf hQ hG).left ++ f x :: f y :: (T.embed f hf hQ hG).right =
      (T.left ++ x :: y :: T.right).map f := by simp [embed]
  rw [he, chainCliqueCount_map hQ]

end CycleClique.Construction.OutsideTemplate

end OAI
