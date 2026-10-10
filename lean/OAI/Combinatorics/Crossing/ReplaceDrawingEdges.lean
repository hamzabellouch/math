import OAI.Combinatorics.Crossing.ReconnectedVertexAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz.ContinuousDrawing
variable {m n : ℕ}

def replaceTwoRoutes (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (g : BipartiteEdge m n) : Path (D.vertex (.inl g.1)) (D.vertex (.inr g.2)) := by
  classical
  exact if h : g=e then γ.cast (congrArg (fun k : BipartiteEdge m n => D.vertex (.inl k.1)) h)
    (congrArg (fun k : BipartiteEdge m n => D.vertex (.inr k.2)) h)
  else if h : g=f then δ.cast (congrArg (fun k : BipartiteEdge m n => D.vertex (.inl k.1)) h)
    (congrArg (fun k : BipartiteEdge m n => D.vertex (.inr k.2)) h)
  else D.edge g

theorem replaceTwoRoutes_first (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2))) :
    D.replaceTwoRoutes e f γ δ e=γ := by
  simp only [replaceTwoRoutes,dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_second (D : ContinuousDrawing m n) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2))) :
    D.replaceTwoRoutes e f γ δ f=δ := by
  simp only [replaceTwoRoutes,dite_eq_right (Ne.symm hef),dite_eq_left rfl,Path.cast_rfl_rfl]

theorem replaceTwoRoutes_other (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (g : BipartiteEdge m n) (hge : g ≠ e) (hgf : g ≠ f) :
    D.replaceTwoRoutes e f γ δ g=D.edge g := by
  simp only [replaceTwoRoutes,dite_eq_right hge,dite_eq_right hgf]

def replaceTwoEdges (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hvγ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, γ t ≠ D.vertex j)
    (hvδ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, δ t ≠ D.vertex j) :
    ContinuousDrawing m n where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.replaceTwoRoutes e f γ δ
  edge_injective := by
    intro g
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hγ
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hδ
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.edge_injective g
  interior_avoids_vertices := by
    intro g t ht j
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hvγ t ht j
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hvδ t ht j
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.interior_avoids_vertices g t ht j

end Zarankiewicz.ContinuousDrawing

end

end OAI
