import Mathlib

namespace OAI

/-!
Ordered moment graphs, sheaves, flabbiness, sections and boundary images.
-/

section


/-! The finite-section extension argument required by source §4.3. No BMP
character theorem is postulated. These definitions are ordinary module-valued
sheaves on a directed ordered graph; labels enter later through which edge
modules vanish after localization. -/

namespace KLInvariance.MomentGraph

universe u v w z

structure OrderedGraph (V : Type v) [PartialOrder V] (E : Type w) where
  source : E → V
  target : E → V
  increasing : ∀ e, source e < target e

variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}

structure Sheaf (G : OrderedGraph V E) where
  vertex : V → ModuleCat.{z} R
  edge : E → ModuleCat.{z} R
  lower : ∀ e, (vertex (G.source e)) →ₗ[R] edge e
  upper : ∀ e, (vertex (G.target e)) →ₗ[R] edge e

namespace Sheaf
variable {G : OrderedGraph V E} (B : Sheaf (R := R) G)

abbrev Assignment := ∀ x, B.vertex x

/-- Exactly the usual section compatibility on edges with both endpoints in
`Ω`; coordinates outside `Ω` are ignored and can be chosen arbitrarily. -/
def CompatibleOn (Ω : Set V) (f : B.Assignment) : Prop :=
  ∀ e, G.source e ∈ Ω → G.target e ∈ Ω →
    B.lower e (f (G.source e)) = B.upper e (f (G.target e))

def IsGlobal (f : B.Assignment) : Prop := B.CompatibleOn Set.univ f

/-- Extension of ordinary sections over ambient upper sets. -/
def Flabby : Prop :=
  ∀ Ω : Set V, IsUpperSet Ω → ∀ f : B.Assignment, B.CompatibleOn Ω f →
    ∃ g : B.Assignment, B.IsGlobal g ∧ ∀ x ∈ Ω, g x = f x

/-- Closure under the edges whose modules survive, strictly weaker than
being an ambient upper set. -/
def ClosedUnder (_B : Sheaf (R := R) G) (live : Set E) (Ω : Set V) : Prop :=
  ∀ e ∈ live, G.source e ∈ Ω → G.target e ∈ Ω

theorem compatible_mono {Ω Ω' : Set V} {f : B.Assignment}
    (hf : B.CompatibleOn Ω f) (h : Ω' ⊆ Ω) : B.CompatibleOn Ω' f :=
  fun e hs ht => hf e (h hs) (h ht)

/-- One step of the descending extension in `loc:relative-flabbiness`.
Previously assigned lower neighbors can only be on zero edge modules. -/
theorem extend_one (hb : B.Flabby) (live : Set E)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (Ω : Set V) (hΩ : B.ClosedUnder live Ω) (a : V) (ha : a ∉ Ω)
    (hmax : ∀ y, a < y → y ∈ Ω) (f : B.Assignment) (hf : B.CompatibleOn Ω f) :
    ∃ g : B.Assignment, B.CompatibleOn (insert a Ω) g ∧
      (∀ x ∈ Ω, g x = f x) := by
  classical
  have hu : IsUpperSet (Set.Ioi a) := fun x y hxy hx => lt_of_lt_of_le hx hxy
  obtain ⟨t, ht, htf⟩ := hb (Set.Ioi a) hu f
    (B.compatible_mono hf (fun y hy => hmax y hy))
  let g : B.Assignment := Function.update f a (t a)
  have hga : g a = t a := by simp [g]
  have hgf (x : V) (hx : x ≠ a) : g x = f x := by simp [g, hx]
  refine ⟨g, ?_, ?_⟩
  · intro e hs htt
    by_cases hlive : e ∈ live
    · by_cases hsa : G.source e = a
      · have hta : G.target e ≠ a := by simpa [hsa] using (G.increasing e).ne'
        have hT : G.target e ∈ Ω := hmax _ (hsa ▸ G.increasing e)
        have hsource : g (G.source e) = t (G.source e) := by subst a; exact hga
        rw [hsource, hgf _ hta, ← htf _ (hsa ▸ G.increasing e)]
        exact ht e (Set.mem_univ _) (Set.mem_univ _)
      · have hS : G.source e ∈ Ω := (Set.mem_insert_iff.mp hs).resolve_left hsa
        have hT : G.target e ∈ Ω := hΩ e hlive hS
        have hta : G.target e ≠ a := fun h => ha (h ▸ hT)
        rw [hgf _ hsa, hgf _ hta]
        exact hf e hS hT
    · let := hdead e hlive
      exact Subsingleton.elim _ _
  · intro x hx
    exact hgf x (fun h => ha (h ▸ hx))

theorem closedUnder_insert (live : Set E) (Ω : Set V)
    (hΩ : B.ClosedUnder live Ω) (a : V) (hmax : ∀ y, a < y → y ∈ Ω) :
    B.ClosedUnder live (insert a Ω) := by
  intro e he hs
  rcases Set.mem_insert_iff.mp hs with hs | hs
  · exact Set.mem_insert_of_mem _ (hmax _ (hs ▸ G.increasing e))
  · exact Set.mem_insert_of_mem _ (hΩ e he hs)

/-- A finite flabby graph sheaf extends from every set closed under its
nonzero edges. This is the source's relative-flabbiness argument in full,
not merely a restatement of flabbiness for ambient upper sets. -/
theorem extend_closedUnder [Finite V] (hb : B.Flabby) (live : Set E)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (Ω : Set V) (hΩ : B.ClosedUnder live Ω) (f : B.Assignment)
    (hf : B.CompatibleOn Ω f) :
    ∃ g : B.Assignment, B.IsGlobal g ∧ (∀ x ∈ Ω, g x = f x) := by
  classical
  let := Fintype.ofFinite V
  suffices h : ∀ s : Finset V, ∀ f : B.Assignment,
      B.ClosedUnder live (s : Set V)ᶜ → B.CompatibleOn (s : Set V)ᶜ f →
      ∃ g : B.Assignment, B.IsGlobal g ∧ ∀ x ∈ (s : Set V)ᶜ, g x = f x by
    have hs : ((Finset.univ.filter (fun x => x ∉ Ω) : Finset V) : Set V)ᶜ = Ω := by
      ext x
      simp
    have H := h (Finset.univ.filter (fun x => x ∉ Ω)) f
    rw [hs] at H
    exact H hΩ hf
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih f hΩ hf
  by_cases hs : s = ∅
  · subst s
    exact ⟨f, by simpa [IsGlobal] using hf, fun _ _ => rfl⟩
  obtain ⟨a, ha, hmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
  have ha' : a ∉ (s : Set V)ᶜ := by simpa using ha
  have hmax' (y : V) (hay : a < y) : y ∈ (s : Set V)ᶜ := by
    intro hy
    exact (not_le_of_gt hay) (hmax hy hay.le)
  obtain ⟨g, hg, hgf⟩ := B.extend_one hb live hdead (s : Set V)ᶜ hΩ a ha' hmax' f hf
  have hnew : ((s.erase a : Finset V) : Set V)ᶜ = insert a (s : Set V)ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_erase,
      Set.mem_insert_iff, not_and_or, not_not]
  have hsmall : s.erase a ⊂ s := Finset.erase_ssubset ha
  obtain ⟨t, ht, htg⟩ := ih (s.erase a) hsmall g
    (by rw [hnew]; exact B.closedUnder_insert live (s : Set V)ᶜ hΩ a hmax')
      (by rw [hnew]; exact hg)
  refine ⟨t, ht, ?_⟩
  intro x hx
  exact (htg x (by rw [hnew]; exact Set.mem_insert_of_mem _ hx)).trans (hgf x hx)

end Sheaf
end KLInvariance.MomentGraph

end

section

namespace KLInvariance.MomentGraph.Sheaf

universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}
  {G : OrderedGraph V E} (B : Sheaf.{u,v,w,z} (R := R) G)

/-- The actual module of sections on a vertex set. Coordinates outside the
set are harmless and ignored by all restriction maps. -/
def sections (Ω : Set V) : Submodule R B.Assignment where
  carrier := {f | B.CompatibleOn Ω f}
  zero_mem' := by intro e hs ht; simp
  add_mem' := by
    intro f g hf hg e hs ht
    change B.lower e (f (G.source e) + g (G.source e)) =
      B.upper e (f (G.target e) + g (G.target e))
    rw [map_add, map_add, hf e hs ht, hg e hs ht]
  smul_mem' := by
    intro r f hf e hs ht
    change B.lower e (r • f (G.source e)) = B.upper e (r • f (G.target e))
    rw [map_smul, map_smul, hf e hs ht]

/-- Generation at a stalk by genuine global sections. -/
def Generated : Prop :=
  ∀ x (b : B.vertex x), ∃ f : B.Assignment, B.IsGlobal f ∧ f x = b

abbrev Outgoing (x : V) := {e : E // G.source e = x}

abbrev Boundary (x : V) := ∀ e : Outgoing (G := G) x, B.edge e.val

/-- The lower-end stalk map on all upward edges. -/
def stalkMap (x : V) : B.vertex x →ₗ[R] B.Boundary x where
  toFun b e := B.lower e.val (e.property.symm ▸ b)
  map_add' b c := by ext e; cases e with | mk e he => subst x; simp
  map_smul' r b := by ext e; cases e with | mk e he => subst x; simp

/-- Boundary values supplied by sections strictly above a vertex. -/
def boundaryMap (x : V) : B.sections (Set.Ioi x) →ₗ[R] B.Boundary x where
  toFun f e := B.upper e.val (f.val (G.target e.val))
  map_add' f g := by ext e; simp
  map_smul' r f := by ext e; simp

def boundaryImage (x : V) : Submodule R (B.Boundary x) :=
  LinearMap.range (B.boundaryMap x)

/-- The precise boundary-image identity in `loc:decomposition`.
Generation supplies one inclusion and flabbiness supplies the other. -/
theorem range_stalkMap_eq_boundaryImage
    (hf : B.Flabby) (hg : B.Generated) (x : V) :
    LinearMap.range (B.stalkMap x) = B.boundaryImage x := by
  apply le_antisymm
  · rintro v ⟨b, rfl⟩
    obtain ⟨f, hglob, hfx⟩ := hg x b
    refine ⟨⟨f, B.compatible_mono hglob (Set.subset_univ _)⟩, ?_⟩
    ext e
    change B.upper e.val (f (G.target e.val)) =
      B.lower e.val (e.property.symm ▸ b)
    have hc := hglob e.val (Set.mem_univ _) (Set.mem_univ _)
    rw [← hc]
    congr 1
    cases e with | mk e he => subst x; exact hfx
  · rintro v ⟨f, rfl⟩
    have hu : IsUpperSet (Set.Ioi x) := fun a b hab ha => lt_of_lt_of_le ha hab
    obtain ⟨g, hglob, hgf⟩ := hf (Set.Ioi x) hu f.val f.property
    refine ⟨g x, ?_⟩
    ext e
    change B.lower e.val (e.property.symm ▸ g x) =
      B.upper e.val (f.val (G.target e.val))
    have hc := hglob e.val (Set.mem_univ _) (Set.mem_univ _)
    have ht : G.target e.val ∈ Set.Ioi x := by
      change x < G.target e.val
      exact lt_of_eq_of_lt e.property.symm (G.increasing e.val)
    rw [← hgf _ ht, ← hc]
    congr 1
    cases e with | mk e he => subst x; rfl

/-- A sheaf satisfying the two standard section properties gives an actual
surjection of its stalk onto the boundary module. -/
def stalkCover (hf : B.Flabby) (hg : B.Generated) (x : V) :
    B.vertex x →ₗ[R] B.boundaryImage x :=
  (B.stalkMap x).codRestrict _ (fun b => by
    rw [← B.range_stalkMap_eq_boundaryImage hf hg x]
    exact ⟨b, rfl⟩)

theorem stalkCover_surjective (hf : B.Flabby) (hg : B.Generated) (x : V) :
    Function.Surjective (B.stalkCover hf hg x) := by
  intro v
  have hv : (v : B.Boundary x) ∈ LinearMap.range (B.stalkMap x) := by
    simpa only [B.range_stalkMap_eq_boundaryImage hf hg x] using v.property
  obtain ⟨b, hb⟩ := hv
  exact ⟨b, Subtype.ext hb⟩

end KLInvariance.MomentGraph.Sheaf


end

end OAI
