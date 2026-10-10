import OAI.RepresentationTheory.KazhdanLusztig.Sheaves
import OAI.RepresentationTheory.KazhdanLusztig.GradedModules
import OAI.RepresentationTheory.KazhdanLusztig.ReflectionSchedules

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/

section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

structure GradedSheaf where
  vertex : V → ModuleData.{uk,ua,um} 𝓐
  edge : E → ModuleData.{uk,ua,um} 𝓐
  lower : ∀ e, ModuleData.Hom (vertex (G.source e)) (edge e)
  upper : ∀ e, ModuleData.Hom (vertex (G.target e)) (edge e)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)

def forget : Sheaf (R := A) G where
  vertex := fun x => (B.vertex x).obj
  edge := fun e => (B.edge e).obj
  lower := fun e => (B.lower e).map
  upper := fun e => (B.upper e).map

/-- Extension for sets closed under actual edges. It implies the source's
ordinary flabbiness, and is convenient for the descending construction. -/
def EdgeFlabby : Prop :=
  ∀ Ω : Set V, B.forget.ClosedUnder Set.univ Ω →
    ∀ f : B.forget.Assignment, B.forget.CompatibleOn Ω f →
    ∃ g : B.forget.Assignment, B.forget.IsGlobal g ∧ ∀ x ∈ Ω, g x = f x

 theorem EdgeFlabby.flabby (h : B.EdgeFlabby) : B.forget.Flabby := by
  intro Ω hΩ f hf
  exact h Ω (fun e _ he => hΩ (G.increasing e).le he) f hf

variable [Fintype V] [Fintype E]

noncomputable def assignments : ModuleData.{uk,ua,um} 𝓐 := ModuleData.pi B.vertex

noncomputable def lowerGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.lower e).comp (ModuleData.projection B.vertex (G.source e))

noncomputable def upperGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.upper e).comp (ModuleData.projection B.vertex (G.target e))

omit [Fintype E] in
 theorem sections_homogeneous (Ω : Set V) :
    ∀ n f, f ∈ B.forget.sections Ω → component B.assignments.piece n f ∈ B.forget.sections Ω := by
  intro n f hf e hs ht
  change (B.lowerGlobal e).map (component B.assignments.piece n f) =
    (B.upperGlobal e).map (component B.assignments.piece n f)
  rw [← (B.lowerGlobal e).component n f, ← (B.upperGlobal e).component n f]
  exact congrArg (component (B.edge e).piece n) (hf e hs ht)

noncomputable def sections [IsNoetherianRing A] (Ω : Set V) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.sub B.assignments (B.forget.sections Ω) (B.sections_homogeneous Ω)

noncomputable def boundary (x : V) : ModuleData.{uk,ua,um} 𝓐 :=
by
  classical
  letI : Fintype (Sheaf.Outgoing (G := G) x) := inferInstanceAs (Fintype {e : E // G.source e = x})
  exact ModuleData.pi (fun e : Sheaf.Outgoing (G := G) x => B.edge e.val)

noncomputable def boundaryHom [IsNoetherianRing A] (x : V) :
    ModuleData.Hom (B.sections (Set.Ioi x)) (B.boundary x) where
  map := B.forget.boundaryMap x
  graded := by
    intro n f hf e _
    exact (B.upper e.val).graded n (f.val (G.target e.val)) (hf (G.target e.val) (Set.mem_univ _))

noncomputable def boundaryImage [IsNoetherianRing A] (x : V) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.range (B.boundaryHom x)

 theorem exists_boundaryCover [IsNoetherianRing A]
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐) (x : V) :
    Nonempty (ModuleData.MinimalCover (B.boundaryImage x)) :=
  ModuleData.exists_minimalCover hneg hscalar (B.boundaryImage x)

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E D : Type um} [PartialOrder V] (G : OrderedGraph V E)

/-- Adjoin a vertex below the old vertices, with specified outgoing edges.
Only the edge orientations, not the extra comparabilities, enter sections. -/
def bottomGraph (τ : D → V) : OrderedGraph (WithBot V) (E ⊕ D) where
  source := Sum.elim (fun e => (G.source e : WithBot V)) (fun _ => ⊥)
  target := Sum.elim (fun e => (G.target e : WithBot V)) (fun d => (τ d : WithBot V))
  increasing := by
    intro e
    cases e with
    | inl e => exact WithBot.coe_lt_coe.mpr (G.increasing e)
    | inr d => exact WithBot.bot_lt_coe (τ d)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)
  [Fintype V] [Fintype D] [IsNoetherianRing A]
  (τ : D → V) (α : D → A) (hα : ∀ d, α d ∈ 𝓐 1)

noncomputable def attachEdges (d : D) : ModuleData.{uk,ua,um} 𝓐 :=
  (B.vertex (τ d)).scalarQuotient (α d) 1 (hα d)

noncomputable def attachQuotient (d : D) :
    ModuleData.Hom (B.vertex (τ d)) (B.attachEdges τ α hα d) :=
  ModuleData.quotientMap _ _ (scalar_range_homogeneous 𝓐 (B.vertex (τ d)).piece 1 (α d) (hα d))

noncomputable def attachBoundary : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.pi (B.attachEdges τ α hα)

noncomputable def attachBoundaryMap :
    ModuleData.Hom (B.sections Set.univ) (B.attachBoundary τ α hα) where
  map := LinearMap.pi fun d => (B.attachQuotient τ α hα d).map.comp
    ((LinearMap.proj (τ d)).comp (B.forget.sections Set.univ).subtype)
  graded := by
    intro n f hf d _
    exact (B.attachQuotient τ α hα d).graded n _ (hf (τ d) (Set.mem_univ _))

noncomputable def attachImage : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.range (B.attachBoundaryMap τ α hα)

variable (C : ModuleData.MinimalCover (B.attachImage τ α hα))

noncomputable def attachStalkMap : ModuleData.Hom C.source (B.attachBoundary τ α hα) :=
  (ModuleData.subtype (B.attachBoundary τ α hα) _
    (range_homogeneous _ _ (B.attachBoundaryMap τ α hα).map 0
      (by simpa using (B.attachBoundaryMap τ α hα).graded))).comp C.hom

noncomputable def extendBottom : GradedSheaf (𝓐 := 𝓐) (bottomGraph G τ) where
  vertex := WithBot.recBotCoe C.source B.vertex
  edge := Sum.elim B.edge (B.attachEdges τ α hα)
  lower := by
    intro e
    cases e with
    | inl e => exact B.lower e
    | inr d =>
      exact (ModuleData.projection (B.attachEdges τ α hα) d).comp
        (B.attachStalkMap τ α hα C)
  upper := by
    intro e
    cases e with
    | inl e => exact B.upper e
    | inr d => exact B.attachQuotient τ α hα d

 def attachAssignment (z : C.source) (f : B.forget.Assignment) :
    (B.extendBottom τ α hα C).forget.Assignment := WithBot.recBotCoe z f

 theorem attachAssignment_global (z : C.source) (f : B.forget.Assignment)
    (hf : B.forget.IsGlobal f)
    (hz : ∀ d, (B.attachStalkMap τ α hα C).map z d =
      (B.attachQuotient τ α hα d).map (f (τ d))) :
    (B.extendBottom τ α hα C).forget.IsGlobal (B.attachAssignment τ α hα C z f) := by
  intro e _ _
  cases e with
  | inl e => exact hf e (Set.mem_univ _) (Set.mem_univ _)
  | inr d => exact hz d

 theorem lift_global (f : B.forget.Assignment) (hf : B.forget.IsGlobal f) :
    ∃ z : C.source, (B.extendBottom τ α hα C).forget.IsGlobal
      (B.attachAssignment τ α hα C z f) := by
  let s : B.sections Set.univ := ⟨f,hf⟩
  let v : B.attachImage τ α hα :=
    ⟨(B.attachBoundaryMap τ α hα).map s, ⟨s,rfl⟩⟩
  obtain ⟨z,hz⟩ := C.surjective v
  refine ⟨z,B.attachAssignment_global τ α hα C z f hf ?_⟩
  intro d
  exact congrArg (fun t : B.attachImage τ α hα => t.val d) hz

 theorem extendBottom_generated (hg : B.forget.Generated) :
    (B.extendBottom τ α hα C).forget.Generated := by
  intro x
  induction x using WithBot.recBotCoe with
  | bot =>
    intro z
    obtain ⟨s,hs⟩ := (C.hom.map z).property
    refine ⟨B.attachAssignment τ α hα C z s.val,
      B.attachAssignment_global τ α hα C z s.val s.property ?_,rfl⟩
    intro d
    exact congrFun hs d |>.symm
  | coe x =>
    intro v
    obtain ⟨f,hf,hfx⟩ := hg x v
    obtain ⟨z,hz⟩ := B.lift_global τ α hα C f hf
    exact ⟨B.attachAssignment τ α hα C z f,hz,hfx⟩

 theorem extendBottom_edgeFlabby (hf : B.EdgeFlabby) :
    (B.extendBottom τ α hα C).EdgeFlabby := by
  intro Ω hΩ f hcompat
  let Ω' : Set V := {x | (x : WithBot V) ∈ Ω}
  let f' : B.forget.Assignment := fun x => f (x : WithBot V)
  have hc : B.forget.ClosedUnder Set.univ Ω' := by
    intro e _ hs
    exact hΩ (Sum.inl e) (Set.mem_univ _) hs
  have hcf : B.forget.CompatibleOn Ω' f' := by
    intro e hs ht
    exact hcompat (Sum.inl e) hs ht
  obtain ⟨g,hg,hgf⟩ := hf Ω' hc f' hcf
  classical
  by_cases hb : (⊥ : WithBot V) ∈ Ω
  · refine ⟨B.attachAssignment τ α hα C (f ⊥) g,
      B.attachAssignment_global τ α hα C (f ⊥) g hg ?_,?_⟩
    · intro d
      have hd : (τ d : WithBot V) ∈ Ω := hΩ (Sum.inr d) (Set.mem_univ _) hb
      rw [hgf (τ d) hd]
      exact hcompat (Sum.inr d) hb hd
    · intro x hx
      induction x using WithBot.recBotCoe with
      | bot => rfl
      | coe x => exact hgf x hx
  · obtain ⟨z,hz⟩ := B.lift_global τ α hα C g hg
    refine ⟨B.attachAssignment τ α hα C z g,hz,?_⟩
    intro x hx
    induction x using WithBot.recBotCoe with
    | bot => exact (hb hx).elim
    | coe x => exact hgf x hx

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

def Hom.ofEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M = N) : Hom M N := h ▸ Hom.id M

@[simp] theorem Hom.ofEq_rfl (M : ModuleData.{uk,ua,um} 𝓐) : Hom.ofEq (rfl : M=M) = Hom.id M := rfl

theorem Hom.ofEq_apply {ι : Type*} (M : ι → ModuleData.{uk,ua,um} 𝓐)
    {x y : ι} (h : x = y) (v : ∀ z, M z) :
    (Hom.ofEq (congrArg M h)).map (v x) = v y := by subst y; rfl

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

/-- An isomorphism of directed graphs, with no order-reflection requirement. -/
structure GraphEquiv (G : OrderedGraph V E) (H : OrderedGraph W F) where
  vertex : V ≃ W
  edge : E ≃ F
  source : ∀ e, vertex (G.source e) = H.source (edge e)
  target : ∀ e, vertex (G.target e) = H.target (edge e)

namespace GradedSheaf
variable (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)

def reindex : GradedSheaf (𝓐 := 𝓐) G where
  vertex := fun x => B.vertex (e.vertex x)
  edge := fun a => B.edge (e.edge a)
  lower := fun a => (B.lower (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.source a)))
  upper := fun a => (B.upper (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.target a)))

def reindexAssignment (f : B.forget.Assignment) : (B.reindex e).forget.Assignment :=
  fun x => f (e.vertex x)

@[simp] theorem reindex_lower (a : E) (f : B.forget.Assignment) :
    (B.reindex e).forget.lower a (B.reindexAssignment e f (G.source a)) =
      B.forget.lower (e.edge a) (f (H.source (e.edge a))) := by
  change (B.lower (e.edge a)).map ((ModuleData.Hom.ofEq (congrArg B.vertex (e.source a))).map
    (f (e.vertex (G.source a)))) = _
  exact congrArg (B.lower (e.edge a)).map
    (ModuleData.Hom.ofEq_apply B.vertex (e.source a) f)

@[simp] theorem reindex_upper (a : E) (f : B.forget.Assignment) :
    (B.reindex e).forget.upper a (B.reindexAssignment e f (G.target a)) =
      B.forget.upper (e.edge a) (f (H.target (e.edge a))) := by
  change (B.upper (e.edge a)).map ((ModuleData.Hom.ofEq (congrArg B.vertex (e.target a))).map
    (f (e.vertex (G.target a)))) = _
  exact congrArg (B.upper (e.edge a)).map
    (ModuleData.Hom.ofEq_apply B.vertex (e.target a) f)

def unreindexAssignment (f : (B.reindex e).forget.Assignment) : B.forget.Assignment :=
  fun y => (ModuleData.Hom.ofEq (congrArg B.vertex (e.vertex.apply_symm_apply y))).map
    (f (e.vertex.symm y))

@[simp] theorem unreindex_reindexAssignment (f : B.forget.Assignment) :
    B.unreindexAssignment e (B.reindexAssignment e f) = f := by
  funext y
  exact ModuleData.Hom.ofEq_apply B.vertex (e.vertex.apply_symm_apply y) f

@[simp] theorem reindex_unreindexAssignment (f : (B.reindex e).forget.Assignment) :
    B.reindexAssignment e (B.unreindexAssignment e f) = f := by
  funext x
  change (ModuleData.Hom.ofEq (congrArg B.vertex (e.vertex.apply_symm_apply (e.vertex x)))).map
    (f (e.vertex.symm (e.vertex x))) = f x
  have h : e.vertex.symm (e.vertex x) = x := e.vertex.symm_apply_apply x
  have hh : (ModuleData.Hom.ofEq
      (congrArg (fun t => B.vertex (e.vertex t)) h)).map
      (f (e.vertex.symm (e.vertex x))) = f x :=
    ModuleData.Hom.ofEq_apply (fun t => B.vertex (e.vertex t)) h f
  exact hh

 theorem reindex_global (f : B.forget.Assignment) (hf : B.forget.IsGlobal f) :
    (B.reindex e).forget.IsGlobal (B.reindexAssignment e f) := by
  intro a _ _
  rw [B.reindex_lower, B.reindex_upper]
  exact hf (e.edge a) (Set.mem_univ _) (Set.mem_univ _)

 theorem reindex_generated (hg : B.forget.Generated) : (B.reindex e).forget.Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hg (e.vertex x) v
  exact ⟨B.reindexAssignment e f,B.reindex_global e f hf,hfx⟩

 theorem reindex_edgeFlabby (hb : B.EdgeFlabby) : (B.reindex e).EdgeFlabby := by
  intro Ω hΩ f hf
  let Ω' := e.vertex '' Ω
  have hc : B.forget.ClosedUnder Set.univ Ω' := by
    intro a _ hs
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    obtain ⟨x,hx,hxs⟩ := hs
    have hx' : x = G.source a := e.vertex.injective (hxs.trans (e.source a).symm)
    exact ⟨G.target a,hΩ a (Set.mem_univ _) (hx' ▸ hx),e.target a⟩
  have hcf : B.forget.CompatibleOn Ω' (B.unreindexAssignment e f) := by
    intro a hs ht
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    have hh (x : V) (h : e.vertex x ∈ Ω') : x ∈ Ω := by
      obtain ⟨y,hy,hyx⟩ := h
      exact (e.vertex.injective hyx) ▸ hy
    have hfa := hf a (hh _ ((e.source a).symm ▸ hs)) (hh _ ((e.target a).symm ▸ ht))
    rw [← B.reindex_unreindexAssignment e f] at hfa
    exact (B.reindex_lower e a (B.unreindexAssignment e f)).symm.trans
      (hfa.trans (B.reindex_upper e a (B.unreindexAssignment e f)))
  obtain ⟨g,hg,hgf⟩ := hb Ω' hc (B.unreindexAssignment e f) hcf
  refine ⟨B.reindexAssignment e g,B.reindex_global e g hg,?_⟩
  intro x hx
  have hh := hgf (e.vertex x) ⟨x,hx,rfl⟩
  change g (e.vertex x) = f x
  rw [hh]
  exact congrFun (B.reindex_unreindexAssignment e f) x

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

theorem Hom.ofEq_bijective {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) :
    Function.Bijective (Hom.ofEq h).map := by subst N; exact Function.bijective_id

noncomputable def unit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) : ModuleData.{uk,ua,um} 𝓐 :=
  free (ι := PUnit.{max ua um + 1}) hneg (fun _ => 0) (fun _ => le_rfl)

instance unit_free [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) : Module.Free A (unit.{uk,ua,um} hneg) :=
  inferInstanceAs (Module.Free A (PUnit.{max ua um + 1} → A))

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

 def FreeStalks (B : GradedSheaf (𝓐 := 𝓐) G) : Prop := ∀ x, Module.Free A (B.vertex x)

/-- The genuine upper-end quotient rule, expressed without choosing a quotient
presentation of the edge object. -/
 def UpperQuotient (B : GradedSheaf (𝓐 := 𝓐) G) (α : E → A) : Prop :=
  ∀ e, Function.Surjective (B.upper e).map ∧
    ∀ v, (B.upper e).map v = 0 ↔ ∃ w, v = α e • w

/-- Minimality of the full outgoing boundary cover. The assignment formulation
avoids dependent casts and is equivalent to the usual kernel containment. -/
 def KernelMinimal (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) : Prop :=
  ∀ f : B.forget.Assignment,
    (∀ e, G.source e = x → B.forget.lower e (f (G.source e)) = 0) →
    f x ∈ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x))

 theorem kernelMinimal_iff (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    B.KernelMinimal x ↔ LinearMap.ker (B.forget.stalkMap x) ≤
      positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
  classical
  constructor
  · intro h v hv
    let f : B.forget.Assignment := Function.update 0 x v
    have hf : f x = v := by simp [f]
    rw [← hf]
    apply h f
    intro e he
    have hh := congrFun (LinearMap.mem_ker.mp hv) (⟨e,he⟩ : Sheaf.Outgoing x)
    subst x
    simpa [Sheaf.stalkMap,f] using hh
  · intro h f hf
    apply h
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact hf e rfl

 theorem reindex_freeStalks (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (h : B.FreeStalks) : (B.reindex e).FreeStalks := fun x => h (e.vertex x)

 theorem reindex_upperQuotient (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    {α : F → A} (h : B.UpperQuotient α) : (B.reindex e).UpperQuotient (α ∘ e.edge) := by
  intro a
  let j := ModuleData.Hom.ofEq (congrArg B.vertex (e.target a))
  have hj := ModuleData.Hom.ofEq_bijective (congrArg B.vertex (e.target a))
  refine ⟨(h (e.edge a)).1.comp hj.2,?_⟩
  intro v
  change (B.upper (e.edge a)).map (j.map v) = 0 ↔ ∃ w, v = α (e.edge a) • w
  rw [(h (e.edge a)).2]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨z,rfl⟩ := hj.2 w
    exact ⟨z,hj.1 (hw.trans (map_smul j.map (α (e.edge a)) z).symm)⟩
  · rintro ⟨w,rfl⟩
    exact ⟨j.map w,map_smul _ _ _⟩

 theorem reindex_kernelMinimal (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (x : V) (h : B.KernelMinimal (e.vertex x)) : (B.reindex e).KernelMinimal x := by
  intro f hf
  have hh : ∀ a, H.source a = e.vertex x →
      B.forget.lower a (B.unreindexAssignment e f (H.source a)) = 0 := by
    intro a ha
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    have hs : G.source a = x := e.vertex.injective ((e.source a).trans ha)
    have hv := hf a hs
    rw [← B.reindex_unreindexAssignment e f] at hv
    exact (B.reindex_lower e a (B.unreindexAssignment e f)).symm.trans hv
  have hm := h (B.unreindexAssignment e f) hh
  have he := congrFun (B.reindex_unreindexAssignment e f) x
  exact he ▸ hm

variable {D : Type um} [Fintype V] [Fintype D] [IsNoetherianRing A]
  (B : GradedSheaf (𝓐 := 𝓐) G) (τ : D → V) (α : D → A)
  (hα : ∀ d, α d ∈ 𝓐 1) (C : ModuleData.MinimalCover (B.attachImage τ α hα))

 theorem extendBottom_freeStalks (hb : B.FreeStalks) :
    (B.extendBottom τ α hα C).FreeStalks := by
  intro x
  induction x using WithBot.recBotCoe with
  | bot => exact C.free
  | coe x => exact hb x

 theorem extendBottom_upperQuotient {αold : E → A} (hb : B.UpperQuotient αold) :
    (B.extendBottom τ α hα C).UpperQuotient (Sum.elim αold α) := by
  intro e
  cases e with
  | inl e => exact hb e
  | inr d =>
    let S := LinearMap.range (LinearMap.lsmul A (B.vertex (τ d)) (α d))
    refine ⟨S.mkQ_surjective,?_⟩
    intro v
    change S.mkQ v = 0 ↔ ∃ w, v = α d • w
    refine (Submodule.Quotient.mk_eq_zero S).trans ?_
    change (∃ w, α d • w = v) ↔ ∃ w, v = α d • w
    exact ⟨fun ⟨w,hw⟩ => ⟨w,hw.symm⟩,fun ⟨w,hw⟩ => ⟨w,hw.symm⟩⟩

 theorem extendBottom_kernelMinimal_bot : (B.extendBottom τ α hα C).KernelMinimal ⊥ := by
  intro f hf
  apply C.minimal
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  funext d
  exact hf (Sum.inr d) rfl

 theorem extendBottom_kernelMinimal_coe (x : V) (h : B.KernelMinimal x) :
    (B.extendBottom τ α hα C).KernelMinimal (x : WithBot V) := by
  intro f hf
  apply h (fun y => f (y : WithBot V))
  intro a ha
  exact hf (Sum.inl a) (congrArg (fun y : V => (y : WithBot V)) ha)

end KLInvariance.MomentGraph.GradedSheaf

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

structure Iso (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) where
  vertex : ∀ x, B.vertex x ≃ₗ[R] C.vertex x
  edge : ∀ e, B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e v, edge e (B.lower e v) = C.lower e (vertex (G.source e) v)
  upper : ∀ e v, edge e (B.upper e v) = C.upper e (vertex (G.target e) v)

namespace Iso
variable {B : Sheaf.{u,v,w,z} (R := R) G} {C : Sheaf.{u,v,w,z'} (R := R) G}
  (j : Iso B C)

def symm : Iso C B where
  vertex x := (j.vertex x).symm
  edge e := (j.edge e).symm
  lower e v := by
    apply (j.edge e).injective
    simp only [LinearEquiv.apply_symm_apply, j.lower]
  upper e v := by
    apply (j.edge e).injective
    simp only [LinearEquiv.apply_symm_apply, j.upper]

noncomputable def assignments : B.Assignment ≃ₗ[R] C.Assignment :=
  LinearEquiv.piCongrRight j.vertex

theorem compatible_iff (Ω : Set V) (f : B.Assignment) :
    C.CompatibleOn Ω (j.assignments f) ↔ B.CompatibleOn Ω f := by
  constructor <;> intro h e hs ht
  · apply (j.edge e).injective
    rw [j.lower,j.upper]
    exact h e hs ht
  · change C.lower e (j.vertex _ (f _)) = C.upper e (j.vertex _ (f _))
    rw [← j.lower,← j.upper,h e hs ht]

theorem map_sections (Ω : Set V) :
    (B.sections Ω).map j.assignments.toLinearMap = C.sections Ω := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact (j.compatible_iff Ω f).mpr hf
  · intro hg
    refine ⟨j.assignments.symm g,?_,j.assignments.apply_symm_apply g⟩
    apply (j.compatible_iff Ω _).mp
    change C.CompatibleOn Ω g at hg
    simpa using hg

noncomputable def sections (Ω : Set V) : B.sections Ω ≃ₗ[R] C.sections Ω :=
  j.assignments.ofSubmodules _ _ (j.map_sections Ω)

noncomputable def boundary (x : V) : B.Boundary x ≃ₗ[R] C.Boundary x :=
  LinearEquiv.piCongrRight (fun e => j.edge e.val)

theorem stalkMap (x : V) (v : B.vertex x) :
    j.boundary x (B.stalkMap x v) = C.stalkMap x (j.vertex x v) := by
  funext e
  rcases e with ⟨e,he⟩
  subst x
  exact j.lower e v

theorem boundaryMap (x : V) (f : B.sections (Set.Ioi x)) :
    j.boundary x (B.boundaryMap x f) = C.boundaryMap x (j.sections _ f) := by
  funext e
  exact j.upper e.val (f.val (G.target e.val))

theorem map_boundaryRange (x : V) :
    (LinearMap.range (B.boundaryMap x)).map (j.boundary x).toLinearMap =
      LinearMap.range (C.boundaryMap x) := by
  ext v
  constructor
  · rintro ⟨w,⟨f,rfl⟩,rfl⟩
    exact ⟨j.sections _ f,(j.boundaryMap x f).symm⟩
  · rintro ⟨f,rfl⟩
    refine ⟨B.boundaryMap x ((j.sections _).symm f),⟨_,rfl⟩,?_⟩
    change j.boundary x (B.boundaryMap x ((j.sections _).symm f)) = _
    rw [j.boundaryMap,LinearEquiv.apply_symm_apply]

end Iso

variable (B : Sheaf.{u,v,w,z} (R := R) G)

def upwardKernel (x : V) (F : Set (Outgoing (G := G) x)) : Submodule R (B.vertex x) where
  carrier := {v | ∀ e ∈ F, B.stalkMap x v e = 0}
  zero_mem' := by intro e _; simp
  add_mem' := by intro v w hv hw e he; simp [hv e he,hw e he]
  smul_mem' := by intro r v hv e he; simp [hv e he]

namespace Iso
variable {B : Sheaf.{u,v,w,z} (R := R) G} {C : Sheaf.{u,v,w,z'} (R := R) G}
  (j : Iso B C)

theorem upwardKernel_iff (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    j.vertex x v ∈ C.upwardKernel x F ↔ v ∈ B.upwardKernel x F := by
  constructor <;> intro h e he
  · apply (j.edge e.val).injective
    rw [map_zero]
    exact (congrFun (j.stalkMap x v) e).trans (h e he)
  · have hh := congrFun (j.stalkMap x v) e
    change j.edge e.val (B.stalkMap x v e) = _ at hh
    rw [h e he,map_zero] at hh
    exact hh.symm

theorem map_upwardKernel (x : V) (F : Set (Outgoing (G := G) x)) :
    (B.upwardKernel x F).map (j.vertex x).toLinearMap = C.upwardKernel x F := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (j.upwardKernel_iff x F w).mpr hw
  · intro hv
    refine ⟨(j.vertex x).symm v,?_,(j.vertex x).apply_symm_apply v⟩
    apply (j.upwardKernel_iff x F _).mp
    simpa using hv

theorem map_lowerImage (e : E) (F : Set (Outgoing (G := G) (G.source e))) :
    ((B.upwardKernel (G.source e) F).map (B.lower e)).map (j.edge e).toLinearMap =
      (C.upwardKernel (G.source e) F).map (C.lower e) := by
  rw [← Submodule.map_comp]
  have h : (j.edge e).toLinearMap.comp (B.lower e) =
      (C.lower e).comp (j.vertex (G.source e)).toLinearMap := LinearMap.ext (j.lower e)
  rw [h,Submodule.map_comp,j.map_upwardKernel]

theorem map_upperImage (e : E) (F : Set (Outgoing (G := G) (G.target e))) :
    ((B.upwardKernel (G.target e) F).map (B.upper e)).map (j.edge e).toLinearMap =
      (C.upwardKernel (G.target e) F).map (C.upper e) := by
  rw [← Submodule.map_comp]
  have h : (j.edge e).toLinearMap.comp (B.upper e) =
      (C.upper e).comp (j.vertex (G.target e)).toLinearMap := LinearMap.ext (j.upper e)
  rw [h,Submodule.map_comp,j.map_upwardKernel]

end Iso
end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.EmbeddedModule
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def scaled (r : R) (K : Submodule R M) : Submodule R M :=
  K.map (LinearMap.lsmul R M r)

theorem map_scaled (j : M ≃ₗ[R] N) (r : R) (K : Submodule R M) :
    (scaled r K).map j.toLinearMap = scaled r (K.map j.toLinearMap) := by
  simp only [scaled,← Submodule.map_comp]
  congr 1
  ext v
  exact j.map_smul r v

/-- Scalar comparison is transported by one and the same edge isomorphism. -/
theorem map_eq_scaled_iff (j : M ≃ₗ[R] N) (r : R) (I J : Submodule R M) :
    I.map j.toLinearMap = scaled r (J.map j.toLinearMap) ↔ I = scaled r J := by
  rw [← map_scaled]
  constructor
  · intro h
    have h' := congrArg (Submodule.map j.symm.toLinearMap) h
    simpa only [← Submodule.map_comp,LinearEquiv.symm_comp,
      Submodule.map_id] using h'
  · exact congrArg (Submodule.map j.toLinearMap)

end KLInvariance.EmbeddedModule

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) (x : V)

/-- An isomorphism already constructed strictly above `x`, including the edge
modules whose upper endpoints are above `x`. The latter are canonically supplied
by the upper quotient rule in the local decomposition. -/
structure AboveIso where
  vertex : ∀ y, x < y → B.vertex y ≃ₗ[R] C.vertex y
  edge : ∀ e, x < G.target e → B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e (h : x < G.source e) v,
    edge e (h.trans (G.increasing e)) (B.lower e v) =
      C.lower e (vertex (G.source e) h v)
  upper : ∀ e (h : x < G.target e) v,
    edge e h (B.upper e v) = C.upper e (vertex (G.target e) h v)

namespace AboveIso
variable {B C x} (j : AboveIso B C x)

def symm : AboveIso C B x where
  vertex y h := (j.vertex y h).symm
  edge e h := (j.edge e h).symm
  lower e h v := by
    apply (j.edge e (h.trans (G.increasing e))).injective
    rw [LinearEquiv.apply_symm_apply,j.lower e h,LinearEquiv.apply_symm_apply]
  upper e h v := by
    apply (j.edge e h).injective
    simp only [LinearEquiv.apply_symm_apply,j.upper]

noncomputable def mapAssignment (f : B.Assignment) : C.Assignment :=
by
  classical
  exact fun y => if h : x < y then j.vertex y h (f y) else 0

lemma mapAssignment_at (f : B.Assignment) (y : V) (h : x < y) :
    j.mapAssignment f y = j.vertex y h (f y) := by
  classical
  simp [mapAssignment,h]

lemma compatible (f : B.Assignment) (hf : B.CompatibleOn (Set.Ioi x) f) :
    C.CompatibleOn (Set.Ioi x) (j.mapAssignment f) := by
  intro e hs ht
  change x < G.source e at hs
  change x < G.target e at ht
  rw [j.mapAssignment_at f _ hs,j.mapAssignment_at f _ ht,← j.lower e hs,← j.upper e ht]
  exact congrArg (j.edge e ht) (hf e hs ht)

noncomputable def boundary : B.Boundary x ≃ₗ[R] C.Boundary x :=
  LinearEquiv.piCongrRight (fun e => j.edge e.val (lt_of_eq_of_lt e.property.symm (G.increasing e.val)))

lemma boundaryMap (f : B.sections (Set.Ioi x)) :
    j.boundary (B.boundaryMap x f) =
      C.boundaryMap x ⟨j.mapAssignment f.val,j.compatible f.val f.property⟩ := by
  funext e
  change j.edge e.val _ (B.upper e.val (f.val (G.target e.val))) =
    C.upper e.val (j.mapAssignment f.val (G.target e.val))
  rw [j.mapAssignment_at _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val)),j.upper]

lemma map_boundaryImage : (B.boundaryImage x).map j.boundary.toLinearMap = C.boundaryImage x := by
  apply le_antisymm
  · rintro v ⟨w,⟨f,rfl⟩,rfl⟩
    exact ⟨⟨j.mapAssignment f.val,j.compatible f.val f.property⟩,(j.boundaryMap f).symm⟩
  · rintro v ⟨f,rfl⟩
    refine ⟨B.boundaryMap x ⟨j.symm.mapAssignment f.val,j.symm.compatible f.val f.property⟩,
      ⟨_,rfl⟩,?_⟩
    funext e
    change j.edge e.val _ (B.upper e.val (j.symm.mapAssignment f.val (G.target e.val))) =
      C.upper e.val (f.val (G.target e.val))
    rw [j.symm.mapAssignment_at _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val)),j.upper]
    exact congrArg (C.upper e.val) ((j.vertex _ _).apply_symm_apply _)

lemma map_stalk_image (hBf : B.Flabby) (hBg : B.Generated)
    (hCf : C.Flabby) (hCg : C.Generated) :
    (LinearMap.range (B.stalkMap x)).map j.boundary.toLinearMap =
      LinearMap.range (C.stalkMap x) := by
  rw [B.range_stalkMap_eq_boundaryImage hBf hBg,C.range_stalkMap_eq_boundaryImage hCf hCg]
  exact j.map_boundaryImage

/-- One genuine descending splitting: the finite-free new top summand is
proved from the local-ring minimum cover, and all outgoing restriction maps
commute with the selected edge isomorphisms. -/
theorem extend_stalk [IsLocalRing R]
    [Module.Free R (B.vertex x)] [Module.Finite R (B.vertex x)]
    [Module.Free R (C.vertex x)] [Module.Finite R (C.vertex x)]
    (hBf : B.Flabby) (hBg : B.Generated) (hCf : C.Flabby) (hCg : C.Generated)
    (hmin : LinearMap.ker (C.stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.vertex x))) :
    ∃ (g : B.vertex x →ₗ[R] C.vertex x)
      (jv : B.vertex x ≃ₗ[R] C.vertex x × LinearMap.ker g),
      Module.Free R (LinearMap.ker g) ∧ Module.Finite R (LinearMap.ker g) ∧
      ∀ (b : B.vertex x) (e : Outgoing (G := G) x),
        j.edge e.val (lt_of_eq_of_lt e.property.symm (G.increasing e.val)) (B.stalkMap x b e) =
          C.stalkMap x (jv b).1 e := by
  let N := LinearMap.range (C.stalkMap x)
  let π : C.vertex x →ₗ[R] N := (C.stalkMap x).rangeRestrict
  have him := j.map_stalk_image hBf hBg hCf hCg
  let φ : B.vertex x →ₗ[R] N := LinearMap.codRestrict N
    (j.boundary.toLinearMap.comp (B.stalkMap x)) (by
      intro b
      change j.boundary (B.stalkMap x b) ∈ LinearMap.range (C.stalkMap x)
      rw [← him]
      exact ⟨B.stalkMap x b,⟨b,rfl⟩,rfl⟩)
  have hφ : Function.Surjective φ := by
    intro n
    have hn : n.val ∈ (LinearMap.range (B.stalkMap x)).map j.boundary.toLinearMap := by
      rw [him]
      exact n.property
    rcases hn with ⟨w,⟨b,rfl⟩,hb⟩
    exact ⟨b,Subtype.ext hb⟩
  have hπmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.vertex x)) := by
    intro c hc
    apply hmin
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hc)
  obtain ⟨g,jv,_,hg,hfree,hfinite,hjv⟩ :=
    LocalCover.exists_split_minimal_cover π φ (by intro n; obtain ⟨c,hc⟩ := n.property; exact ⟨c,Subtype.ext hc⟩) hφ hπmin
  refine ⟨g,jv,hfree,hfinite,?_⟩
  intro b e
  have h := congrArg (fun n : N => n.val e) (hjv b).2
  exact h.symm

end AboveIso
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i}

/-- Finite direct sums represented by products, as used in the plane localization. -/
def pi (B : ι → Sheaf.{u,v,w,z} (R := R) G) : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (∀ i, (B i).vertex x)
  edge e := ModuleCat.of R (∀ i, (B i).edge e)
  lower e := LinearMap.pi (fun i => ((B i).lower e).comp (LinearMap.proj i))
  upper e := LinearMap.pi (fun i => ((B i).upper e).comp (LinearMap.proj i))

lemma pi_compatible (B : ι → Sheaf.{u,v,w,z} (R := R) G) (Ω : Set V)
    (f : (pi B).Assignment) :
    (pi B).CompatibleOn Ω f ↔ ∀ i, (B i).CompatibleOn Ω (fun x => f x i) := by
  constructor
  · intro h i e hs ht
    exact congrFun (h e hs ht) i
  · intro h e hs ht
    funext i
    exact h i e hs ht

lemma pi_generated (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Generated) : (pi B).Generated := by
  intro x v
  classical
  choose f hf hfx using fun i => h i x (v i)
  exact ⟨fun y i => f i y,(pi_compatible B Set.univ _).mpr hf,funext hfx⟩

lemma pi_flabby (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Flabby) : (pi B).Flabby := by
  intro Ω hΩ f hf
  classical
  choose g hg hgf using fun i => h i Ω hΩ (fun x => f x i) ((pi_compatible B Ω f).mp hf i)
  exact ⟨fun y i => g i y,(pi_compatible B Set.univ _).mpr hg,fun x hx => funext (fun i => hgf i x hx)⟩

lemma pi_kernel_iff (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V)
    (f : (pi B).vertex x) :
    f ∈ LinearMap.ker ((pi B).stalkMap x) ↔ ∀ i, f i ∈ LinearMap.ker ((B i).stalkMap x) := by
  constructor
  · intro h i
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact congrFun (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩) i
  · intro h
    apply LinearMap.mem_ker.mpr
    funext e i
    rcases e with ⟨e,he⟩
    subst x
    exact congrFun (LinearMap.mem_ker.mp (h i)) ⟨e,rfl⟩

end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.LocalCover
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
  (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Coordinatewise membership in the ideal multiple of a finite product. -/
lemma pi_mem_ideal_smul (I : Ideal R) (f : ∀ i, M i)
    (hf : ∀ i, f i ∈ I • (⊤ : Submodule R (M i))) :
    f ∈ I • (⊤ : Submodule R (∀ i, M i)) := by
  classical
  have hs (i : ι) : Pi.single i (f i) ∈ I • (⊤ : Submodule R (∀ i, M i)) := by
    have hmap : (I • (⊤ : Submodule R (M i))).map (LinearMap.single R M i) ≤
        I • (⊤ : Submodule R (∀ i, M i)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap ⟨f i,hf i,rfl⟩
  simpa only [Finset.univ_sum_single] using Submodule.sum_mem (I • (⊤ : Submodule R (∀ i, M i))) (t := Finset.univ) (fun i _ => hs i)

end KLInvariance.LocalCover

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i} [Fintype ι]

lemma pi_minimal (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (h : ∀ i, LinearMap.ker ((B i).stalkMap x) ≤ I • (⊤ : Submodule R ((B i).vertex x))) :
    LinearMap.ker ((pi B).stalkMap x) ≤ I • (⊤ : Submodule R ((pi B).vertex x)) := by
  intro f hf
  exact LocalCover.pi_mem_ideal_smul (fun i => (B i).vertex x) I f
    (fun i => h i ((pi_kernel_iff B x f).mp hf i))

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.QuotientEdge
variable {R M N E F : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- The edge isomorphism forced by an upper stalk isomorphism and exact quotient maps. -/
noncomputable def iso (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : M ≃ₗ[R] N) (hk : (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g) : E ≃ₗ[R] F :=
  (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.Quotient.equiv _ _ h hk).trans (g.quotKerEquivOfSurjective hg))

@[simp] lemma iso_apply (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : M ≃ₗ[R] N) (hk : (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g) (v : M) :
    iso f g hf hg h hk (f v) = g (h v) := by
  simp [iso,Submodule.Quotient.equiv]

lemma map_kernel_scalar (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v = r • w) (h : M ≃ₗ[R] N) :
    (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨u,rfl⟩ := (hf w).mp hw
    exact (hg _).mpr ⟨h u,h.map_smul r u⟩
  · intro hv
    obtain ⟨w,rfl⟩ := (hg v).mp hv
    refine ⟨r • h.symm w,(hf _).mpr ⟨h.symm w,rfl⟩,?_⟩
    simp

/-- No separate choice of edge data or scalar compatibility hypothesis is needed. -/
theorem exists_scalar_iso (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v = r • w) (h : M ≃ₗ[R] N) :
    ∃ j : E ≃ₗ[R] F, ∀ v, j (f v) = g (h v) :=
  ⟨iso f g hfs hgs h (map_kernel_scalar f g r hf hg h),iso_apply f g hfs hgs h _⟩

end KLInvariance.QuotientEdge

end


section

/-! Partial sheaf isomorphisms on upper sets, and their actual descending
extension. In particular the incoming edge component is induced by the upper
scalar quotient, not independently assumed. -/
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G)

 def UpperQuotient (α : E → R) : Prop :=
  ∀ e, Function.Surjective (B.upper e) ∧
    ∀ v, B.upper e v = 0 ↔ ∃ w, v = α e • w

def castStalkIso {x y : V} (h : x=y) (j : B.vertex x ≃ₗ[R] C.vertex x) :
    B.vertex y ≃ₗ[R] C.vertex y := h ▸ j

structure OnIso (U : Set V) where
  vertex : ∀ x, x ∈ U → B.vertex x ≃ₗ[R] C.vertex x
  edge : ∀ e, G.target e ∈ U → B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e (hs : G.source e ∈ U) (ht : G.target e ∈ U) v,
    edge e ht (B.lower e v) = C.lower e (vertex (G.source e) hs v)
  upper : ∀ e (ht : G.target e ∈ U) v,
    edge e ht (B.upper e v) = C.upper e (vertex (G.target e) ht v)

namespace OnIso
variable {B C} {U : Set V} (j : OnIso B C U)

 def above (x : V) (hx : Set.Ioi x ⊆ U) : AboveIso B C x where
  vertex y h := j.vertex y (hx h)
  edge e h := j.edge e (hx h)
  lower e h v := j.lower e (hx h) (hx (h.trans (G.increasing e))) v
  upper e h v := j.upper e (hx h) v

 def ofUniv (j : OnIso B C Set.univ) : Iso B C where
  vertex x := j.vertex x (Set.mem_univ x)
  edge e := j.edge e (Set.mem_univ _)
  lower e v := j.lower e (Set.mem_univ _) (Set.mem_univ _) v
  upper e v := j.upper e (Set.mem_univ _) v

/-- Given the new stalk and its outgoing commuting squares, all new incoming
edges are forced by the scalar quotient rule. -/
noncomputable def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → R)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : B.vertex x ≃ₗ[R] C.vertex x)
    (hout : ∀ e (he : G.source e = x) v,
      j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.lower e v) = C.lower e (castStalkIso B C he.symm jv v)) :
    OnIso B C (insert x U) := by
  classical
  let vj : ∀ y, y ∈ insert x U → B.vertex y ≃ₗ[R] C.vertex y := fun y hy =>
    if h : y = x then castStalkIso B C h.symm jv
    else j.vertex y ((Set.mem_insert_iff.mp hy).resolve_left h)
  have vj_old (y : V) (hy : y ∈ U) : vj y (Set.mem_insert_of_mem x hy) = j.vertex y hy := by
    simp only [vj,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]
  have vj_new : vj x (Set.mem_insert x U) = jv := by simp [vj,castStalkIso]
  let ej : ∀ e, G.target e ∈ insert x U → B.edge e ≃ₗ[R] C.edge e := fun e he =>
    if h : G.target e = x then
      QuotientEdge.iso (B.upper e) (C.upper e) (hBq e).1 (hCq e).1
        (vj (G.target e) he)
        (QuotientEdge.map_kernel_scalar (B.upper e) (C.upper e) (α e)
          (hBq e).2 (hCq e).2 (vj (G.target e) he))
    else j.edge e ((Set.mem_insert_iff.mp he).resolve_left h)
  have ej_old (e : E) (he : G.target e ∈ U) :
      ej e (Set.mem_insert_of_mem x he) = j.edge e he := by
    simp only [ej,dite_eq_right (show G.target e ≠ x from fun h => hx (h ▸ he))]
  refine ⟨vj,ej,?_,?_⟩
  · intro e hs ht v
    have htU : G.target e ∈ U := by
      rcases Set.mem_insert_iff.mp hs with hs | hs
      · exact hmax (lt_of_eq_of_lt hs.symm (G.increasing e))
      · exact hU (G.increasing e).le hs
    rw [ej_old e htU]
    by_cases he : G.source e = x
    · subst x
      rw [vj_new]
      exact hout e rfl v
    · have hsU : G.source e ∈ U := (Set.mem_insert_iff.mp hs).resolve_left he
      rw [vj_old _ hsU]
      exact j.lower e hsU htU v
  · intro e ht v
    by_cases he : G.target e = x
    · simp only [ej,dite_eq_left he]
      exact QuotientEdge.iso_apply _ _ _ _ _ _ v
    · have htU : G.target e ∈ U := (Set.mem_insert_iff.mp ht).resolve_left he
      rw [ej_old e htU,vj_old _ htU]
      exact j.upper e htU v

end OnIso
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph
universe um
variable {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

 def removeGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    OrderedGraph {y : V // y ≠ x} {e : E // G.source e ≠ x} where
  source e := ⟨G.source e.val,e.property⟩
  target e := ⟨G.target e.val,ht e.val⟩
  increasing e := G.increasing e.val

 def removeTarget (x : V) (ht : ∀ e, G.target e ≠ x) :
    {e : E // G.source e = x} → {y : V // y ≠ x} := fun e => ⟨G.target e.val,ht e.val⟩

noncomputable def splitVertex (x : V) : V ≃ WithBot {y : V // y ≠ x} := by
  classical
  exact
    { toFun := fun y => if h : y=x then ⊥ else (⟨y,h⟩ : {y : V // y ≠ x})
      invFun := WithBot.recBotCoe x Subtype.val
      left_inv := by intro y; by_cases h : y=x <;> simp [h]
      right_inv := by
        intro y
        induction y using WithBot.recBotCoe with
        | bot => simp
        | coe y => simp [y.property] }

noncomputable def splitEdge (x : V) : E ≃ {e : E // G.source e ≠ x} ⊕ {e : E // G.source e = x} := by
  classical
  exact
    { toFun := fun e => if h : G.source e=x then Sum.inr ⟨e,h⟩ else Sum.inl ⟨e,h⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := by intro e; by_cases h : G.source e=x <;> simp [h]
      right_inv := by
        intro e
        cases e with
        | inl e => simp [e.property]
        | inr e => simp [e.property] }

omit [PartialOrder V] in
@[simp] theorem splitVertex_self (x : V) : splitVertex x x = ⊥ := by
  classical
  simp [splitVertex]

omit [PartialOrder V] in
 theorem splitVertex_ne (x y : V) (hy : y ≠ x) :
    splitVertex x y = (⟨y,hy⟩ : {y : V // y ≠ x}) := by
  classical
  simp [splitVertex,hy]

noncomputable def splitGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    GraphEquiv G (bottomGraph (removeGraph G x ht) (removeTarget G x ht)) where
  vertex := splitVertex x
  edge := splitEdge G x
  source := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,bottomGraph]
    · simp [splitEdge,splitVertex,h,bottomGraph,removeGraph]
  target := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeTarget]
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeGraph]

 theorem splitEdge_labels {A : Type*} (α : E → A) (x : V) :
    (Sum.elim (fun e : {e : E // G.source e ≠ x} => α e.val)
      (fun e : {e : E // G.source e = x} => α e.val)) ∘ (splitEdge G x) = α := by
  classical
  funext e
  by_cases h : G.source e=x <;> simp [splitEdge,h]

end KLInvariance.MomentGraph

end


section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

/-- The outcome of the actual minimal boundary construction. Full upward-kernel
freeness, integral duality and KL characters are NOT part of this structure. -/
structure BoundarySheaf {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)
    (α : E → A) (b : V) where
  sheaf : GradedSheaf (𝓐 := 𝓐) G
  free : sheaf.FreeStalks
  quotient : sheaf.UpperQuotient α
  flabby : sheaf.EdgeFlabby
  generated : sheaf.forget.Generated
  top : sheaf.vertex b = ModuleData.unit hneg
  minimal : ∀ x, x ≠ b → sheaf.KernelMinimal x

variable {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

noncomputable def singletonSheaf [IsEmpty E] : GradedSheaf (𝓐 := 𝓐) G where
  vertex := fun _ => ModuleData.unit hneg
  edge := isEmptyElim
  lower := isEmptyElim
  upper := isEmptyElim

 theorem singleton_boundarySheaf (b : V) (hV : ∀ x, x=b) (α : E → A) :
    Nonempty (BoundarySheaf hneg G α b) := by
  have hempty : IsEmpty E := ⟨fun e => (G.increasing e).ne ((hV _).trans (hV _).symm)⟩
  let := hempty
  let B := singletonSheaf hneg G
  refine ⟨⟨B,?_,?_,?_,?_,rfl,?_⟩⟩
  · intro x
    exact ModuleData.unit_free hneg
  · intro e
    exact isEmptyElim e
  · intro Ω _ f _
    exact ⟨f,fun e => isEmptyElim e,fun _ _ => rfl⟩
  · intro x v
    exact ⟨fun _ => v,fun e => isEmptyElim e,rfl⟩
  · intro x hx
    exact (hx (hV x)).elim

variable [IsNoetherianRing A]
  (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)

include hscalar in
 theorem exists_boundarySheaf_card (n : ℕ)
    [Fintype V] [Fintype E] (b : V) (hb : ∀ x, x ≤ b)
    (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1) (hn : Fintype.card V = n) :
    Nonempty (BoundarySheaf hneg G α b) := by
  classical
  induction n using Nat.strong_induction_on generalizing V E with
  | h n ih =>
    by_cases hV : ∀ x : V, x=b
    · exact singleton_boundarySheaf hneg G b hV α
    obtain ⟨y,hy⟩ := not_forall.mp hV
    obtain ⟨x,hx⟩ := exists_minimal_of_wellFoundedLT (fun _ : V => True) ⟨b,trivial⟩
    have hxb : x ≠ b := by
      intro he
      have hlt : y < x := he ▸ lt_of_le_of_ne (hb y) hy
      exact hx.not_lt trivial hlt
    have ht (e : E) : G.target e ≠ x := by
      intro he
      exact hx.not_lt trivial (he ▸ G.increasing e)
    let V' := {y : V // y ≠ x}
    let E' := {e : E // G.source e ≠ x}
    let D := {e : E // G.source e = x}
    let G' := removeGraph G x ht
    let τ := removeTarget G x ht
    let b' : V' := ⟨b,hxb.symm⟩
    let α' : E' → A := fun e => α e.val
    let β : D → A := fun e => α e.val
    have hβ : ∀ e : D, β e ∈ 𝓐 1 := fun e => hα e.val
    have hcard : Fintype.card V' < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := x) (not_not.mpr rfl)
    obtain ⟨B⟩ := ih (Fintype.card V') hcard G' b' (fun y => hb y.val)
      α' (fun e => hα e.val) rfl
    obtain ⟨C⟩ := ModuleData.exists_minimalCover hneg hscalar (B.sheaf.attachImage τ β hβ)
    let H := B.sheaf.extendBottom τ β hβ C
    let e := splitGraph G x ht
    refine ⟨⟨H.reindex e,?_,?_,?_,?_,?_,?_⟩⟩
    · exact H.reindex_freeStalks e (B.sheaf.extendBottom_freeStalks τ β hβ C B.free)
    · have hh := H.reindex_upperQuotient e
        (B.sheaf.extendBottom_upperQuotient τ β hβ C B.quotient)
      have he : (Sum.elim α' β) ∘ e.edge = α := splitEdge_labels G α x
      exact he ▸ hh
    · exact H.reindex_edgeFlabby e (B.sheaf.extendBottom_edgeFlabby τ β hβ C B.flabby)
    · exact H.reindex_generated e (B.sheaf.extendBottom_generated τ β hβ C B.generated)
    · change H.vertex (splitVertex x b) = _
      rw [splitVertex_ne x b hxb.symm]
      exact B.top
    · intro z hz
      apply H.reindex_kernelMinimal e z
      by_cases hzx : z=x
      · subst z
        change H.KernelMinimal (splitVertex x x)
        rw [splitVertex_self]
        exact B.sheaf.extendBottom_kernelMinimal_bot τ β hβ C
      · change H.KernelMinimal (splitVertex x z)
        rw [splitVertex_ne x z hzx]
        apply B.sheaf.extendBottom_kernelMinimal_coe τ β hβ C ⟨z,hzx⟩
        apply B.minimal
        intro hzz
        exact hz (congrArg Subtype.val hzz)

include hscalar in
 theorem exists_boundarySheaf [Fintype V] [Fintype E] (b : V) (hb : ∀ x, x ≤ b)
    (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1) : Nonempty (BoundarySheaf hneg G α b) :=
  exists_boundarySheaf_card hneg G hscalar (Fintype.card V) b hb α hα rfl

end KLInvariance.MomentGraph

end


section


end

end OAI
