import OAI.Combinatorics.MatchingEntropy.OddCuts

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def onSide (G : LooplessGraph V E) (S : Finset V) :
    LooplessGraph (Option {v // v ∈ S}) {e // G.left e ∈ S ∨ G.right e ∈ S} where
  left e := if h : G.left e.val ∈ S then some ⟨G.left e.val, h⟩ else none
  right e := if h : G.right e.val ∈ S then some ⟨G.right e.val, h⟩ else none
  loopless e := by
    dsimp
    split_ifs with hl hr
    · intro he
      have hv := Option.some.inj he
      exact G.loopless e.val (congrArg Subtype.val hv)
    · simp
    · simp
    · rename_i hr
      exact (e.property.elim hl hr).elim

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_some (G : LooplessGraph V E) (S : Finset V)
    (v : {v // v ∈ S}) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident (some v) e ↔ G.Incident v.val e.val := by
  have hf : ∀ (w : V),
      (if h : w ∈ S then some (⟨w,h⟩ : {v // v ∈ S}) else none) = some v ↔ w=v.val := by
    intro w
    by_cases hw : w ∈ S
    · simp only [hw, ↓reduceDIte, Option.some.injEq]
      exact Subtype.ext_iff
    · simp only [hw, ↓reduceDIte]
      constructor
      · intro h
        cases h
      · intro he
        exact (hw (he.symm ▸ v.property)).elim
  change ((if h : G.left e.val ∈ S then some ⟨G.left e.val,h⟩ else none) = some v ∨
    (if h : G.right e.val ∈ S then some ⟨G.right e.val,h⟩ else none) = some v) ↔ _
  rw [hf, hf]
  rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_none (G : LooplessGraph V E) (S : Finset V)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident none e ↔ G.Crosses S e.val := by
  simp only [Incident, onSide, Crosses]
  by_cases hl : G.left e.val ∈ S <;> by_cases hr : G.right e.val ∈ S <;>
    simp [hl, hr]
  exact (e.property.elim hl hr).elim

def boundaryEdge (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} := Classical.choose (M.property none)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.boundaryEdge S M ∈ M.val :=
  (Classical.choose_spec (M.property none)).1.1

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_crosses (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.Crosses S (G.boundaryEdge S M).val :=
  (G.onSide_incident_none S _).mp (Classical.choose_spec (M.property none)).1.2

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem eq_boundaryEdge (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : {e // G.left e ∈ S ∨ G.right e ∈ S}}
    (he : e ∈ M.val) (hc : G.Crosses S e.val) : e = G.boundaryEdge S M :=
  (Classical.choose_spec (M.property none)).2 e ⟨he, (G.onSide_incident_none S e).mpr hc⟩

def liftedEdges (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) : Finset E :=
  M.val.image Subtype.val

omit [Fintype V] [Fintype E] in
theorem mem_liftedEdges (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M ↔ e ∈ M.val := by
  simp only [liftedEdges, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' : a = e := Subtype.ext he
    simpa only [he'] using ha
  · intro he
    exact ⟨e, he, rfl⟩

omit [Fintype V] [Fintype E] in
theorem liftedEdges_keep (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M) :
    G.left e ∈ S ∨ G.right e ∈ S := by
  rcases Finset.mem_image.mp he with ⟨a, _, rfl⟩
  exact a.property

omit [Fintype V] [Fintype E] in
theorem lifted_cross_eq_boundary (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M)
    (hc : G.Crosses S e) : e = (G.boundaryEdge S M).val := by
  let e' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨e, G.liftedEdges_keep S M he⟩
  exact congrArg Subtype.val (G.eq_boundaryEdge S M ((G.mem_liftedEdges S M e').mp he) hc)

omit [Fintype V] [Fintype E] in
theorem boundary_mem_lifted (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : (G.boundaryEdge S M).val ∈ G.liftedEdges S M :=
  (G.mem_liftedEdges S M _).mpr (G.boundaryEdge_mem S M)

omit [Fintype E] [DecidableEq E] in
theorem crosses_of_kept_both (G : LooplessGraph V E) (S : Finset V) (e : E)
    (h₁ : G.left e ∈ S ∨ G.right e ∈ S)
    (h₂ : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ) : G.Crosses S e := by
  simp only [Finset.mem_compl] at h₂
  unfold Crosses
  tauto

omit [Fintype E] in

theorem lifted_other_subset (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    {e : E} (he : e ∈ G.liftedEdges Sᶜ M₂)
    (hkeep : G.left e ∈ S ∨ G.right e ∈ S) : e ∈ G.liftedEdges S M₁ := by
  have hc := G.crosses_of_kept_both S e hkeep (G.liftedEdges_keep Sᶜ M₂ he)
  have hcb : G.Crosses Sᶜ e := (G.crosses_compl S e).mpr hc
  rw [G.lifted_cross_eq_boundary Sᶜ M₂ he hcb, ← heq]
  exact G.boundary_mem_lifted S M₁

omit [Fintype E] in

theorem mem_glued_left (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₁.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact (G.mem_liftedEdges S M₁ e).mp h
    · exact (G.mem_liftedEdges S M₁ e).mp (G.lifted_other_subset S M₁ M₂ heq h e.property)
  · intro h
    exact Or.inl ((G.mem_liftedEdges S M₁ e).mpr h)

omit [Fintype E] in
theorem mem_glued_right (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₂.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · have hc := G.crosses_of_kept_both S e.val (G.liftedEdges_keep S M₁ h) e.property
      have he := (G.lifted_cross_eq_boundary S M₁ h hc).trans heq
      apply (G.mem_liftedEdges Sᶜ M₂ e).mp
      rw [he]
      exact G.boundary_mem_lifted Sᶜ M₂
    · exact (G.mem_liftedEdges Sᶜ M₂ e).mp h
  · intro h
    exact Or.inr ((G.mem_liftedEdges Sᶜ M₂ e).mpr h)

omit [Fintype E] in
theorem glued_perfect (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val) :
    G.IsPerfectMatching (G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂) := by
  intro v
  by_cases hv : v ∈ S
  · obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₁.property (some ⟨v,hv⟩)
    have hev' := (G.onSide_incident_some S ⟨v,hv⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_left S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ S ∨ G.right f ∈ S := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv)
      · exact Or.inr (h.symm ▸ hv)
    let f' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨f,hk⟩
    have hf' : f' ∈ M₁.val := (G.mem_glued_left S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some S ⟨v,hv⟩ f').mpr hfv⟩)
  · have hv' := Finset.mem_compl.mpr hv
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₂.property (some ⟨v,hv'⟩)
    have hev' := (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_right S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ Sᶜ ∨ G.right f ∈ Sᶜ := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv')
      · exact Or.inr (h.symm ▸ hv')
    let f' : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ} := ⟨f,hk⟩
    have hf' : f' ∈ M₂.val := (G.mem_glued_right S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ f').mpr hfv⟩)

def glueMatching (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val}) : G.Matching :=
  ⟨G.liftedEdges S z.val.1 ∪ G.liftedEdges Sᶜ z.val.2,
    G.glued_perfect S z.val.1 z.val.2 z.property⟩

omit [Fintype E] in
theorem indicator_glue_left (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide S).indicator z.val.1 e := by
  simp only [indicator, glueMatching, G.mem_glued_left S z.val.1 z.val.2 z.property e]

omit [Fintype E] in
theorem indicator_glue_right (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide Sᶜ).indicator z.val.2 e := by
  simp only [indicator, glueMatching, G.mem_glued_right S z.val.1 z.val.2 z.property e]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundary_eq_iff_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) : (G.boundaryEdge S M).val=e.val ↔ e ∈ M.val := by
  constructor
  · intro h
    have he : G.boundaryEdge S M = e := Subtype.ext h
    exact he ▸ G.boundaryEdge_mem S M
  · intro h
    exact (congrArg Subtype.val (G.eq_boundaryEdge S M h hc)).symm

omit [Fintype V] in
theorem boundary_fiber (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e.val = (G.onSide S).mean p e := by
  unfold fiberMass mean
  apply Finset.sum_congr rfl
  intro M _
  simp only [G.boundary_eq_iff_mem S M e hc, indicator]
  split <;> simp

omit [Fintype V] in
theorem boundary_fiber_zero (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : E) (hc : ¬G.Crosses S e) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  have he : (G.boundaryEdge S M).val ≠ e := by
    intro h
    exact hc (h ▸ G.boundaryEdge_crosses S M)
  simp [he]

theorem couple_laws (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ)
    {p : (G.onSide S).Matching → ℝ} {q : (G.onSide Sᶜ).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (G.onSide S).Matching)
    (hq : q ∈ probabilitySimplex (G.onSide Sᶜ).Matching)
    (hpx : ∀ e, (G.onSide S).mean p e = x e.val)
    (hqx : ∀ e, (G.onSide Sᶜ).mean q e = x e.val) :
    ∃ r, r ∈ G.feasibleLaws x := by
  let f := fun M : (G.onSide S).Matching => (G.boundaryEdge S M).val
  let g := fun M : (G.onSide Sᶜ).Matching => (G.boundaryEdge Sᶜ M).val
  have hc : ∀ e, fiberMass p f e = fiberMass q g e := by
    intro e
    by_cases he : G.Crosses S e
    · have hk : G.left e ∈ S ∨ G.right e ∈ S := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      have he' := (G.crosses_compl S e).mpr he
      have hk' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := he'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      rw [G.boundary_fiber S p ⟨e,hk⟩ he, G.boundary_fiber Sᶜ q ⟨e,hk'⟩ he', hpx, hqx]
    · have he' : ¬G.Crosses Sᶜ e := fun h => he ((G.crosses_compl S e).mp h)
      rw [G.boundary_fiber_zero S p e he, G.boundary_fiber_zero Sᶜ q e he']
  let Z := {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching // f z.1=g z.2}
  let w : Z → ℝ := fun z => jointLaw p q f g z.val
  have hw : w ∈ probabilitySimplex Z := compatible_jointLaw_mem_simplex hp hq f g hc
  refine ⟨fiberMass w (G.glueMatching S), fiberMass_mem_simplex hw _, ?_⟩
  ext e
  rw [mean, fiberMass_expect]
  by_cases he : G.left e ∈ S ∨ G.right e ∈ S
  · have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide S).indicator z.val.1 ⟨e,he⟩ := fun z => G.indicator_glue_left S z ⟨e,he⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_first hp.1 f g hc
      (fun M => (G.onSide S).indicator M ⟨e,he⟩)).trans (hpx ⟨e,he⟩)
  · have he' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := by
      simp only [not_or] at he
      exact Or.inl (Finset.mem_compl.mpr he.1)
    have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide Sᶜ).indicator z.val.2 ⟨e,he'⟩ := fun z => G.indicator_glue_right S z ⟨e,he'⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_second hq.1 f g hc
      (fun M => (G.onSide Sᶜ).indicator M ⟨e,he'⟩)).trans (hqx ⟨e,he'⟩)

def sideMap (S : Finset V) (v : V) : Option {v // v ∈ S} :=
  if h : v ∈ S then some ⟨v,h⟩ else none

def liftVertices (S : Finset V) (T : Finset (Option {v // v ∈ S})) : Finset V :=
  Finset.univ.filter (fun v => sideMap S v ∈ T)

@[simp] theorem mem_liftVertices (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (v : V) :
    v ∈ liftVertices S T ↔ sideMap S v ∈ T := by simp [liftVertices]

omit [Fintype V] in
@[simp] theorem sideMap_some (S : Finset V) (v : {v // v ∈ S}) :
    sideMap S v.val = some v := by
  simp [sideMap, v.property]

theorem liftVertices_card (S : Finset V) (T : Finset (Option {v // v ∈ S}))
    (hn : none ∉ T) : (liftVertices S T).card = T.card := by
  apply Finset.card_bij (fun v _ => sideMap S v)
  · intro v hv
    exact (mem_liftVertices S T v).mp hv
  · intro v hv w hw he
    have hvS : v ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T v).mp hv
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    have hwS : w ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T w).mp hw
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    simp only [sideMap, hvS, hwS, ↓reduceDIte, Option.some.injEq] at he
    exact congrArg Subtype.val he
  · intro t ht
    cases t with
    | none => exact (hn ht).elim
    | some v => exact ⟨v.val, by simpa only [mem_liftVertices, sideMap_some] using ht, sideMap_some S v⟩

omit [Fintype E] [DecidableEq E] in
theorem onSide_cut_crosses (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Crosses T e ↔ G.Crosses (liftVertices S T) e.val := by
  simp only [Crosses, mem_liftVertices]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem crosses_lift_kept (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : E)
    (he : G.Crosses (liftVertices S T) e) : G.left e ∈ S ∨ G.right e ∈ S := by
  by_contra h
  simp only [not_or] at h
  simp only [Crosses, mem_liftVertices, sideMap, h.1, h.2, ↓reduceDIte] at he
  tauto

omit [DecidableEq E] in
theorem onSide_cutMass (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (T : Finset (Option {v // v ∈ S})) :
    (G.onSide S).cutMass (fun e => x e.val) T = G.cutMass x (liftVertices S T) := by
  simp only [cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_cut_crosses S T]
  exact sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses (liftVertices S T) e then x e else 0)
    (by intro e he; rw [ite_eq_right (fun hc => he (G.crosses_lift_kept S T e hc))])

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_some (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (v : {v // v ∈ S}) :
    (G.onSide S).degree (fun e => x e.val) (some v) = G.degree x v.val := by
  simp only [degree]
  simp_rw [G.onSide_incident_some S v]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Incident v.val e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl (h.symm ▸ v.property))
  · exact he (Or.inr (h.symm ▸ v.property))

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_none (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ) :
    (G.onSide S).degree (fun e => x e.val) none = G.cutMass x S := by
  simp only [degree, cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_incident_none S]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses S e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl h.1)
  · exact he (Or.inr h.2)

theorem odd_compl_of_even {W : Type uW} [Fintype W] [DecidableEq W]
    (hn : Even (Fintype.card W)) {T : Finset W} (hT : Odd T.card) : Odd Tᶜ.card := by
  rcases hn with ⟨k,hk⟩
  rcases hT with ⟨l,hl⟩
  have hle := Finset.card_le_univ T
  rw [Finset.card_compl]
  refine ⟨k-l-1, ?_⟩
  omega

omit [DecidableEq E] in

theorem restriction_mem_constraints (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (S : Finset V) (hS : Odd S.card)
    (htight : G.cutMass x S = 1) :
    (fun e : {e // G.left e ∈ S ∨ G.right e ∈ S} => x e.val) ∈
      (G.onSide S).constraintPolytope := by
  refine ⟨fun e => hx.1 e.val, ?_, ?_⟩
  · intro v
    cases v with
    | none => exact (G.onSide_degree_none S x).trans htight
    | some v => exact (G.onSide_degree_some S x v).trans (hx.2.1 v.val)
  · intro T hT
    by_cases hn : none ∈ T
    · have hn' : none ∉ Tᶜ := by simpa using hn
      have hnEven : Even (Fintype.card (Option {v // v ∈ S})) := by
        simp only [Fintype.card_option, Fintype.card_coe]
        exact hS.add_odd odd_one
      have hTc := odd_compl_of_even hnEven hT
      have hh := hx.2.2 (liftVertices S Tᶜ) (by rwa [liftVertices_card S Tᶜ hn'])
      rw [← G.onSide_cutMass S x Tᶜ] at hh
      simpa only [cutMass, cut_compl] using hh
    · rw [G.onSide_cutMass S x T]
      exact hx.2.2 _ (by rwa [liftVertices_card S T hn])

end MatchingEntropyBounds.LooplessGraph

end

end OAI
