import OAI.Combinatorics.MatchingEntropy.Degenerate

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section TriangleExpansion
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def CubicColoring (G : LooplessGraph V E) (c : E → Fin 3) : Prop :=
  ∀ v i, ∃! e, G.Incident v e ∧ c e = i

def colorEdges (c : E → Fin 3) (i : Fin 3) : Finset E := Finset.univ.filter (fun e => c e = i)

def triangleTip (v : V) (i : Fin 3) : V ⊕ Fin 2 := ![Sum.inl v, Sum.inr 0, Sum.inr 1] i

def triangleCollapse (v : V) : V ⊕ Fin 2 → V := Sum.elim id (fun _ => v)

def reattach (v : V) (i : Fin 3) (w : V) : V ⊕ Fin 2 :=
  if w = v then triangleTip v i else Sum.inl w

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem collapse_reattach (v : V) (i : Fin 3) (w : V) :
    triangleCollapse v (reattach v i w) = w := by
  by_cases h : w = v
  · subst w
    fin_cases i <;> simp [reattach,triangleTip,triangleCollapse]
  · simp [reattach,h,triangleCollapse]

def triangleExpansion (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    LooplessGraph (V ⊕ Fin 2) (E ⊕ Fin 3) where
  left := Sum.elim (fun e => reattach v (c e) (G.left e)) (fun i => triangleTip v (i + 1))
  right := Sum.elim (fun e => reattach v (c e) (G.right e)) (fun i => triangleTip v (i + 2))
  loopless := by
    intro e h
    rcases e with e | i
    · have hh := congrArg (triangleCollapse v) h
      exact G.loopless e ((collapse_reattach v (c e) (G.left e)).symm.trans
        (hh.trans (collapse_reattach v (c e) (G.right e))))
    · fin_cases i <;> simp [triangleTip] at h

def expandedColor (c : E → Fin 3) : E ⊕ Fin 3 → Fin 3 := Sum.elim c id

def triangleVertices (v : V) : Finset (V ⊕ Fin 2) := Finset.univ.image (triangleTip v)

def vertexColorEdge (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) (i : Fin 3) : E := Classical.choose (hc v i)

def triangleExtension (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) : (E → ℝ) →ₗ[ℝ] (E ⊕ Fin 3 → ℝ) where
  toFun x := Sum.elim x (fun i => x (vertexColorEdge G c hc v i))
  map_add' x y := by ext e; cases e <;> rfl
  map_smul' a x := by ext e; cases e <;> rfl

def IsSimpleLabelled (G : LooplessGraph V E) : Prop :=
  ∀ e f, ((G.left e = G.left f ∧ G.right e = G.right f) ∨
    (G.left e = G.right f ∧ G.right e = G.left f)) → e = f

end TriangleExpansion

def KleeV : ℕ → Type
  | 0 => Fin 2
  | n + 1 => KleeV n ⊕ Fin 2

def KleeE : ℕ → Type
  | 0 => Fin 3
  | n + 1 => KleeE n ⊕ Fin 3

noncomputable instance kleeVFintype (n : ℕ) : Fintype (KleeV n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 2))
  | succ n ih =>
    let : Fintype (KleeV n) := ih
    exact inferInstanceAs (Fintype (KleeV n ⊕ Fin 2))
noncomputable instance kleeEFintype (n : ℕ) : Fintype (KleeE n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 3))
  | succ n ih =>
    let : Fintype (KleeE n) := ih
    exact inferInstanceAs (Fintype (KleeE n ⊕ Fin 3))
noncomputable instance kleeVDecEq (n : ℕ) : DecidableEq (KleeV n) := Classical.decEq _
noncomputable instance kleeEDecEq (n : ℕ) : DecidableEq (KleeE n) := Classical.decEq _

def kleeRoot : (n : ℕ) → KleeV n
  | 0 => (0 : Fin 2)
  | n + 1 => Sum.inl (kleeRoot n)

def kleeColor : (n : ℕ) → KleeE n → Fin 3
  | 0 => id
  | n + 1 => expandedColor (kleeColor n)

def kleeGraph : (n : ℕ) → LooplessGraph (KleeV n) (KleeE n)
  | 0 => ⟨fun _ => (0 : Fin 2), fun _ => (1 : Fin 2), fun _ => by exact (by norm_num : (0 : Fin 2) ≠ 1)⟩
  | n + 1 => triangleExpansion (kleeGraph n) (kleeColor n) (kleeRoot n)

def kleeUniform (n : ℕ) : KleeE n → ℝ := fun _ => 1 / 3

def coloredVector {E : Type uE} (c : E → Fin 3) (i : Fin 3) : E → ℝ :=
  fun e => if c e = i then 1 else 0

def kleeTriangle (n : ℕ) : Set (KleeE n → ℝ) :=
  convexHull ℝ (Set.range (coloredVector (kleeColor n)))

def kleeLaw (n : ℕ) : (kleeGraph n).Matching → ℝ :=
  fun M => ∑ i : Fin 3, if M.val = colorEdges (kleeColor n) i then 1 / 3 else 0

section ExpansionSupport
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleTip_injective (v : V) : Function.Injective (triangleTip v) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_eq_tip (v w : V) (i j : Fin 3) :
    reattach v i w = triangleTip v j ↔ w = v ∧ i = j := by
  by_cases h : w = v
  · simp [reattach,h,(triangleTip_injective v).eq_iff]
  · fin_cases j <;> simp [reattach,h,triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_eq_inl (v w z : V) (hz : z ≠ v) (i : Fin 3) :
    reattach v i w = Sum.inl z ↔ w = z := by
  by_cases h : w = v
  · subst w
    fin_cases i <;> simp [reattach,triangleTip,hz.symm]
  · simp [reattach,h]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_old_tip (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (e : E) (j : Fin 3) :
    (triangleExpansion G c v).Incident (triangleTip v j) (Sum.inl e) ↔
      G.Incident v e ∧ c e = j := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inl,reattach_eq_tip]
  tauto

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_old_inl (G : LooplessGraph V E) (c : E → Fin 3) (v w : V)
    (hw : w ≠ v) (e : E) :
    (triangleExpansion G c v).Incident (Sum.inl w) (Sum.inl e) ↔ G.Incident w e := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inl,reattach_eq_inl v _ w hw]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_new_tip (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (i j : Fin 3) :
    (triangleExpansion G c v).Incident (triangleTip v j) (Sum.inr i) ↔ i ≠ j := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inr,
    (triangleTip_injective v).eq_iff]
  fin_cases i <;> fin_cases j <;> decide

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_new_inl (G : LooplessGraph V E) (c : E → Fin 3) (v w : V)
    (hw : w ≠ v) (i : Fin 3) :
    ¬(triangleExpansion G c v).Incident (Sum.inl w) (Sum.inr i) := by
  fin_cases i <;> simp [LooplessGraph.Incident,triangleExpansion,triangleTip,hw.symm]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem vertexColorEdge_spec (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) (i : Fin 3) :
    G.Incident v (vertexColorEdge G c hc v i) ∧ c (vertexColorEdge G c hc v i) = i :=
  (Classical.choose_spec (hc v i)).1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_vertexColorEdge (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) {e : E} {i : Fin 3} (he : G.Incident v e) (hi : c e = i) :
    e = vertexColorEdge G c hc v i := (Classical.choose_spec (hc v i)).2 e ⟨he,hi⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem colorEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (i : Fin 3) : G.IsPerfectMatching (colorEdges c i) := by
  intro v
  obtain ⟨e, he, hu⟩ := hc v i
  refine ⟨e,⟨by simp [colorEdges,he.2],he.1⟩,?_⟩
  intro f hf
  exact hu f ⟨hf.2,by simpa [colorEdges] using hf.1⟩

omit [Fintype V] [DecidableEq V] in
def colorMatching (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (i : Fin 3) : G.Matching := ⟨colorEdges c i,colorEdges_matching G c hc i⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem cubicColoring_expansion (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : CubicColoring (triangleExpansion G c v) (expandedColor c) := by
  intro w i
  have htip (j : Fin 3) : ∃! e, (triangleExpansion G c v).Incident (triangleTip v j) e ∧ expandedColor c e = i := by
    by_cases hij : i = j
    · subst j
      refine ⟨Sum.inl (vertexColorEdge G c hc v i), ⟨?_,(vertexColorEdge_spec G c hc v i).2⟩, ?_⟩
      · exact (expanded_incident_old_tip G c v _ _).mpr (vertexColorEdge_spec G c hc v i)
      · intro e he
        rcases e with e | e
        · apply congrArg Sum.inl
          exact eq_vertexColorEdge G c hc v ((expanded_incident_old_tip G c v e i).mp he.1).1 he.2
        · exact ((expanded_incident_new_tip G c v e i).mp he.1 he.2).elim
    · refine ⟨Sum.inr i,⟨(expanded_incident_new_tip G c v i j).mpr hij,rfl⟩,?_⟩
      intro e he
      rcases e with e | e
      · have hej := ((expanded_incident_old_tip G c v e j).mp he.1).2
        exact (hij (he.2.symm.trans hej)).elim
      · exact congrArg Sum.inr he.2
  rcases w with w | w
  · by_cases hw : w = v
    · subst w
      exact htip 0
    · obtain ⟨e,he,hu⟩ := hc w i
      refine ⟨Sum.inl e,⟨(expanded_incident_old_inl G c v w hw e).mpr he.1,he.2⟩,?_⟩
      intro f hf
      rcases f with f | f
      · exact congrArg Sum.inl (hu f ⟨(expanded_incident_old_inl G c v w hw f).mp hf.1,hf.2⟩)
      · exact (expanded_incident_new_inl G c v w hw f hf.1).elim
  · fin_cases w
    · exact htip 1
    · exact htip 2

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem triangleVertices_eq (v : V) :
    triangleVertices v = {Sum.inl v, Sum.inr 0, Sum.inr 1} := by
  simp [triangleVertices,Fin.univ_succ,triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem mem_triangleVertices_tip (v : V) (i : Fin 3) : triangleTip v i ∈ triangleVertices v :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_mem_triangle (v w : V) (i : Fin 3) :
    reattach v i w ∈ triangleVertices v ↔ w = v := by
  by_cases h : w = v
  · simp [reattach,h,mem_triangleVertices_tip]
  · simp [reattach,h,triangleVertices_eq]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_crosses_old (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (e : E) :
    (triangleExpansion G c v).Crosses (triangleVertices v) (Sum.inl e) ↔ G.Incident v e := by
  have hl := G.loopless e
  simp only [LooplessGraph.Crosses,triangleExpansion,Sum.elim_inl,reattach_mem_triangle,
    LooplessGraph.Incident]
  constructor
  · tauto
  · rintro (h | h)
    · exact Or.inl ⟨h,fun hh => hl (h.trans hh.symm)⟩
    · exact Or.inr ⟨fun hh => hl (hh.trans h.symm),h⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_crosses_new (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (i : Fin 3) :
    ¬(triangleExpansion G c v).Crosses (triangleVertices v) (Sum.inr i) := by
  simp [LooplessGraph.Crosses,triangleExpansion,mem_triangleVertices_tip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem triangleVertices_odd (v : V) : Odd (triangleVertices v).card := by
  have hcard : (triangleVertices v).card = 3 := by
    rw [triangleVertices,Finset.card_image_of_injective _ (triangleTip_injective v)]
    simp
  rw [hcard]
  norm_num

omit [Fintype V] [DecidableEq E] in
theorem expanded_cutMass (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (y : E ⊕ Fin 3 → ℝ) :
    (triangleExpansion G c v).cutMass y (triangleVertices v) = G.degree (fun e => y (Sum.inl e)) v := by
  simp only [LooplessGraph.cutMass,LooplessGraph.cut,Finset.sum_filter,Fintype.sum_sum_type,
    expanded_crosses_old,expanded_crosses_new,ite_false,Finset.sum_const_zero,add_zero,
    LooplessGraph.degree]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
def incidentChoice (G : LooplessGraph V E) (M : G.Matching) (v : V) : E :=
  Classical.choose (M.property v)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem incidentChoice_spec (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    incidentChoice G M v ∈ M.val ∧ G.Incident v (incidentChoice G M v) :=
  (Classical.choose_spec (M.property v)).1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_incidentChoice (G : LooplessGraph V E) (M : G.Matching) (v : V) {e : E}
    (he : e ∈ M.val) (hv : G.Incident v e) : e = incidentChoice G M v :=
  (Classical.choose_spec (M.property v)).2 e ⟨he,hv⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
def expandEdges (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    Finset (E ⊕ Fin 3) := M.val.disjSum {c (incidentChoice G M v)}

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expandEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).IsPerfectMatching (expandEdges G c v M) := by
  let e := incidentChoice G M v
  have he := incidentChoice_spec G M v
  have htip (j : Fin 3) : ∃! f, f ∈ expandEdges G c v M ∧
      (triangleExpansion G c v).Incident (triangleTip v j) f := by
    by_cases hj : c e = j
    · refine ⟨Sum.inl e,⟨by simp [expandEdges,he.1,e],
        (expanded_incident_old_tip G c v e j).mpr ⟨he.2,hj⟩⟩,?_⟩
      intro f hf
      rcases f with f | f
      · have hfm : f ∈ M.val := by simpa [expandEdges] using hf.1
        exact congrArg Sum.inl (eq_incidentChoice G M v hfm
          ((expanded_incident_old_tip G c v f j).mp hf.2).1)
      · have hfcol : f = c e := by simpa [expandEdges,e] using hf.1
        exact ((expanded_incident_new_tip G c v f j).mp hf.2 (hfcol.trans hj)).elim
    · refine ⟨Sum.inr (c e),⟨by simp [expandEdges,e],
        (expanded_incident_new_tip G c v (c e) j).mpr hj⟩,?_⟩
      intro f hf
      rcases f with f | f
      · have hfm : f ∈ M.val := by simpa [expandEdges] using hf.1
        have hfv := (expanded_incident_old_tip G c v f j).mp hf.2
        have hfe : f = e := eq_incidentChoice G M v hfm hfv.1
        exact (hj (hfe ▸ hfv.2)).elim
      · exact congrArg Sum.inr (by simpa [expandEdges,e] using hf.1)
  intro w
  rcases w with w | w
  · by_cases hw : w = v
    · subst w
      exact htip 0
    · obtain ⟨f,hf,hu⟩ := M.property w
      refine ⟨Sum.inl f,⟨by simpa [expandEdges] using hf.1,
        (expanded_incident_old_inl G c v w hw f).mpr hf.2⟩,?_⟩
      intro g hg
      rcases g with g | g
      · exact congrArg Sum.inl (hu g ⟨by simpa [expandEdges] using hg.1,
          (expanded_incident_old_inl G c v w hw g).mp hg.2⟩)
      · exact (expanded_incident_new_inl G c v w hw g hg.2).elim
  · fin_cases w
    · exact htip 1
    · exact htip 2

omit [Fintype V] [Fintype E] [DecidableEq E] in
def expandMatching (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).Matching := ⟨expandEdges G c v M,expandEdges_matching G c v M⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expandMatching_injective (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    Function.Injective (expandMatching G c v) := by
  intro M N h
  apply Subtype.ext
  ext e
  have hh := congrArg (fun K : (triangleExpansion G c v).Matching => Sum.inl e ∈ K.val) h
  simpa [expandMatching,expandEdges] using hh

omit [Fintype V] [Fintype E] in
theorem expandMatching_indicator (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).indicator (expandMatching G c v M) = triangleExtension G c hc v (G.indicator M) := by
  ext e
  rcases e with e | i
  · simp [LooplessGraph.indicator,expandMatching,expandEdges,triangleExtension]
  · have hh : c (incidentChoice G M v) = i ↔ vertexColorEdge G c hc v i ∈ M.val := by
      constructor
      · intro h
        rw [← eq_vertexColorEdge G c hc v (incidentChoice_spec G M v).2 h]
        exact (incidentChoice_spec G M v).1
      · intro h
        rw [← eq_incidentChoice G M v h (vertexColorEdge_spec G c hc v i).1]
        exact (vertexColorEdge_spec G c hc v i).2
    simp only [LooplessGraph.indicator,expandMatching,expandEdges,Finset.inr_mem_disjSum,
      Finset.mem_singleton,triangleExtension,LinearMap.coe_mk,AddHom.coe_mk,Sum.elim_inr]
    simp only [eq_comm (a := i) (b := c (incidentChoice G M v)),hh]

def CrossOnce (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) : Prop :=
  ∃! e, Sum.inl e ∈ N.val ∧ G.Incident v e

omit [Fintype V] in
theorem cutMass_indicator_card (G : LooplessGraph V E) (M : G.Matching) (S : Finset V) :
    G.cutMass (G.indicator M) S = ((M.val.filter (G.Crosses S)).card : ℝ) := by
  simp only [LooplessGraph.cutMass,LooplessGraph.indicator,Finset.sum_boole]
  congr 2
  ext e
  simp [LooplessGraph.cut,and_comm]

omit [Fintype V] in
theorem crossOnce_of_cut_eq_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching)
    (hN : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).indicator N) (triangleVertices v) = 1) :
    CrossOnce G c v N := by
  rw [cutMass_indicator_card] at hN
  have hn : (N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v))).card = 1 := by
    exact_mod_cast hN
  obtain ⟨f,hf⟩ := Finset.card_eq_one.mp hn
  have hfm : f ∈ N.val ∧ (triangleExpansion G c v).Crosses (triangleVertices v) f := by
    have hh : f ∈ N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v)) := by rw [hf]; simp
    exact Finset.mem_filter.mp hh
  rcases f with e | i
  · refine ⟨e,⟨hfm.1,(expanded_crosses_old G c v e).mp hfm.2⟩,?_⟩
    intro f hfg
    have hh : Sum.inl f ∈ N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v)) :=
      Finset.mem_filter.mpr ⟨hfg.1,(expanded_crosses_old G c v f).mpr hfg.2⟩
    rw [hf,Finset.mem_singleton] at hh
    exact Sum.inl.inj hh
  · exact (expanded_crosses_new G c v i hfm.2).elim

def contractEdges (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) : Finset E :=
  Finset.univ.filter (fun e => Sum.inl e ∈ N.val)

omit [Fintype V] in
theorem contractEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    G.IsPerfectMatching (contractEdges G c v N) := by
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [CrossOnce,contractEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hN
  · obtain ⟨f,hf,hu⟩ := N.property (Sum.inl w)
    rcases f with f | f
    · refine ⟨f,⟨by simpa [contractEdges] using hf.1,
        (expanded_incident_old_inl G c v w hw f).mp hf.2⟩,?_⟩
      intro g hg
      apply Sum.inl.inj
      exact hu (Sum.inl g) ⟨by simpa [contractEdges] using hg.1,
        (expanded_incident_old_inl G c v w hw g).mpr hg.2⟩
    · exact (expanded_incident_new_inl G c v w hw f hf.2).elim

def contractMatching (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) : G.Matching :=
  ⟨contractEdges G c v N,contractEdges_matching G c v N hN⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem fin3_add_one_ne (i : Fin 3) : i + 1 ≠ i := by fin_cases i <;> decide

omit [Fintype V] in
theorem expand_contract (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    expandMatching G c v (contractMatching G c v N hN) = N := by
  let M := contractMatching G c v N hN
  let e := incidentChoice G M v
  have he : Sum.inl e ∈ N.val ∧ G.Incident v e := by
    simpa [e,M,contractMatching,contractEdges] using incidentChoice_spec G M v
  have hcol : ∀ i : Fin 3, Sum.inr i ∈ N.val → i = c e := by
    intro i hi
    by_contra hn
    have hh := (N.property (triangleTip v (c e))).unique
      ⟨hi,(expanded_incident_new_tip G c v i (c e)).mpr hn⟩
      ⟨he.1,(expanded_incident_old_tip G c v e (c e)).mpr ⟨he.2,rfl⟩⟩
    cases hh
  have hmem : Sum.inr (c e) ∈ N.val := by
    obtain ⟨f,hf,_⟩ := N.property (triangleTip v (c e + 1))
    rcases f with f | i
    · have hfv := (expanded_incident_old_tip G c v f (c e + 1)).mp hf.2
      have hfe : f = e := hN.unique ⟨hf.1,hfv.1⟩ he
      have hh : c e = c e + 1 := hfe ▸ hfv.2
      exact (fin3_add_one_ne (c e) hh.symm).elim
    · exact hcol i hf.1 ▸ hf.1
  apply Subtype.ext
  ext f
  rcases f with f | i
  · simp [expandMatching,expandEdges,contractMatching,contractEdges]
  · simp only [expandMatching,expandEdges,Finset.inr_mem_disjSum,Finset.mem_singleton]
    change i = c e ↔ Sum.inr i ∈ N.val
    exact ⟨fun hi => hi ▸ hmem,hcol i⟩

omit [Fintype V] in
theorem range_expandMatching_of_crossOnce (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    N ∈ Set.range (expandMatching G c v) := ⟨contractMatching G c v N hN,expand_contract G c v N hN⟩

omit [Fintype V] in
theorem cutMass_mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (S : Finset V) :
    G.cutMass (G.mean p) S = ∑ M, p M * G.cutMass (G.indicator M) S := by
  simp only [LooplessGraph.cutMass,LooplessGraph.mean,Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype V] in
theorem positive_law_tight_cut (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (S : Finset V) (hS : Odd S.card)
    (ht : G.cutMass (G.mean p) S = 1) {M : G.Matching} (hM : p M ≠ 0) :
    G.cutMass (G.indicator M) S = 1 := by
  have hl (N : G.Matching) : 0 ≤ G.cutMass (G.indicator N) S - 1 :=
    sub_nonneg.mpr ((G.indicator_mem_constraintPolytope N).2.2 S hS)
  have heq : ∑ N, p N * (G.cutMass (G.indicator N) S - 1) = 0 := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,← cutMass_mean,ht,hp.2,sub_self]
  have hz : p M * (G.cutMass (G.indicator M) S - 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun N _ => mul_nonneg (hp.1 N) (hl N))).mp heq M (Finset.mem_univ M)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hM)

omit [Fintype V] in
theorem expanded_push_mean (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (q : G.Matching → ℝ) :
    (triangleExpansion G c v).mean (fiberMass q (expandMatching G c v)) =
      triangleExtension G c hc v (G.mean q) := by
  ext e
  rw [LooplessGraph.mean,fiberMass_expect]
  simp_rw [expandMatching_indicator G c hc v]
  rcases e with e | i <;> rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleExtension_injective (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : Function.Injective (triangleExtension G c hc v) := by
  intro x y h
  ext e
  exact congrFun h (Sum.inl e)

omit [Fintype V] in
theorem expanded_push_feasible (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) {x : E → ℝ} {q : G.Matching → ℝ}
    (hq : q ∈ G.feasibleLaws x) :
    fiberMass q (expandMatching G c v) ∈ (triangleExpansion G c v).feasibleLaws (triangleExtension G c hc v x) := by
  exact ⟨fiberMass_mem_simplex hq.1 _,by rw [expanded_push_mean G c hc v,hq.2]⟩

omit [Fintype V] in
theorem expanded_pull_simplex (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {p : (triangleExpansion G c v).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (triangleExpansion G c v).Matching)
    (ht : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1) :
    p = fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) ∧
    (fun M => p (expandMatching G c v M)) ∈ probabilitySimplex G.Matching := by
  have heq : fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) = p := by
    apply fiberMass_pullback _ _ (expandMatching_injective G c v)
    intro N hN
    by_contra hn
    exact hN (range_expandMatching_of_crossOnce G c v N (crossOnce_of_cut_eq_one G c v N
      (positive_law_tight_cut _ hp _ (triangleVertices_odd v) ht hn)))
  refine ⟨heq.symm,simplex_of_fiberMass _ _ (expandMatching_injective G c v) ?_⟩
  exact heq.symm ▸ hp

omit [Fintype V] in
theorem expanded_pull_feasible (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) {x : E → ℝ} (hx : x ∈ G.polytope)
    {p : (triangleExpansion G c v).Matching → ℝ}
    (hp : p ∈ (triangleExpansion G c v).feasibleLaws (triangleExtension G c hc v x)) :
    p = fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) ∧
    (fun M => p (expandMatching G c v M)) ∈ G.feasibleLaws x := by
  have ht : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1 := by
    rw [hp.2,expanded_cutMass]
    exact (G.polytope_subset_constraintPolytope hx).2.1 v
  obtain ⟨heq,hq⟩ := expanded_pull_simplex G c v hp.1 ht
  refine ⟨heq,hq,triangleExtension_injective G c hc v ?_⟩
  rw [← expanded_push_mean,← heq,hp.2]

omit [Fintype V] in
theorem expansion_image_eq (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) :
    triangleExtension G c hc v '' G.polytope =
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨q,hq⟩ := (G.mem_polytope_iff x).mp hx
    refine ⟨((triangleExpansion G c v).mem_polytope_iff _).mpr
      ⟨_,expanded_push_feasible G c hc v hq⟩,?_⟩
    rw [expanded_cutMass]
    exact (G.polytope_subset_constraintPolytope hx).2.1 v
  · rintro ⟨hy,ht⟩
    obtain ⟨p,hp⟩ := ((triangleExpansion G c v).mem_polytope_iff y).mp hy
    have ht' : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1 := hp.2.symm ▸ ht
    obtain ⟨heq,hq⟩ := expanded_pull_simplex G c v hp.1 ht'
    refine ⟨_,G.mean_mem_polytope hq,?_⟩
    rw [← expanded_push_mean,← heq,hp.2]

omit [Fintype V] in
theorem expansion_image_extreme (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) :
    IsExtreme ℝ (triangleExpansion G c v).polytope (triangleExtension G c hc v '' G.polytope) := by
  rw [expansion_image_eq]
  refine ⟨fun _ h => h.1, ?_⟩
  intro y hy z hz w hw hseg
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hseg
  refine ⟨hy,?_⟩
  have heq := hw.2
  rw [LooplessGraph.cutMass_linear] at heq
  have hyl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hy).2.2 _ (triangleVertices_odd v)
  have hzl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hz).2.2 _ (triangleVertices_odd v)
  apply le_antisymm _ hyl
  by_contra! hn
  have hpos := mul_pos ha (sub_pos.mpr hn)
  have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hzl)
  nlinarith

omit [Fintype V] in
theorem expansion_entropy (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) {x : E → ℝ} (hx : x ∈ G.polytope) :
    maxMatchingEntropy (triangleExpansion G c v) (triangleExtension G c hc v x) = maxMatchingEntropy G x := by
  have hxe : triangleExtension G c hc v x ∈ (triangleExpansion G c v).polytope :=
    (expansion_image_extreme G c hc v).subset ⟨x,hx,rfl⟩
  apply le_antisymm
  · obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained _ hxe
    obtain ⟨heq,hq⟩ := expanded_pull_feasible G c hc v hx hp
    rw [← hopt,heq,entropy_fiberMass_injective _ _ (expandMatching_injective G c v)]
    exact entropy_le_maxMatchingEntropy G hq
  · obtain ⟨q,hq,hopt⟩ := maxMatchingEntropy_attained G hx
    rw [← hopt,← entropy_fiberMass_injective q _ (expandMatching_injective G c v)]
    exact entropy_le_maxMatchingEntropy (triangleExpansion G c v) (expanded_push_feasible G c hc v hq)

theorem expansion_face (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c) (v : V) :
    let H := triangleExpansion G c v
    let f := triangleExtension G c hc v
    f '' G.polytope = {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1} ∧
    IsExtreme ℝ H.polytope (f '' G.polytope) ∧
    ∀ x ∈ G.polytope,
      minimalFace H (f x) = f '' minimalFace G x ∧
      faceDimension H (f x) = faceDimension G x ∧
      maxMatchingEntropy H (f x) = maxMatchingEntropy G x := by
  refine ⟨expansion_image_eq G c hc v,expansion_image_extreme G c hc v,?_⟩
  intro x hx
  exact ⟨(minimalFace_map _ G (triangleExtension G c hc v).toAffineMap
      (triangleExtension_injective G c hc v) (expansion_image_extreme G c hc v) hx).symm,
    (faceDimension_map _ G (triangleExtension G c hc v).toAffineMap
      (triangleExtension_injective G c hc v) (expansion_image_extreme G c hc v) hx).symm,
    expansion_entropy G c hc v hx⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem simplicity_expansion (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hG : IsSimpleLabelled G) : IsSimpleLabelled (triangleExpansion G c v) := by
  intro e f h
  rcases e with e | i <;> rcases f with f | j
  · apply congrArg Sum.inl
    apply hG e f
    rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Or.inl ⟨by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hl,
        by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hr⟩
    · exact Or.inr ⟨by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hl,
        by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hr⟩
  · exfalso
    rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;>
      simp only [triangleExpansion,Sum.elim_inl,Sum.elim_inr,reattach_eq_tip] at hl hr <;>
      exact G.loopless e (hl.1.trans hr.1.symm)
  · exfalso
    rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simp only [triangleExpansion,Sum.elim_inl,Sum.elim_inr] at hl hr
      have hl' := (reattach_eq_tip v _ _ _).mp hl.symm
      have hr' := (reattach_eq_tip v _ _ _).mp hr.symm
      exact G.loopless f (hl'.1.trans hr'.1.symm)
    · simp only [triangleExpansion,Sum.elim_inl,Sum.elim_inr] at hl hr
      have hl' := (reattach_eq_tip v _ _ _).mp hl.symm
      have hr' := (reattach_eq_tip v _ _ _).mp hr.symm
      exact G.loopless f (hr'.1.trans hl'.1.symm)
  · fin_cases i <;> fin_cases j <;> simp_all [triangleExpansion,triangleTip]

end ExpansionSupport
theorem klee_cubic (n : ℕ) : CubicColoring (kleeGraph n) (kleeColor n) := by
  induction n with
  | zero =>
    intro v i
    refine ⟨i,⟨?_,rfl⟩,?_⟩
    · fin_cases v <;> simp [LooplessGraph.Incident,kleeGraph,KleeV]
    · intro e he
      exact he.2
  | succ n ih => exact cubicColoring_expansion _ _ ih _

theorem klee_cardV (n : ℕ) : Fintype.card (KleeV n) = 2 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (KleeV n ⊕ Fin 2) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

theorem klee_cardE (n : ℕ) : Fintype.card (KleeE n) = 3 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (KleeE n ⊕ Fin 3) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

theorem klee_simple_one : IsSimpleLabelled (kleeGraph 1) := by
  intro e f h
  rcases e with e | i <;> rcases f with f | j
  · fin_cases e <;> fin_cases f <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
  · fin_cases e <;> fin_cases j <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
  · fin_cases i <;> fin_cases f <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
  · fin_cases i <;> fin_cases j <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]

theorem klee_simple (n : ℕ) (hn : 0 < n) : IsSimpleLabelled (kleeGraph n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => exact klee_simple_one
    | succ n => exact simplicity_expansion _ _ _ (ih (by omega))

theorem klee_graph_properties (n : ℕ) :
    Fintype.card (KleeV n) = 2 * (n + 1) ∧ Fintype.card (KleeE n) = 3 * (n + 1) ∧
    CubicColoring (kleeGraph n) (kleeColor n) ∧
    (∀ i, (kleeGraph n).IsPerfectMatching (colorEdges (kleeColor n) i)) ∧
    (∀ e, ∃! i, e ∈ colorEdges (kleeColor n) i) ∧
    (0 < n → IsSimpleLabelled (kleeGraph n)) := by
  refine ⟨klee_cardV n,klee_cardE n,klee_cubic n,fun i => colorEdges_matching _ _ (klee_cubic n) i,?_,klee_simple n⟩
  intro e
  refine ⟨kleeColor n e,by simp [colorEdges],?_⟩
  intro i hi
  exact (by simpa [colorEdges] using hi : kleeColor n e = i).symm

end MatchingEntropyBounds.Refined

end

end OAI
