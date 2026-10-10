import OAI.Computability.WitnessedChoice.TreeElimination

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ}

def facePlane : Face n → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def faceSide : Face n → Fin 4 → Edge n
  | .inl (i,j,k) => ![ex i j.castSucc k, ey i.succ j k, ex i j.succ k, ey i.castSucc j k]
  | .inr (.inl (i,j,k)) => ![ex i j k.castSucc, ez i.succ j k, ex i j k.succ, ez i.castSucc j k]
  | .inr (.inr (i,j,k)) => ![ey i j k.castSucc, ez i j.succ k, ey i j k.succ, ez i j.castSucc k]

def sideAxis : Fin 3 → Fin 4 → Fin 3 :=
  ![![0,1,0,1], ![0,2,0,2], ![1,2,1,2]]

lemma faceSide_axis (f : Face n) (i : Fin 4) :
    edgeAxis (faceSide f i) = sideAxis (facePlane f) i := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;>
    fin_cases i <;> rfl

lemma faceSide_injective {f g : Face n} (hp : facePlane f = facePlane g)
    (i : Fin 4) (he : faceSide f i = faceSide g i) : f = g := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;>
    rcases g with ⟨a,b,c⟩ | (⟨a,b,c⟩ | ⟨a,b,c⟩) <;>
    simp only [facePlane] at hp
  all_goals first | contradiction | skip
  all_goals fin_cases i <;> simpa [faceSide,ex,ey,ez] using he

lemma support_cycle (f : Face n) (e : Edge n) (h : cycle f e ≠ 0) :
    ∃ i, faceSide f i = e := by
  by_contra hn
  have hh (i : Fin 4) : e ≠ faceSide f i := fun he => hn ⟨i,he.symm⟩
  apply h
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩)
  all_goals
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    simp [faceSide] at h0 h1 h2 h3
    simp [cycle,Pi.single_eq_of_ne,h0,h1,h2,h3]

lemma edgeFaces_card_le_four (e : Edge n) : Fintype.card (EdgeFaces e) ≤ 4 := by
  let chooseSide (f : EdgeFaces e) : Fin 4 := (support_cycle f.val e f.property).choose
  have hs (f : EdgeFaces e) : faceSide f.val (chooseSide f) = e :=
    (support_cycle f.val e f.property).choose_spec
  let key (f : EdgeFaces e) : {k : Fin 3 × Fin 4 // sideAxis k.1 k.2 = edgeAxis e} :=
    ⟨(facePlane f.val,chooseSide f), (faceSide_axis f.val (chooseSide f)).symm.trans (congrArg edgeAxis (hs f))⟩
  have hi : Function.Injective key := by
    intro f g h
    have h' := congrArg Subtype.val h
    have hp := congrArg Prod.fst h'
    have hc := congrArg Prod.snd h'
    apply Subtype.ext
    apply faceSide_injective hp (chooseSide f)
    change chooseSide f = chooseSide g at hc
    exact (hs f).trans (by rw [hc,hs g])
  have ht : Fintype.card {k : Fin 3 × Fin 4 // sideAxis k.1 k.2 = edgeAxis e} = 4 := by
    generalize edgeAxis e = a
    fin_cases a <;> decide
  simpa only [ht] using Fintype.card_le_of_injective key hi

def faceCorner : Face n → Fin 4 → Vertex n
  | .inl (i,j,k) => ![(i.castSucc,j.castSucc,k),(i.succ,j.castSucc,k),
      (i.succ,j.succ,k),(i.castSucc,j.succ,k)]
  | .inr (.inl (i,j,k)) => ![(i.castSucc,j,k.castSucc),(i.succ,j,k.castSucc),
      (i.succ,j,k.succ),(i.castSucc,j,k.succ)]
  | .inr (.inr (i,j,k)) => ![(i,j.castSucc,k.castSucc),(i,j.succ,k.castSucc),
      (i,j.succ,k.succ),(i,j.castSucc,k.succ)]

lemma faceCorner_injective {f g : Face n} (hp : facePlane f = facePlane g)
    (i : Fin 4) (he : faceCorner f i = faceCorner g i) : f = g := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;>
    rcases g with ⟨a,b,c⟩ | (⟨a,b,c⟩ | ⟨a,b,c⟩) <;>
    simp only [facePlane] at hp
  all_goals first | contradiction | skip
  all_goals fin_cases i <;> simpa [faceCorner] using he

lemma faceSide_endpoints (f : Face n) (i : Fin 4) (v : Vertex n)
    (hv : incident v (faceSide f i)) : ∃ j, faceCorner f j = v := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals
    rcases hv with h | h
    all_goals first
      | exact ⟨0,h⟩
      | exact ⟨1,h⟩
      | exact ⟨2,h⟩
      | exact ⟨3,h⟩

abbrev VertexFaces (v : Vertex n) :=
  {f : Face n // ∃ e : IncidentEdges v, cycle f e.val ≠ 0}

lemma vertexFaces_card_le_twelve (v : Vertex n) : Fintype.card (VertexFaces v) ≤ 12 := by
  have hc (f : VertexFaces v) : ∃ i, faceCorner f.val i = v := by
    obtain ⟨e,he⟩ := f.property
    obtain ⟨i,hi⟩ := support_cycle f.val e.val he
    exact faceSide_endpoints f.val i v (hi ▸ e.property)
  let key (f : VertexFaces v) : Fin 3 × Fin 4 := (facePlane f.val,(hc f).choose)
  have hi : Function.Injective key := by
    intro f g h
    have hp := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    apply Subtype.ext
    apply faceCorner_injective hp (hc f).choose
    change (hc f).choose = (hc g).choose at hk
    exact (hc f).choose_spec.trans (by rw [hk,(hc g).choose_spec])
  simpa using Fintype.card_le_of_injective key hi

lemma localGroup_card_le_upper (e : Edge n) : Fintype.card (LocalGroup e) ≤ 3^9 := by
  have hc : Fintype.card (LocalGroup e) = 3 ^ (2 * Fintype.card (EdgeFaces e) + 1) := by
    rw [← Nat.card_eq_fintype_card,Support.H.ambient_card]
    congr 1
    rw [Module.finrank_pi_fintype]
    simp [Support.Plane,Support.Scalar,Module.finrank_prod,Nat.mul_comm]
  rw [hc]
  exact Nat.pow_le_pow_right (by omega) (by have := edgeFaces_card_le_four e; omega)

lemma exists_incident (hn : 1 ≤ n) (v : Vertex n) : Nonempty (IncidentEdges v) := by
  rcases v with ⟨i,j,k⟩
  by_cases hi : i.val < n
  · refine ⟨⟨ex ⟨i.val,hi⟩ j k,Or.inr ?_⟩⟩
    simp only [ex,tail,Prod.mk.injEq,and_true]
    exact Fin.ext rfl
  · refine ⟨⟨ex ⟨n-1,by omega⟩ j k,Or.inl ?_⟩⟩
    simp only [ex,head,Prod.mk.injEq,and_true]
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

lemma epsilon_ne_zero (v : Vertex n) (e : IncidentEdges v) : epsilon v e.val ≠ 0 := by
  by_cases hh : head e.val = v
  · have ht : tail e.val ≠ v := fun h => head_ne_tail e.val (hh.trans h.symm)
    simp [epsilon,hh,ht]
  · have ht := e.property.resolve_left hh
    simp [epsilon,hh,ht]

variable {b : Vertex n → Scalar} {v : Vertex n}

def Configuration.faceValue (s : Configuration b v) (f : VertexFaces v) : Plane :=
  (s.state f.property.choose).face ⟨f.val,f.property.choose_spec⟩

lemma Configuration.faceValue_eq (s : Configuration b v) (e : IncidentEdges v)
    (f : EdgeFaces e.val) :
    s.faceValue ⟨f.val,⟨e,f.property⟩⟩ = (s.state e).face f := by
  exact s.compatible _ e f.val _ f.property

def Configuration.code (e0 : IncidentEdges v) (s : Configuration b v) :
    (VertexFaces v → Plane) × ({e : IncidentEdges v // e ≠ e0} → Scalar) :=
  (s.faceValue,fun e => (s.state e.val).flow)

lemma Configuration.code_injective (e0 : IncidentEdges v) :
    Function.Injective (Configuration.code (b := b) e0) := by
  intro s t h
  have hf (e : IncidentEdges v) : (s.state e).face = (t.state e).face := by
    funext f
    rw [←s.faceValue_eq e f,←t.faceValue_eq e f]
    exact congrFun (congrArg Prod.fst h) ⟨f.val,⟨e,f.property⟩⟩
  have hz (e : IncidentEdges v) (he : e ≠ e0) : (s.state e).flow = (t.state e).flow :=
    congrFun (congrArg Prod.snd h) ⟨e,he⟩
  have hz0 : (s.state e0).flow = (t.state e0).flow := by
    have hsum := s.charge.trans t.charge.symm
    change (∑ e : IncidentEdges v, epsilon v e.val * (s.state e).flow) =
      ∑ e : IncidentEdges v, epsilon v e.val * (t.state e).flow at hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0),
      ← Finset.add_sum_erase _ (fun e : IncidentEdges v => epsilon v e.val * (t.state e).flow)
        (Finset.mem_univ e0)] at hsum
    have hr : (∑ e ∈ Finset.univ.erase e0, epsilon v e.val * (s.state e).flow) =
        ∑ e ∈ Finset.univ.erase e0, epsilon v e.val * (t.state e).flow := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hz e (Finset.ne_of_mem_erase he)]
    rw [hr] at hsum
    exact mul_left_cancel₀ (epsilon_ne_zero v e0) (add_right_cancel hsum)
  apply Configuration.ext
  intro e
  apply Support.H.ext (hf e)
  by_cases he : e = e0
  · subst e
    exact hz0
  · exact hz e he

lemma configuration_card_le_upper (hn : 1 ≤ n) (b : Vertex n → Scalar) (v : Vertex n) :
    Fintype.card (Configuration b v) ≤ 3^29 := by
  classical
  let e0 := Classical.choice (exists_incident hn v)
  rw [← Nat.card_eq_fintype_card]
  have hcard := Nat.card_le_card_of_injective _ (Configuration.code_injective (b := b) e0)
  have he : Nat.card {e : IncidentEdges v // e ≠ e0} ≤ 5 := by
    rw [Nat.card_eq_fintype_card]
    have hc := Fintype.card_subtype_compl (fun e : IncidentEdges v => e = e0)
    have hdeg : Fintype.card (IncidentEdges v) ≤ 6 := degree_le_six v
    have hone : Fintype.card {e : IncidentEdges v // e = e0} = 1 := by simp
    rw [hone] at hc
    rw [hc]
    omega
  have hc : Nat.card ((VertexFaces v → Plane) ×
      ({e : IncidentEdges v // e ≠ e0} → Scalar)) =
      3 ^ (2 * Nat.card (VertexFaces v) + Nat.card {e : IncidentEdges v // e ≠ e0}) := by
    simp only [Nat.card_prod,Nat.card_fun,Plane,Support.Scalar,Scalar]
    have hz : Nat.card (ZMod 3) = 3 := by simp [Nat.card_eq_fintype_card]
    rw [hz]
    rw [←pow_two,←pow_mul,←pow_add]
  rw [hc] at hcard
  exact hcard.trans (Nat.pow_le_pow_right (by omega) (by
    have hh : Nat.card (VertexFaces v) ≤ 12 := by
      simpa only [Nat.card_eq_fintype_card] using vertexFaces_card_le_twelve v
    omega))

end





noncomputable section

open Classical WitnessedChoice.TreeTest

variable {n : ℕ}

structure ParentEdges (T : RootedTree (Vertex n)) where
  edge : (v : Vertex n) → v ≠ T.root → Edge n
  endpoints : ∀ v h,
    (head (edge v h) = v ∧ tail (edge v h) = T.parent v) ∨
    (tail (edge v h) = v ∧ head (edge v h) = T.parent v)

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def treeEdges : Finset (Edge n) :=
  Finset.univ.image (fun v : {v : Vertex n // v ≠ T.root} => P.edge v.val v.property)

def sign (v : Vertex n) (h : v ≠ T.root) : Scalar :=
  if head (P.edge v h) = v then 1 else -1

lemma edge_mem (v : Vertex n) (hv : v ≠ T.root) : P.edge v hv ∈ P.treeEdges := by
  exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩

def route (Q : ParentEdges T) (v : Vertex n) : Edge n → Scalar :=
  if hv : v = T.root then 0 else
    Pi.single (Q.edge v hv) (Q.sign v hv) + route Q (T.parent v)
termination_by T.level v
decreasing_by exact T.parent_lower v hv

lemma boundary_single (e : Edge n) (a : Scalar) :
    boundary (Pi.single e a) = a • (Pi.single (head e) 1 - Pi.single (tail e) 1) := by
  rw [WitnessedSeparation.Grid.boundary_single]
  simp only [smul_sub,← Pi.single_smul,smul_eq_mul,mul_one]

lemma boundary_parent (v : Vertex n) (hv : v ≠ T.root) :
    boundary (Pi.single (P.edge v hv) (P.sign v hv)) =
      Pi.single v 1 - Pi.single (T.parent v) 1 := by
  rw [boundary_single]
  rcases P.endpoints v hv with ⟨hh,ht⟩ | ⟨ht,hh⟩
  · simp [sign,hh,ht]
  · have hne : head (P.edge v hv) ≠ v := by
      intro he
      have hp : T.parent v = v := hh.symm.trans he
      have := T.parent_lower v hv
      rw [hp] at this
      omega
    rw [sign,ite_eq_right hne,ht,hh,neg_smul,one_smul]
    abel

lemma boundary_route (v : Vertex n) :
    boundary (P.route v) = Pi.single v 1 - Pi.single T.root 1 := by
  induction v using (measure T.level).wf.induction with
  | h v ih =>
    rw [route]
    split_ifs with hv
    · subst v
      simp
    · rw [map_add,P.boundary_parent v hv,ih (T.parent v) (T.parent_lower v hv)]
      abel

lemma route_zero_off_tree {e : Edge n} (he : e ∉ P.treeEdges) (v : Vertex n) : P.route v e = 0 := by
  induction v using (measure T.level).wf.induction with
  | h v ih =>
    rw [route]
    split_ifs with hv
    · rfl
    · have hne : e ≠ P.edge v hv := fun h => he (h.symm ▸ P.edge_mem v hv)
      simp only [Pi.add_apply,Pi.single_eq_of_ne hne,zero_add]
      exact ih (T.parent v) (T.parent_lower v hv)

def fundamental (e : Edge n) (a : Scalar) : Edge n → Scalar :=
  Pi.single e a + a • P.route (tail e) - a • P.route (head e)

lemma boundary_fundamental (e : Edge n) (a : Scalar) : boundary (P.fundamental e a) = 0 := by
  rw [fundamental,map_sub,map_add,map_smul,map_smul,boundary_single,
    P.boundary_route,P.boundary_route]
  simp only [smul_sub]
  abel

def flow (e : Edge n) (a : Scalar) : FlowSpace n := ⟨P.fundamental e a,P.boundary_fundamental e a⟩

lemma flow_self (e : Edge n) (he : e ∉ P.treeEdges) (a : Scalar) : (P.flow e a).val e = a := by
  simp [flow,fundamental,P.route_zero_off_tree he]

lemma flow_other (e f : Edge n) (hf : f ∉ P.treeEdges) (hne : f ≠ e) (a : Scalar) :
    (P.flow e a).val f = 0 := by
  simp [flow,fundamental,P.route_zero_off_tree hf,Pi.single_eq_of_ne hne]

def solve (r : Vertex n → Scalar) : Edge n → Scalar := ∑ v, r v • P.route v

lemma boundary_solve (r : Vertex n → Scalar) (hr : ∑ v, r v = 0) :
    boundary (P.solve r) = r := by
  simp only [solve,map_sum,map_smul,P.boundary_route,smul_sub,Finset.sum_sub_distrib]
  rw [← Finset.sum_smul,hr,zero_smul,sub_zero]
  funext v
  simp [Pi.single_apply]

lemma solve_zero_off_tree (r : Vertex n → Scalar) {e : Edge n} (he : e ∉ P.treeEdges) :
    P.solve r e = 0 := by
  simp only [solve,Finset.sum_apply,Pi.smul_apply,P.route_zero_off_tree he,smul_zero,Finset.sum_const_zero]

lemma extend_scalars (b : Vertex n → Scalar) (hb : ∑ v, b v = 0) (z : Edge n → Scalar) :
    ∃ w : Edge n → Scalar, boundary w = b ∧ ∀ e, e ∉ P.treeEdges → w e = z e := by
  let r := b - boundary z
  have hr : ∑ v, r v = 0 := by
    simp only [r,Pi.sub_apply,Finset.sum_sub_distrib,hb,sum_boundary,sub_self]
  refine ⟨z + P.solve r, ?_, ?_⟩
  · rw [map_add,P.boundary_solve r hr]
    dsimp [r]
    abel
  · intro e he
    simp only [Pi.add_apply,P.solve_zero_off_tree r he,add_zero]

end ParentEdges

end





noncomputable section

open Classical Support WitnessedChoice.TreeTest

variable {n : ℕ}

def ConsistentSelection (x : Finset (Σ e : Edge n, LocalGroup e)) : Prop :=
  (∀ r ∈ x, ∀ s ∈ x, r.1 = s.1 → r = s) ∧
  ∀ r ∈ x, ∀ s ∈ x, ∀ f : Face n, ∀ hr : cycle f r.1 ≠ 0, ∀ hs : cycle f s.1 ≠ 0,
    r.2.face ⟨f,hr⟩ = s.2.face ⟨f,hs⟩

def selectedVectors (x : Finset (Σ e : Edge n, LocalGroup e)) (f : Face n) : Plane :=
  if h : ∃ r ∈ x, cycle f r.1 ≠ 0 then
    h.choose.2.face ⟨f,h.choose_spec.2⟩ else 0

def selectedScalars (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) : Scalar :=
  if h : ∃ r ∈ x, r.1 = e then h.choose.2.flow else 0

lemma selectedVectors_preserves {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x)
    (f : EdgeFaces r.1) : selectedVectors x f.val = r.2.face f := by
  have h : ∃ s ∈ x, cycle f.val s.1 ≠ 0 := ⟨r,hr,f.property⟩
  rw [selectedVectors,dite_eq_left h]
  exact hx.2 h.choose h.choose_spec.1 r hr f.val h.choose_spec.2 f.property

lemma selectedScalars_preserves {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x) :
    selectedScalars x r.1 = r.2.flow := by
  have h : ∃ s ∈ x, s.1 = r.1 := ⟨r,hr,rfl⟩
  rw [selectedScalars,dite_eq_left h,hx.1 h.choose h.choose_spec.1 r hr h.choose_spec.2]

def globalStates (u : Face n → Plane) (z : Edge n → Scalar) (e : Edge n) : LocalGroup e :=
  ⟨fun f => u f.val,z e⟩

lemma globalStates_compatible (u : Face n → Plane) (z : Edge n → Scalar) (v : Vertex n) :
    Compatible (fun e : IncidentEdges v => globalStates u z e.val) := by
  intro e e' f hf hf'
  rfl

lemma globalStates_charge (u : Face n → Plane) (z : Edge n → Scalar) (v : Vertex n) :
    divergence (fun e : IncidentEdges v => globalStates u z e.val) = boundary z v :=
  sum_incident z v

def globalConfiguration (b : Vertex n → Scalar) (u : Face n → Plane)
    (z : Edge n → Scalar) (hz : boundary z = b) (v : Vertex n) : Configuration b v where
  state := fun e => globalStates u z e.val
  compatible := globalStates_compatible u z v
  charge := (globalStates_charge u z v).trans (congrFun hz v)

theorem extend_consistent_selection {T : RootedTree (Vertex n)} (P : ParentEdges T)
    (b : Vertex n → Scalar) (hb : ∑ v, b v = 0)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges) :
    ∃ (s : (e : Edge n) → LocalGroup e) (t : (v : Vertex n) → Configuration b v),
      (∀ r ∈ x, s r.1 = r.2) ∧ ∀ v (e : IncidentEdges v), (t v).state e = s e.val := by
  obtain ⟨z,hz,hkeep⟩ := P.extend_scalars b hb (selectedScalars x)
  refine ⟨globalStates (selectedVectors x) z,globalConfiguration b (selectedVectors x) z hz,?_,?_⟩
  · intro r hr
    apply H.ext
    · funext f
      exact selectedVectors_preserves hx hr f
    · exact (hkeep r.1 (hoff r hr)).trans (selectedScalars_preserves hx hr)
  · intro v e
    rfl

theorem total_charge_of_global_configurations (b : Vertex n → Scalar)
    (s : (e : Edge n) → LocalGroup e) (t : (v : Vertex n) → Configuration b v)
    (h : ∀ v (e : IncidentEdges v), (t v).state e = s e.val) : ∑ v, b v = 0 := by
  have hb : boundary (fun e => (s e).flow) = b := by
    funext v
    rw [← sum_incident]
    exact (show divergence (fun e : IncidentEdges v => s e.val) = b v by
      have hh : (t v).state = fun e : IncidentEdges v => s e.val := funext (h v)
      rw [← hh]
      exact (t v).charge)
  rw [← hb]
  exact sum_boundary _

end





noncomputable section

open Classical Support

variable {n : ℕ} {v : Vertex n} {b : Vertex n → Scalar}

lemma incident_on_axis (hn : 1 ≤ n) (v : Vertex n) (a : Fin 3) :
    ∃ e : IncidentEdges v, edgeAxis e.val = a := by
  rcases v with ⟨i,j,k⟩
  fin_cases a
  · by_cases hi : i.val = 0
    · refine ⟨⟨ex ⟨0,by omega⟩ j k,Or.inr ?_⟩,rfl⟩
      simp only [ex,tail,Prod.mk.injEq,and_true]
      apply Fin.ext
      exact hi.symm
    · refine ⟨⟨ex ⟨i.val-1,by omega⟩ j k,Or.inl ?_⟩,rfl⟩
      simp only [ex,head,Prod.mk.injEq,and_true]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · by_cases hj : j.val = 0
    · refine ⟨⟨ey i ⟨0,by omega⟩ k,Or.inr ?_⟩,rfl⟩
      simp only [ey,tail,Prod.mk.injEq,true_and,and_true]
      apply Fin.ext
      exact hj.symm
    · refine ⟨⟨ey i ⟨j.val-1,by omega⟩ k,Or.inl ?_⟩,rfl⟩
      simp only [ey,head,Prod.mk.injEq,true_and,and_true]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · by_cases hk : k.val = 0
    · refine ⟨⟨ez i j ⟨0,by omega⟩,Or.inr ?_⟩,rfl⟩
      simp only [ez,tail,Prod.mk.injEq,true_and]
      apply Fin.ext
      exact hk.symm
    · refine ⟨⟨ez i j ⟨k.val-1,by omega⟩,Or.inl ?_⟩,rfl⟩
      simp only [ez,head,Prod.mk.injEq,true_and]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

lemma fin_three_other (a b : Fin 3) : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact ⟨0,by decide,by decide⟩
    | exact ⟨1,by decide,by decide⟩
    | exact ⟨2,by decide,by decide⟩

lemma other_incident (hn : 1 ≤ n) (e e' : IncidentEdges v) :
    ∃ h : IncidentEdges v, h ≠ e ∧ h ≠ e' := by
  obtain ⟨a,ha,ha'⟩ := fin_three_other (edgeAxis e.val) (edgeAxis e'.val)
  obtain ⟨h,hh⟩ := incident_on_axis hn v a
  refine ⟨h,?_,?_⟩
  · intro he
    subst h
    exact ha hh.symm
  · intro he
    subst h
    exact ha' hh.symm

def extendVertexScalars (b : Vertex n → Scalar) (v : Vertex n) (e0 : IncidentEdges v)
    (z : IncidentEdges v → Scalar) (e : IncidentEdges v) : Scalar :=
  if e = e0 then (epsilon v e0.val)⁻¹ *
    (b v - ∑ h ∈ Finset.univ.erase e0, epsilon v h.val * z h)
  else z e

lemma extendVertexScalars_charge (e0 : IncidentEdges v) (z : IncidentEdges v → Scalar) :
    (∑ e, epsilon v e.val * extendVertexScalars b v e0 z e) = b v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
  have he : (∑ e ∈ Finset.univ.erase e0,
      epsilon v e.val * extendVertexScalars b v e0 z e) =
      ∑ e ∈ Finset.univ.erase e0, epsilon v e.val * z e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [extendVertexScalars,ite_eq_right (Finset.ne_of_mem_erase he)]
  rw [he,extendVertexScalars,ite_eq_left rfl,mul_inv_cancel_left₀ (epsilon_ne_zero v e0),sub_add_cancel]

lemma exists_configuration_two (hn : 1 ≤ n) (e e' : IncidentEdges v) (hne : e ≠ e')
    (s : LocalGroup e.val) (t : LocalGroup e'.val)
    (hc : ∀ f : Face n, ∀ he : cycle f e.val ≠ 0, ∀ he' : cycle f e'.val ≠ 0,
      s.face ⟨f,he⟩ = t.face ⟨f,he'⟩) :
    ∃ c : Configuration b v, c.state e = s ∧ c.state e' = t := by
  obtain ⟨e0,hr,hr'⟩ := other_incident hn e e'
  let u (f : Face n) : Plane := if h : cycle f e.val ≠ 0 then s.face ⟨f,h⟩
    else if h' : cycle f e'.val ≠ 0 then t.face ⟨f,h'⟩ else 0
  let z (h : IncidentEdges v) : Scalar := if h = e then s.flow else if h = e' then t.flow else 0
  let c : Configuration b v :=
    { state := fun h => ⟨fun f => u f.val,extendVertexScalars b v e0 z h⟩
      compatible := by intro h h' f hf hf'; rfl
      charge := extendVertexScalars_charge e0 z }
  refine ⟨c,?_,?_⟩
  · apply H.ext
    · funext f
      exact dite_eq_left f.property
    · change extendVertexScalars b v e0 z e = s.flow
      simp only [extendVertexScalars,ite_eq_right (Ne.symm hr),z,ite_eq_left rfl]
  · apply H.ext
    · funext f
      change u f.val = t.face f
      dsimp only [u]
      split_ifs with he he'
      · exact hc f.val he f.property
      · rfl
      · exact (he' f.property).elim
    · change extendVertexScalars b v e0 z e' = t.flow
      simp only [extendVertexScalars,ite_eq_right (Ne.symm hr'),z,ite_eq_right (Ne.symm hne),ite_true]

end





noncomputable section

open Classical Support

variable {n : ℕ}

def vertexCoord (v : Vertex n) : Fin 3 → Fin (n+1) := ![v.1,v.2.1,v.2.2]

def planeAxis (p a : Fin 3) : Prop := ∃ i : Fin 4, sideAxis p i = a

instance (p a : Fin 3) : Decidable (planeAxis p a) := Classical.propDecidable _

def faceBase (f : Face n) : Fin 3 → Fin (n+1) := vertexCoord (faceCorner f 0)

lemma vertexCoord_injective : Function.Injective (vertexCoord (n := n)) := by
  intro v w h
  exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2))

lemma faceBase_injective {f g : Face n} (hp : facePlane f = facePlane g)
    (h : faceBase f = faceBase g) : f = g :=
  faceCorner_injective hp 0 (vertexCoord_injective h)

lemma two_axes_plane : ∀ p q a b : Fin 3, a ≠ b →
    planeAxis p a → planeAxis p b → planeAxis q a → planeAxis q b → p = q := by
  unfold planeAxis
  decide

lemma plane_axis_exhaust : ∀ p a b c : Fin 3, a ≠ b → planeAxis p a → planeAxis p b →
    c = a ∨ c = b ∨ ¬ planeAxis p c := by
  unfold planeAxis
  decide

lemma side_axis_in_plane (f : Face n) (i : Fin 4) :
    planeAxis (facePlane f) (edgeAxis (faceSide f i)) := ⟨i,(faceSide_axis f i).symm⟩

lemma faceBase_on_axis (f : Face n) (i : Fin 4) :
    faceBase f (edgeAxis (faceSide f i)) =
      vertexCoord (tail (faceSide f i)) (edgeAxis (faceSide f i)) := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i <;> rfl

lemma faceBase_outside (f : Face n) (i : Fin 4) (a : Fin 3)
    (ha : ¬ planeAxis (facePlane f) a) :
    faceBase f a = vertexCoord (tail (faceSide f i)) a := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases a
  all_goals first
    | exact (ha ⟨0,rfl⟩).elim
    | exact (ha ⟨1,rfl⟩).elim
    | (fin_cases i <;> rfl)

lemma common_face_unique (e e' : Edge n) (hne : edgeAxis e ≠ edgeAxis e')
    {f g : Face n} (hf : cycle f e ≠ 0) (hf' : cycle f e' ≠ 0)
    (hg : cycle g e ≠ 0) (hg' : cycle g e' ≠ 0) : f = g := by
  obtain ⟨i,hi⟩ := support_cycle f e hf
  obtain ⟨j,hj⟩ := support_cycle f e' hf'
  obtain ⟨k,hk⟩ := support_cycle g e hg
  obtain ⟨l,hl⟩ := support_cycle g e' hg'
  have ha : planeAxis (facePlane f) (edgeAxis e) := hi ▸ side_axis_in_plane f i
  have hb : planeAxis (facePlane f) (edgeAxis e') := hj ▸ side_axis_in_plane f j
  have hc : planeAxis (facePlane g) (edgeAxis e) := hk ▸ side_axis_in_plane g k
  have hd : planeAxis (facePlane g) (edgeAxis e') := hl ▸ side_axis_in_plane g l
  have hp := two_axes_plane _ _ _ _ hne ha hb hc hd
  apply faceBase_injective hp
  funext a
  rcases plane_axis_exhaust _ _ _ a hne ha hb with rfl|rfl|h
  · calc
      faceBase f (edgeAxis e) = vertexCoord (tail e) (edgeAxis e) := by
        simpa only [hi] using faceBase_on_axis f i
      _ = faceBase g (edgeAxis e) := by simpa only [hk] using (faceBase_on_axis g k).symm
  · calc
      faceBase f (edgeAxis e') = vertexCoord (tail e') (edgeAxis e') := by
        simpa only [hj] using faceBase_on_axis f j
      _ = faceBase g (edgeAxis e') := by simpa only [hl] using (faceBase_on_axis g l).symm
  · calc
      faceBase f a = vertexCoord (tail e) a := by simpa only [hi] using faceBase_outside f i a h
      _ = faceBase g a := by simpa only [hk] using (faceBase_outside g k a (hp ▸ h)).symm

end





noncomputable section

open Classical Support

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] lemma castSucc_ne_succ_self (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castSucc,Fin.val_succ] at hh
  omega

@[simp] lemma succ_ne_castSucc_self (i : Fin n) : i.succ ≠ i.castSucc :=
  (castSucc_ne_succ_self i).symm

lemma cycle_faceSide (f : Face n) (i : Fin 4) : cycle f (faceSide f i) ≠ 0 := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals simp [cycle,faceSide,ex,ey,ez]

lemma faceSide_injective_index (f : Face n) : Function.Injective (faceSide f) := by
  intro i j
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i <;> fin_cases j
  all_goals simp [faceSide,ex,ey,ez]

def AdjacentIndex (i j : Fin 4) : Prop := j = i+1 ∨ i = j+1

lemma adjacent_axis_ne (f : Face n) (i j : Fin 4) (h : AdjacentIndex i j) :
    edgeAxis (faceSide f i) ≠ edgeAxis (faceSide f j) := by
  rw [faceSide_axis,faceSide_axis]
  generalize facePlane f = p
  revert h
  unfold AdjacentIndex
  fin_cases p <;> decide +revert

lemma adjacent_common_vertex (f : Face n) (i j : Fin 4) (h : AdjacentIndex i j) :
    ∃ v, incident v (faceSide f i) ∧ incident v (faceSide f j) := by
  rcases h with rfl | rfl
  · refine ⟨faceCorner f (i+1),?_,?_⟩
    all_goals
      rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
      all_goals first | exact Or.inl rfl | exact Or.inr rfl
  · refine ⟨faceCorner f (j+1),?_,?_⟩
    all_goals
      rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases j
      all_goals first | exact Or.inl rfl | exact Or.inr rfl

def SideAdjacent (f : Face n) (i j : Fin 4)
    (s : LocalGroup (faceSide f i)) (t : LocalGroup (faceSide f j)) : Prop :=
  ∃ v, ∃ hi : incident v (faceSide f i), ∃ hj : incident v (faceSide f j),
    ∃ c : Configuration b v, c.state ⟨faceSide f i,hi⟩ = s ∧ c.state ⟨faceSide f j,hj⟩ = t

lemma sideAdjacent_iff (hn : 1 ≤ n) (f : Face n) (i j : Fin 4) (h : AdjacentIndex i j)
    (s : LocalGroup (faceSide f i)) (t : LocalGroup (faceSide f j)) :
    SideAdjacent (b := b) f i j s t ↔
      s.face ⟨f,cycle_faceSide f i⟩ = t.face ⟨f,cycle_faceSide f j⟩ := by
  constructor
  · rintro ⟨v,hi,hj,c,he,he'⟩
    simpa only [he,he'] using c.compatible ⟨_,hi⟩ ⟨_,hj⟩ f (cycle_faceSide f i) (cycle_faceSide f j)
  · intro hs
    obtain ⟨v,hi,hj⟩ := adjacent_common_vertex f i j h
    have he : (⟨faceSide f i,hi⟩ : IncidentEdges v) ≠ ⟨faceSide f j,hj⟩ := by
      intro hh
      exact adjacent_axis_ne f i j h (congrArg (edgeAxis ∘ Subtype.val) hh)
    obtain ⟨c,hc,hc'⟩ := exists_configuration_two (b := b) hn ⟨_,hi⟩ ⟨_,hj⟩ he s t (by
      intro g hgi hgj
      have hg := common_face_unique _ _ (adjacent_axis_ne f i j h)
        (cycle_faceSide f i) (cycle_faceSide f j) hgi hgj
      subst g
      exact hs)
    exact ⟨v,hi,hj,c,hc,hc'⟩

def SideMatch (f : Face n) (i j : Fin 4)
    (s : LocalGroup (faceSide f i)) (t : LocalGroup (faceSide f j)) : Prop :=
  if AdjacentIndex i j then SideAdjacent (b := b) f i j s t else
    ∃ q : LocalGroup (faceSide f (i+1)),
      SideAdjacent (b := b) f i (i+1) s q ∧ SideAdjacent (b := b) f j (i+1) t q

lemma index_next_adjacent (i : Fin 4) : AdjacentIndex i (i+1) := Or.inl rfl

lemma nonadjacent_next (i j : Fin 4) (h : ¬ AdjacentIndex i j) : AdjacentIndex j (i+1) := by
  revert i j
  unfold AdjacentIndex
  decide

lemma sideMatch_iff (hn : 1 ≤ n) (f : Face n) (i j : Fin 4)
    (s : LocalGroup (faceSide f i)) (t : LocalGroup (faceSide f j)) :
    SideMatch (b := b) f i j s t ↔
      s.face ⟨f,cycle_faceSide f i⟩ = t.face ⟨f,cycle_faceSide f j⟩ := by
  unfold SideMatch
  split_ifs with h
  · exact sideAdjacent_iff hn f i j h s t
  · simp only [sideAdjacent_iff hn f i (i+1) (index_next_adjacent i),
      sideAdjacent_iff hn f j (i+1) (nonadjacent_next i j h)]
    constructor
    · rintro ⟨q,hs,ht⟩
      exact hs.trans ht.symm
    · intro he
      refine ⟨⟨fun _ => s.face ⟨f,cycle_faceSide f i⟩,0⟩,rfl,he.symm⟩

end





noncomputable section

open Classical Support WitnessedChoice

variable {n : ℕ} {b : Vertex n → Scalar}

def actionPerm (g : BoxGroup n) : Equiv.Perm (Atom b) := MulAction.toPerm g

@[simp] lemma actionPerm_apply (g : BoxGroup n) (a : Atom b) : actionPerm g a = g • a := rfl

lemma actionPerm_fullAut (g : BoxGroup n) : actionPerm (b := b) g ∈ fullAut (atomInput b) := by
  intro r x y
  exact congrArg (fun p => @decide p (Classical.propDecidable p))
    (propext (AtomRelation.map_iff g r x y))

def edgeFootprint (F : Finset (Face n)) : Finset (Edge n) :=
  F.biUnion fun f => Finset.univ.image (faceSide f)

def vertexFootprint (F : Finset (Face n)) : Finset (Vertex n) :=
  F.biUnion fun f => Finset.univ.image (faceCorner f)

lemma edgeFootprint_card (F : Finset (Face n)) : (edgeFootprint F).card ≤ 4*F.card := by
  calc
    _ ≤ ∑ f ∈ F, (Finset.univ.image (faceSide f)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ F, 4 := Finset.sum_le_sum fun f _ => (Finset.card_image_le).trans (by simp)
    _ = _ := by simp [Nat.mul_comm]

lemma vertexFootprint_card (F : Finset (Face n)) : (vertexFootprint F).card ≤ 4*F.card := by
  calc
    _ ≤ ∑ f ∈ F, (Finset.univ.image (faceCorner f)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ F, 4 := Finset.sum_le_sum fun f _ => (Finset.card_image_le).trans (by simp)
    _ = _ := by simp [Nat.mul_comm]

lemma mem_edgeFootprint {F : Finset (Face n)} {f : Face n} (hf : f ∈ F)
    {e : Edge n} (he : cycle f e ≠ 0) : e ∈ edgeFootprint F := by
  obtain ⟨i,hi⟩ := support_cycle f e he
  exact Finset.mem_biUnion.mpr ⟨f,hf,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩⟩

lemma mem_vertexFootprint {F : Finset (Face n)} {f : Face n} (hf : f ∈ F)
    {v : Vertex n} (e : IncidentEdges v) (he : cycle f e.val ≠ 0) : v ∈ vertexFootprint F := by
  obtain ⟨i,hi⟩ := support_cycle f e.val he
  obtain ⟨j,hj⟩ := faceSide_endpoints f i v (hi ▸ e.property)
  exact Finset.mem_biUnion.mpr ⟨f,hf,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩⟩

def edgeBlockSet (b : Vertex n → Scalar) (e : Edge n) : Finset (Atom b) :=
  Finset.univ.image (fun s : LocalGroup e => .inl ⟨e,s⟩)

def vertexBlockSet (b : Vertex n → Scalar) (v : Vertex n) : Finset (Atom b) :=
  Finset.univ.image (fun s : Configuration b v => .inr ⟨v,s⟩)

def affectedAtoms (b : Vertex n → Scalar) (E : Finset (Edge n)) (V : Finset (Vertex n)) : Finset (Atom b) :=
  (E.biUnion (edgeBlockSet b)) ∪ (V.biUnion (vertexBlockSet b))

lemma affectedAtoms_card_le (hn : 1 ≤ n) (E : Finset (Edge n)) (V : Finset (Vertex n)) :
    (affectedAtoms b E V).card ≤ E.card*3^9 + V.card*3^29 := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ e ∈ E, (edgeBlockSet b e).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ E, 3^9 := Finset.sum_le_sum fun e _ =>
          Finset.card_image_le.trans (by simpa using localGroup_card_le_upper e)
      _ = _ := by simp
  · calc
      _ ≤ ∑ v ∈ V, (vertexBlockSet b v).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ V, 3^29 := Finset.sum_le_sum fun v _ =>
          Finset.card_image_le.trans (by simpa using configuration_card_le_upper hn b v)
      _ = _ := by simp

lemma faceTranslation_moved_subset (a : Face n → Plane) (F : Finset (Face n))
    (ha : ∀ f, a f ≠ 0 → f ∈ F) :
    (Finset.univ.filter fun x : Atom b => actionPerm (⟨a,0⟩ : BoxGroup n) x ≠ x) ⊆
      affectedAtoms b (edgeFootprint F) (vertexFootprint F) := by
  intro x hx
  have hmove := (Finset.mem_filter.mp hx).2
  rcases x with ⟨e,s⟩ | ⟨v,s⟩
  · have he : e ∈ edgeFootprint F := by
      by_contra hn
      have hr : restrictGroup e (⟨a,0⟩ : BoxGroup n) = 1 := by
        apply Support.H.ext
        · funext f
          by_contra h
          exact hn (mem_edgeFootprint (ha f.val h) f.property)
        · rfl
      apply hmove
      change (Sum.inl ⟨e,restrictGroup e (⟨a,0⟩ : BoxGroup n) * s⟩ : Atom b) = _
      simp only [hr,one_mul]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨e,he,Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩⟩)
  · have hv : v ∈ vertexFootprint F := by
      by_contra hn
      have hr (e : IncidentEdges v) : restrictGroup e.val (⟨a,0⟩ : BoxGroup n) = 1 := by
        apply Support.H.ext
        · funext f
          by_contra h
          exact hn (mem_vertexFootprint (ha f.val h) e f.property)
        · rfl
      apply hmove
      change (Sum.inr ⟨v,actConfiguration (⟨a,0⟩ : BoxGroup n) s⟩ : Atom b) = _
      congr 1
      congr 1
      apply Configuration.ext
      intro e
      change restrictGroup e.val (⟨a,0⟩ : BoxGroup n) * s.state e = s.state e
      rw [hr e,one_mul]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨v,hv,Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩⟩)

lemma faceTranslation_in_localPool_bound (B : ℕ) (hB : 16*(3^9+3^29) ≤ B) (hn : 1 ≤ n) (a : Face n → Plane)
    (F : Finset (Face n)) (hF : F.card ≤ 4) (ha : ∀ f, a f ≠ 0 → f ∈ F) :
    RelationPools.graph (actionPerm (b := b) (⟨a,0⟩ : BoxGroup n)) ∈
      RelationPools.localPool B := by
  apply RelationPools.localPool_contains
  calc
    _ ≤ (affectedAtoms b (edgeFootprint F) (vertexFootprint F)).card :=
      Finset.card_le_card (faceTranslation_moved_subset a F ha)
    _ ≤ (edgeFootprint F).card*3^9 + (vertexFootprint F).card*3^29 := affectedAtoms_card_le hn _ _
    _ ≤ 16*3^9 + 16*3^29 := Nat.add_le_add
        (Nat.mul_le_mul_right _ ((edgeFootprint_card F).trans (by omega)))
        (Nat.mul_le_mul_right _ ((vertexFootprint_card F).trans (by omega)))
    _ = 16*(3^9+3^29) := by rw [Nat.mul_add]
    _ ≤ B := hB

lemma faceTranslation_in_localPool (hn : 1 ≤ n) (a : Face n → Plane)
    (F : Finset (Face n)) (hF : F.card ≤ 4) (ha : ∀ f, a f ≠ 0 → f ∈ F) :
    RelationPools.graph (actionPerm (b := b) (⟨a,0⟩ : BoxGroup n)) ∈
      RelationPools.localPool RelationPools.localBound :=
  faceTranslation_in_localPool_bound RelationPools.localBound (by rw [RelationPools.localBound]) hn a F hF ha

end





noncomputable section

open Classical Support WitnessedChoice

variable {n : ℕ} {b : Vertex n → Scalar}

def AcceptsFaces (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) (s : LocalGroup e) : Prop :=
  ∀ t ∈ x, ∀ f : Face n, ∀ he : cycle f e ≠ 0, ∀ ht : cycle f t.1 ≠ 0,
    s.face ⟨f,he⟩ = t.2.face ⟨f,ht⟩

def faceDelta (e : Edge n) (s t : LocalGroup e) (f : Face n) : Plane :=
  if h : cycle f e ≠ 0 then t.face ⟨f,h⟩ - s.face ⟨f,h⟩ else 0

lemma faceDelta_support (e : Edge n) (s t : LocalGroup e) :
    ∀ f, faceDelta e s t f ≠ 0 → f ∈ Finset.univ.filter (fun f => cycle f e ≠ 0) := by
  intro f hf
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
    (show cycle f e ≠ 0 from fun h => hf (by simp [faceDelta,h]))

lemma faceDelta_zero_on_past {x : Finset (Σ e : Edge n, LocalGroup e)}
    {e : Edge n} {s t : LocalGroup e} (hs : AcceptsFaces x e s) (ht : AcceptsFaces x e t)
    {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x) (f : EdgeFaces r.1) :
    faceDelta e s t f.val = 0 := by
  by_cases he : cycle f.val e ≠ 0
  · rw [faceDelta,dite_eq_left he,ht r hr f.val he f.property,hs r hr f.val he f.property,sub_self]
  · simp only [faceDelta,dite_eq_right he]

lemma faceDelta_fix_past {x : Finset (Σ e : Edge n, LocalGroup e)}
    {e : Edge n} {s t : LocalGroup e} (hs : AcceptsFaces x e s) (ht : AcceptsFaces x e t)
    {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x) :
    actionPerm (b := b) (⟨faceDelta e s t,0⟩ : BoxGroup n) (.inl r) = .inl r := by
  have hg : restrictGroup r.1 (⟨faceDelta e s t,0⟩ : BoxGroup n) = 1 := by
    apply Support.H.ext
    · funext f
      exact faceDelta_zero_on_past hs ht hr f
    · rfl
  change (Sum.inl ⟨r.1,restrictGroup r.1 (⟨faceDelta e s t,0⟩ : BoxGroup n) * r.2⟩ : Atom b) = _
  rw [hg,one_mul]

lemma faceDelta_hits_vectors (e : Edge n) (s t : LocalGroup e) :
    (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).face = t.face := by
  funext f
  change faceDelta e s t f.val + s.face f = t.face f
  rw [faceDelta,dite_eq_left f.property,sub_add_cancel]

lemma faceDelta_in_localPool (hn : 1 ≤ n) (e : Edge n) (s t : LocalGroup e) :
    RelationPools.graph (actionPerm (b := b) (⟨faceDelta e s t,0⟩ : BoxGroup n)) ∈
      RelationPools.localPool RelationPools.localBound := by
  have hF : (Finset.univ.filter (fun f => cycle f e ≠ 0)).card ≤ 4 := by
    simpa only [← Fintype.card_subtype] using edgeFaces_card_le_four e
  exact faceTranslation_in_localPool hn _ _ hF (faceDelta_support e s t)

lemma central_after_local (e : Edge n) (s t : LocalGroup e) (k : FlowSpace n)
    (hk : k.val e = t.flow - (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).flow) :
    actionPerm (b := b) (⟨0,k⟩ : BoxGroup n)
      (actionPerm (⟨faceDelta e s t,0⟩ : BoxGroup n) (.inl ⟨e,s⟩)) = .inl ⟨e,t⟩ := by
  change (Sum.inl ⟨e, restrictGroup e (⟨0,k⟩ : BoxGroup n) *
    (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s)⟩ : Atom b) = _
  congr 1
  congr 1
  apply Support.H.ext
  · funext f
    change 0 + (faceDelta e s t f.val + s.face f) = t.face f
    rw [zero_add]
    exact congrFun (faceDelta_hits_vectors e s t) f
  · change k.val e + (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).flow +
        correction (localCycle e) 0 (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).face = t.flow
    rw [correction_zero_left,add_zero,hk,sub_add_cancel]

lemma central_fix_edge (k : FlowSpace n) (e : Edge n) (s : LocalGroup e) (hk : k.val e = 0) :
    actionPerm (b := b) (⟨0,k⟩ : BoxGroup n) (.inl ⟨e,s⟩) = .inl ⟨e,s⟩ := by
  have hh : restrictGroup e (⟨0,k⟩ : BoxGroup n) = 1 := by
    apply Support.H.ext
    · rfl
    · exact hk
  change (Sum.inl ⟨e,restrictGroup e (⟨0,k⟩ : BoxGroup n) * s⟩ : Atom b) = _
  rw [hh,one_mul]

end





noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

lemma path_walk_lower {u v : Fin (n+1)} (w : (pathGraph (n+1)).Walk u v) :
    Nat.dist u.val v.val ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab w ih =>
    have ha := pathGraph_adj.mp hab
    simp only [Walk.length_cons]
    simp only [Nat.dist] at ih ⊢
    omega

lemma path_walk_upper_le (k : ℕ) : ∀ u v : Fin (n+1), u.val ≤ v.val → v.val-u.val = k →
    ∃ w : (pathGraph (n+1)).Walk u v, w.length = k := by
  induction k with
  | zero =>
    intro u v huv he
    have h : u = v := Fin.ext (by omega)
    subst v
    exact ⟨.nil,rfl⟩
  | succ k ih =>
    intro u v huv he
    let u' : Fin (n+1) := ⟨u.val+1,by omega⟩
    have hadj : (pathGraph (n+1)).Adj u u' := pathGraph_adj.mpr (Or.inl rfl)
    obtain ⟨w,hw⟩ := ih u' v (by dsimp [u']; omega) (by dsimp [u']; omega)
    exact ⟨.cons hadj w,by simp only [Walk.length_cons,hw]⟩

lemma path_dist (u v : Fin (n+1)) : (pathGraph (n+1)).dist u v = Nat.dist u.val v.val := by
  apply Nat.le_antisymm
  · by_cases h : u.val ≤ v.val
    · obtain ⟨w,hw⟩ := path_walk_upper_le (v.val-u.val) u v h rfl
      rw [Nat.dist_eq_sub_of_le h,← hw]
      exact dist_le w
    · have h' : v.val ≤ u.val := by omega
      obtain ⟨w,hw⟩ := path_walk_upper_le (u.val-v.val) v u h' rfl
      rw [Nat.dist_eq_sub_of_le_right h',← hw,← w.length_reverse]
      exact dist_le w.reverse
  · obtain ⟨w,hw⟩ := ((pathGraph_connected n).preconnected u v).exists_walk_length_eq_dist
    rw [← hw]
    exact path_walk_lower w

lemma path_edist (u v : Fin (n+1)) : (pathGraph (n+1)).edist u v = (Nat.dist u.val v.val : ℕ∞) := by
  rw [← ((pathGraph_connected n).preconnected u v).coe_dist_eq_edist,path_dist]

def boxGraph (n : ℕ) : SimpleGraph (Vertex n) :=
  (pathGraph (n+1)).boxProd ((pathGraph (n+1)).boxProd (pathGraph (n+1)))

lemma boxGraph_connected (n : ℕ) : (boxGraph n).Connected := by
  simp only [boxGraph,connected_boxProd,pathGraph_connected,and_self]

lemma boxGraph_dist (u v : Vertex n) : (boxGraph n).dist u v =
    Nat.dist u.1.val v.1.val + (Nat.dist u.2.1.val v.2.1.val + Nat.dist u.2.2.val v.2.2.val) := by
  have h := ((boxGraph_connected n).preconnected u v).coe_dist_eq_edist
  simp only [boxGraph,edist_boxProd,path_edist,← Nat.cast_add] at h
  exact_mod_cast h

lemma boxGraph_tail_head (e : Edge n) : (boxGraph n).Adj (tail e) (head e) := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp [boxGraph,boxProd_adj,pathGraph_adj,tail,head]

lemma boxGraph_adj_iff (u v : Vertex n) : (boxGraph n).Adj u v ↔
    ∃ e : Edge n, (u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e) := by
  constructor
  · intro h
    rcases u with ⟨i,j,k⟩
    rcases v with ⟨i',j',k'⟩
    simp only [boxGraph,boxProd_adj,pathGraph_adj,Prod.mk.injEq] at h
    rcases h with ⟨h,he⟩ | ⟨h,hi⟩
    · rcases he with ⟨rfl,rfl⟩
      rcases h with h | h
      · refine ⟨ex ⟨i.val,by omega⟩ j k,Or.inl ⟨?_,?_⟩⟩
        · rfl
        · apply Prod.ext
          · apply Fin.ext; exact h.symm
          · rfl
      · refine ⟨ex ⟨i'.val,by omega⟩ j k,Or.inr ⟨?_,?_⟩⟩
        · rfl
        · apply Prod.ext
          · apply Fin.ext; exact h.symm
          · rfl
    · subst i'
      rcases h with ⟨h,hk⟩ | ⟨h,hj⟩
      · subst k'
        rcases h with h | h
        · refine ⟨ey i ⟨j.val,by omega⟩ k,Or.inl ⟨?_,?_⟩⟩
          · rfl
          · simp only [ey,head,Prod.mk.injEq,true_and,and_true]
            exact Fin.ext h.symm
        · refine ⟨ey i ⟨j'.val,by omega⟩ k,Or.inr ⟨?_,?_⟩⟩
          · rfl
          · simp only [ey,head,Prod.mk.injEq,true_and,and_true]
            exact Fin.ext h.symm
      · subst j'
        rcases h with h | h
        · refine ⟨ez i j ⟨k.val,by omega⟩,Or.inl ⟨?_,?_⟩⟩
          · rfl
          · simp only [ez,head,Prod.mk.injEq,true_and]
            exact Fin.ext h.symm
        · refine ⟨ez i j ⟨k'.val,by omega⟩,Or.inr ⟨?_,?_⟩⟩
          · rfl
          · simp only [ez,head,Prod.mk.injEq,true_and]
            exact Fin.ext h.symm
  · rintro ⟨e,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    · exact boxGraph_tail_head e
    · exact (boxGraph_tail_head e).symm

def cornerAnchors (n : ℕ) : Fin 4 → Vertex n :=
  ![(0,0,0),(Fin.last n,0,0),(0,Fin.last n,0),(0,0,Fin.last n)]

lemma cornerAnchors_resolve (u v : Vertex n)
    (h : ∀ i : Fin 4, (boxGraph n).dist (cornerAnchors n i) u =
      (boxGraph n).dist (cornerAnchors n i) v) : u = v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [boxGraph_dist] at h0 h1 h2 h3
  simp only [cornerAnchors, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_last,
    Nat.dist_zero_left] at h0 h1 h2 h3
  simp only [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ u.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ u.2.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ u.2.2.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ v.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ v.2.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ v.2.2.isLt)] at h1 h2 h3
  apply Prod.ext
  · apply Fin.ext; omega
  · apply Prod.ext
    · apply Fin.ext; omega
    · apply Fin.ext; omega

end

end WitnessedSeparation.Grid

end OAI
