import OAI.Combinatorics.ParityLifts.GraphIso

namespace OAI

namespace ParityWL.Complexity

abbrev ChoiceData (t : ℕ) := (Fin t → List (Fin t → ℕ)) × (Fin t → Fin t → ℕ)

def ChoiceData.entry {t : ℕ} (D : ChoiceData t) (i : Fin t) (d : ℕ) (j : Fin t) : ℕ :=
  (D.1 i)[d]?.getD (fun _ => 0) j

def ChoiceData.pairBound {t : ℕ} (D : ChoiceData t) (i j : Fin t) : ℕ :=
  D.2 (min i j) (max i j)

def ChoiceData.label {t : ℕ} (D : ChoiceData t) (i : Fin t) (d : ℕ) (j : Fin t) : ℕ :=
  min (D.entry i d j) (D.pairBound i j)

lemma ChoiceData.pairBound_symm {t : ℕ} (D : ChoiceData t) (i j : Fin t) :
    D.pairBound i j = D.pairBound j i := by simp [pairBound, min_comm, max_comm]

noncomputable def ChoiceData.system {t : ℕ} (D : ChoiceData t) : ChoiceSystem t where
  Domain i := Fin (D.1 i).length
  domainFintype _ := inferInstance
  Label p := Fin (D.2 p.1.1 p.1.2+1)
  labelFintype _ := inferInstance
  leftLabel p d := ⟨D.label p.1.1 d.val p.1.2, by
    change min (D.entry p.1.1 d.val p.1.2) (D.pairBound p.1.1 p.1.2) < _
    rw [pairBound, min_eq_left p.2.le, max_eq_right p.2.le]
    exact Nat.lt_succ_of_le (min_le_right _ _)⟩
  rightLabel p d := ⟨D.label p.1.2 d.val p.1.1, by
    change min (D.entry p.1.2 d.val p.1.1) (D.pairBound p.1.2 p.1.1) < _
    rw [pairBound, min_eq_right p.2.le, max_eq_left p.2.le]
    exact Nat.lt_succ_of_le (min_le_right _ _)⟩

def ChoiceData.roleSize {t : ℕ} (D : ChoiceData t) : TemplateVertex t → ℕ
  | .inl i => (D.1 i).length
  | .inr h => D.2 h.1.1.1.1 h.1.1.1.2+1

def ChoiceData.vertex {t : ℕ} (D : ChoiceData t) : (a : TemplateVertex t) →
    Fin (D.roleSize a) → BaseVertex D.system
  | .inl i, d => .inl ⟨i,d⟩
  | .inr h, q => .inr ⟨h,q⟩

@[simp] lemma ChoiceData.vertex_type {t : ℕ} (D : ChoiceData t) (a : TemplateVertex t)
    (d : Fin (D.roleSize a)) : baseType (D.vertex a d) = a := by cases a <;> rfl

def ChoiceData.baseIndex {t : ℕ} (D : ChoiceData t) : BaseVertex D.system → ℕ
  | .inl x => x.2.val
  | .inr x => x.2.val

@[simp] lemma ChoiceData.vertex_index {t : ℕ} (D : ChoiceData t) (a : TemplateVertex t)
    (d : Fin (D.roleSize a)) : D.baseIndex (D.vertex a d) = d.val := by cases a <;> rfl

def ChoiceData.helperTest {t : ℕ} (D : ChoiceData t) (h : Helper t) (q : ℕ) (i : Fin t) (d : ℕ) : Bool :=
  if i=h.1.1.1.1 then decide (D.label i d h.1.1.1.2 = q)
  else if i=h.1.1.1.2 then decide (D.label i d h.1.1.1.1 = q)
  else decide (i=h.1.2)

def ChoiceData.baseTest {t : ℕ} (D : ChoiceData t) : TemplateVertex t → ℕ → TemplateVertex t → ℕ → Bool
  | .inl i, d, .inl j, e => decide (i≠j) && decide (D.label i d j = D.label j e i)
  | .inl i, d, .inr h, q => D.helperTest h q i d
  | .inr h, q, .inl i, d => D.helperTest h q i d
  | .inr _, _, .inr _, _ => false

lemma ChoiceData.baseTest_symm {t : ℕ} (D : ChoiceData t) (a b : TemplateVertex t) (d e : ℕ) :
    D.baseTest a d b e = D.baseTest b e a d := by
  cases a <;> cases b <;> simp [baseTest, eq_comm]

lemma ChoiceData.baseTest_arc {t : ℕ} (D : ChoiceData t) {x y : BaseVertex D.system}
    (h : BaseArc D.system x y) : D.baseTest (baseType x) (D.baseIndex x) (baseType y) (D.baseIndex y) = true := by
  cases h with
  | main p d e h =>
    have he := congrArg Fin.val h
    simp only [ChoiceData.system] at he
    simp [baseType, baseIndex, baseTest, ne_of_lt p.2, he]
  | left h d => simp [baseType, baseIndex, baseTest, helperTest, ChoiceData.system]
  | right h d =>
    simp [baseType, baseIndex, baseTest, helperTest, ChoiceData.system, ne_of_gt h.1.1.2]
  | third h q d =>
    simp [baseType, baseIndex, baseTest, helperTest, h.2.1, h.2.2]

lemma ChoiceData.baseTest_adj {t : ℕ} (D : ChoiceData t) {x y : BaseVertex D.system}
    (h : (baseGraph D.system).Adj x y) :
    D.baseTest (baseType x) (D.baseIndex x) (baseType y) (D.baseIndex y) = true := by
  rcases h.2 with h | h
  · exact D.baseTest_arc h
  · rw [D.baseTest_symm]
    exact D.baseTest_arc h

lemma ChoiceData.helperTest_arc {t : ℕ} (D : ChoiceData t) (h : Helper t)
    (q : D.system.Label h.1.1) (i : Fin t) (d : D.system.Domain i)
    (he : D.helperTest h q.val i d.val = true) :
    BaseArc D.system (.inr ⟨h,q⟩) (.inl ⟨i,d⟩) := by
  by_cases hi : i=h.1.1.1.1
  · subst i
    have hq : D.system.leftLabel h.1.1 d=q := by
      apply Fin.ext
      simpa [helperTest, ChoiceData.system] using he
    rw [← hq]
    exact BaseArc.left h d
  · by_cases hj : i=h.1.1.1.2
    · subst i
      have hq : D.system.rightLabel h.1.1 d=q := by
        apply Fin.ext
        simpa [helperTest, hi, ChoiceData.system] using he
      rw [← hq]
      exact BaseArc.right h d
    · have hk : i=h.1.2 := by simpa [helperTest, hi, hj] using he
      subst i
      exact BaseArc.third h q d

lemma ChoiceData.adj_of_baseTest {t : ℕ} (D : ChoiceData t) (x y : BaseVertex D.system)
    (hr : D.baseTest (baseType x) (D.baseIndex x) (baseType y) (D.baseIndex y) = true) :
    (baseGraph D.system).Adj x y := by
  rcases x with ⟨i,d⟩ | ⟨h,q⟩ <;> rcases y with ⟨j,e⟩ | ⟨g,r⟩
  · have he : i≠j ∧ D.label i d.val j=D.label j e.val i := by simpa [baseTest, baseType, baseIndex] using hr
    have hne : (.inl ⟨i,d⟩ : BaseVertex D.system) ≠ .inl ⟨j,e⟩ := by
      intro hh
      have hi := congrArg baseType hh
      exact he.1 (Sum.inl.inj hi)
    refine ⟨hne, ?_⟩
    rcases lt_or_gt_of_ne he.1 with hij | hji
    · exact Or.inl (BaseArc.main ⟨(i,j),hij⟩ d e (Fin.ext he.2))
    · exact Or.inr (BaseArc.main ⟨(j,i),hji⟩ e d (Fin.ext he.2.symm))
  · exact ⟨by simp, Or.inr (D.helperTest_arc g r i d hr)⟩
  · exact ⟨by simp, Or.inl (D.helperTest_arc h q j e hr)⟩
  · simp [baseType, baseIndex, baseTest] at hr

lemma ChoiceData.baseTest_iff {t : ℕ} (D : ChoiceData t) (x y : BaseVertex D.system) :
    D.baseTest (baseType x) (D.baseIndex x) (baseType y) (D.baseIndex y) = true ↔
      (baseGraph D.system).Adj x y :=
  ⟨D.adj_of_baseTest x y, D.baseTest_adj⟩

end ParityWL.Complexity

namespace ParityWL.Complexity

def enumPairs {m : ℕ} (n : Fin m → ℕ) : List (Fin m × ℕ) :=
  (List.ofFn id).flatMap (fun z => (List.range (n z)).map (z,·))

@[simp] lemma mem_enumPairs {m : ℕ} (n : Fin m → ℕ) (z : Fin m) (d : ℕ) :
    (z,d) ∈ enumPairs n ↔ d<n z := by
  simp [enumPairs]

lemma nodup_enumPairs {m : ℕ} (n : Fin m → ℕ) : (enumPairs n).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro z _
    exact (List.nodup_range).map (fun a b h => congrArg Prod.snd h)
  · apply (List.nodup_ofFn.mpr (Function.injective_id)).imp
    intro z w h x hx hy
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e, _, he⟩ := List.mem_map.mp hy
    exact h (congrArg Prod.fst he).symm

def enumPairsEquiv {m : ℕ} (n : Fin m → ℕ) : Fin (enumPairs n).length ≃ (z : Fin m) × Fin (n z) :=
  (List.Nodup.getEquiv _ (nodup_enumPairs n)).trans {
    toFun := fun x => ⟨x.val.1,⟨x.val.2,(mem_enumPairs n _ _).mp x.property⟩⟩
    invFun := fun x => ⟨(x.1,x.2.val),(mem_enumPairs n _ _).mpr x.2.isLt⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }

@[simp] lemma enumPairsEquiv_fst {m : ℕ} (n : Fin m → ℕ) (i : Fin (enumPairs n).length) :
    (enumPairsEquiv n i).1 = ((enumPairs n).get i).1 := rfl
@[simp] lemma enumPairsEquiv_snd {m : ℕ} (n : Fin m → ℕ) (i : Fin (enumPairs n).length) :
    (enumPairsEquiv n i).2.val = ((enumPairs n).get i).2 := rfl

abbrev GlobalTag (t : ℕ) (b : TemplateVertex t → Bit) := (a : TemplateVertex t) × Tag (template t) b a

abbrev TagIndex (t : ℕ) (b : TemplateVertex t → Bit) := Fin (Fintype.card (GlobalTag t b))

noncomputable def tagDecode (t : ℕ) (b : TemplateVertex t → Bit) : TagIndex t b ≃ GlobalTag t b :=
  (Fintype.equivFin (GlobalTag t b)).symm

noncomputable def ChoiceData.globalLiftEquiv {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit) :
    ((z : GlobalTag t b) × Fin (D.roleSize z.1)) ≃
      LiftVertex (template t) (baseGraph D.system) (baseProjection D.system) b where
  toFun x := match x with
    | ⟨⟨.inl i,z⟩,d⟩ => ⟨.inl ⟨i,d⟩,z⟩
    | ⟨⟨.inr h,z⟩,q⟩ => ⟨.inr ⟨h,q⟩,z⟩
  invFun x := match x with
    | ⟨.inl ⟨i,d⟩,z⟩ => ⟨⟨.inl i,z⟩,d⟩
    | ⟨.inr ⟨h,q⟩,z⟩ => ⟨⟨.inr h,z⟩,q⟩
  left_inv := by rintro ⟨⟨i,z⟩,d⟩; cases i <;> rfl
  right_inv := by rintro ⟨x,z⟩; rcases x with ⟨i,d⟩ | ⟨h,q⟩ <;> rfl

noncomputable def ChoiceData.indexSize {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit)
    (z : TagIndex t b) : ℕ := D.roleSize (tagDecode t b z).1

noncomputable def ChoiceData.vertices {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit) :
    List (TagIndex t b × ℕ) := enumPairs (D.indexSize b)

noncomputable def ChoiceData.vertexEquiv {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit) :
    Fin (D.vertices b).length ≃ LiftVertex (template t) (baseGraph D.system) (baseProjection D.system) b :=
  (enumPairsEquiv (D.indexSize b)).trans
    ((Equiv.sigmaCongrLeft (β := fun z : GlobalTag t b => Fin (D.roleSize z.1)) (tagDecode t b)).trans
      (D.globalLiftEquiv b))

noncomputable def ChoiceData.indexedGraph {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit) :
    SimpleGraph (Fin (D.vertices b).length) :=
  (liftGraph (template t) (baseGraph D.system) (baseProjection D.system) b).comap (D.vertexEquiv b)

noncomputable def ChoiceData.indexedIso {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit) :
    D.indexedGraph b ≃g liftGraph (template t) (baseGraph D.system) (baseProjection D.system) b :=
  SimpleGraph.Iso.comap (D.vertexEquiv b) _

noncomputable def tagTest {t : ℕ} (b : TemplateVertex t → Bit) (x y : GlobalTag t b) : Bool := by
  classical
  exact if h : (template t).Adj x.1 y.1 then decide (x.2.1 ⟨y.1,h⟩ = y.2.1 ⟨x.1,h.symm⟩) else false

noncomputable def ChoiceData.edgeTest {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit)
    (x y : TagIndex t b × ℕ) : Bool :=
  D.baseTest (tagDecode t b x.1).1 x.2 (tagDecode t b y.1).1 y.2 &&
    tagTest b (tagDecode t b x.1) (tagDecode t b y.1)

lemma ChoiceData.lift_arc_iff {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit)
    (x y : LiftVertex (template t) (baseGraph D.system) (baseProjection D.system) b) :
    (liftGraph (template t) (baseGraph D.system) (baseProjection D.system) b).Adj x y ↔
    D.baseTest (baseType x.1) (D.baseIndex x.1) (baseType y.1) (D.baseIndex y.1) = true ∧
      tagTest b ⟨baseType x.1,x.2⟩ ⟨baseType y.1,y.2⟩ = true := by
  classical
  rw [D.baseTest_iff]
  constructor
  · rintro ⟨h,he⟩
    refine ⟨h, ?_⟩
    have ht : (template t).Adj (baseType x.1) (baseType y.1) :=
      (baseProjection D.system).map_adj h
    simp only [tagTest, ht, ↓reduceDIte, decide_eq_true_eq]
    exact he
  · rintro ⟨h,he⟩
    refine ⟨h, ?_⟩
    have ht : (template t).Adj (baseType x.1) (baseType y.1) :=
      (baseProjection D.system).map_adj h
    simp only [tagTest, ht, ↓reduceDIte, decide_eq_true_eq] at he
    exact he

lemma ChoiceData.globalLift_raw {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit)
    (x : (z : GlobalTag t b) × Fin (D.roleSize z.1)) :
    (⟨baseType (D.globalLiftEquiv b x).1,(D.globalLiftEquiv b x).2⟩ : GlobalTag t b) = x.1 ∧
      D.baseIndex (D.globalLiftEquiv b x).1=x.2.val := by
  rcases x with ⟨⟨a,z⟩,d⟩
  cases a <;> exact ⟨rfl,rfl⟩

lemma ChoiceData.vertexEquiv_raw {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit)
    (i : Fin (D.vertices b).length) :
    (⟨baseType (D.vertexEquiv b i).1,(D.vertexEquiv b i).2⟩ : GlobalTag t b) =
      tagDecode t b ((D.vertices b).get i).1 ∧
      D.baseIndex (D.vertexEquiv b i).1=((D.vertices b).get i).2 := by
  exact D.globalLift_raw b _

lemma ChoiceData.indexed_adj {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit)
    (i j : Fin (D.vertices b).length) :
    (D.indexedGraph b).Adj i j ↔ D.edgeTest b ((D.vertices b).get i) ((D.vertices b).get j) = true := by
  change (liftGraph (template t) (baseGraph D.system) (baseProjection D.system) b).Adj _ _ ↔ _
  rw [D.lift_arc_iff]
  obtain ⟨hx,hxi⟩ := D.vertexEquiv_raw b i
  obtain ⟨hy,hyi⟩ := D.vertexEquiv_raw b j
  have hx' : baseType (D.vertexEquiv b i).1 = (tagDecode t b ((D.vertices b).get i).1).1 := congrArg Sigma.fst hx
  have hy' : baseType (D.vertexEquiv b j).1 = (tagDecode t b ((D.vertices b).get j).1).1 := congrArg Sigma.fst hy
  simp only [edgeTest, Bool.and_eq_true, hx, hy, hx', hy', hxi, hyi]

end ParityWL.Complexity

end OAI
