import OAI.Combinatorics.ParityLifts.BitTables

namespace OAI

namespace ParityWL.Complexity

def PolyProgram.finite2 {n m : ℕ} {α : Type} [TreeCodec α]
    (f : Fin n → Fin m → α) : PolyProgram (Fin n × Fin m) α (fun x => f x.1 x.2) :=
  .expr (TExpr.caseFin n TExpr.input.left (fun i =>
    TExpr.caseFin m TExpr.input.right (fun j => .const (treeEncode (f i j))) .nil) .nil) (by
      rintro ⟨i,j⟩
      rw [TExpr.caseFin_eval i _ _ _ _ (by rfl), TExpr.caseFin_eval j _ _ _ _ (by rfl)]
      rfl)

def PolyProgram.choiceEntry (t : ℕ) :
    PolyProgram (ChoiceData t × (Fin t × (ℕ × Fin t))) ℕ
      (fun x => x.1.entry x.2.1 x.2.2.1 x.2.2.2) := by
  let row : PolyProgram (ChoiceData t × (Fin t × (ℕ × Fin t))) (Fin t × (Fin t → List (Fin t → ℕ)))
      (fun x => (x.2.1,x.1.1)) := .expr (.pair TExpr.input.right.left TExpr.input.left.left) (by intro x; rfl)
  let R := row.comp (PolyProgram.evalFin t (List (Fin t → ℕ)))
  let idx : PolyProgram (ChoiceData t × (Fin t × (ℕ × Fin t))) ℕ (fun x => x.2.2.1) :=
    .expr TExpr.input.right.right.left (by intro x; rfl)
  let V := (idx.pair R).comp (PolyProgram.getD (Fin t → ℕ) (fun _ => 0))
  let col : PolyProgram (ChoiceData t × (Fin t × (ℕ × Fin t))) (Fin t) (fun x => x.2.2.2) :=
    .expr TExpr.input.right.right.right (by intro x; rfl)
  exact (col.pair V).comp (PolyProgram.evalFin t ℕ)

def PolyProgram.choiceBound (t : ℕ) :
    PolyProgram (ChoiceData t × (Fin t × Fin t)) ℕ (fun x => x.1.pairBound x.2.1 x.2.2) := by
  let I := (PolyProgram.snd (ChoiceData t) (Fin t × Fin t)).comp
    (PolyProgram.finite2 (fun i j : Fin t => (min i j,max i j)))
  let T := (PolyProgram.fst (ChoiceData t) (Fin t × Fin t)).comp
    (PolyProgram.snd (Fin t → List (Fin t → ℕ)) (Fin t → Fin t → ℕ))
  let R := ((I.comp (PolyProgram.fst (Fin t) (Fin t))).pair T).comp
    (PolyProgram.evalFin t (Fin t → ℕ))
  exact ((I.comp (PolyProgram.snd (Fin t) (Fin t))).pair R).comp (PolyProgram.evalFin t ℕ)

def PolyProgram.choiceLabel (t : ℕ) :
    PolyProgram (ChoiceData t × (Fin t × (ℕ × Fin t))) ℕ
      (fun x => x.1.label x.2.1 x.2.2.1 x.2.2.2) := by
  let Q : PolyProgram (ChoiceData t × (Fin t × (ℕ × Fin t))) (ChoiceData t × (Fin t × Fin t))
      (fun x => (x.1,(x.2.1,x.2.2.2))) :=
    .expr (.pair TExpr.input.left (.pair TExpr.input.right.left TExpr.input.right.right.right)) (by intro x; rfl)
  exact ((PolyProgram.choiceEntry t).pair (Q.comp (PolyProgram.choiceBound t))).comp PolyProgram.natMin

/-- The finite role data is compiled into finite control, independent of table size. -/
noncomputable def roleCode {t : ℕ} [NeZero t] : TemplateVertex t → Bool × (Fin t × Fin t)
  | .inl i => (false,(i,i))
  | .inr h => (true,(h.1.1.1.1,h.1.1.1.2))

noncomputable def PolyProgram.indexSize (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    PolyProgram (TagIndex t b × ChoiceData t) ℕ (fun x => x.2.indexSize b x.1) := by
  let R := (PolyProgram.fst (TagIndex t b) (ChoiceData t)).comp
    (PolyProgram.finite (fun z => roleCode (tagDecode t b z).1))
  let I := R.comp (PolyProgram.snd Bool (Fin t × Fin t))
  let D := PolyProgram.snd (TagIndex t b) (ChoiceData t)
  let Ds := D.comp (PolyProgram.fst (Fin t → List (Fin t → ℕ)) (Fin t → Fin t → ℕ))
  let row := ((I.comp (PolyProgram.fst (Fin t) (Fin t))).pair Ds).comp
    (PolyProgram.evalFin t (List (Fin t → ℕ))) |>.comp (PolyProgram.length (Fin t → ℕ))
  let Bs := D.comp (PolyProgram.snd (Fin t → List (Fin t → ℕ)) (Fin t → Fin t → ℕ))
  let brow := ((I.comp (PolyProgram.fst (Fin t) (Fin t))).pair Bs).comp (PolyProgram.evalFin t (Fin t → ℕ))
  let val := ((I.comp (PolyProgram.snd (Fin t) (Fin t))).pair brow).comp (PolyProgram.evalFin t ℕ) |>.comp PolyProgram.natSucc
  refine ((R.comp (PolyProgram.fst Bool (Fin t × Fin t))).ite val row).congr ?_
  intro x
  change (if (roleCode (tagDecode t b x.1).1).1 then _ else _) = _
  rcases h : (tagDecode t b x.1).1 with i | h
  · simp [roleCode, ChoiceData.indexSize, ChoiceData.roleSize, h]
  · simp [roleCode, ChoiceData.indexSize, ChoiceData.roleSize, h]

noncomputable def PolyProgram.vertices (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    PolyProgram (ChoiceData t) (List (TagIndex t b × ℕ)) (fun D => D.vertices b) := by
  let R := (PolyProgram.indexSize t b).comp PolyProgram.range
  let pairTag : PolyProgram (ℕ × TagIndex t b) (TagIndex t b × ℕ) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let group := (R.pair (PolyProgram.fst (TagIndex t b) (ChoiceData t))).comp pairTag.mapWith
  unfold ChoiceData.vertices enumPairs
  exact (((PolyProgram.const (List.ofFn (_root_.id : TagIndex t b → TagIndex t b))).pair
    (PolyProgram.id (ChoiceData t))).comp group.mapWith).comp (PolyProgram.flatten (TagIndex t b × ℕ))

/-- 0 and 1 are constants; 2 compares two labels; 3 and 4 compare a label and a helper value. -/
def baseRule {t : ℕ} [NeZero t] : TemplateVertex t → TemplateVertex t → Fin 5 × (Fin t × Fin t)
  | .inl i, .inl j => (if i=j then 0 else 2,(i,j))
  | .inl i, .inr h =>
    if i=h.1.1.1.1 then (3,(i,h.1.1.1.2))
    else if i=h.1.1.1.2 then (3,(i,h.1.1.1.1))
    else (if i=h.1.2 then 1 else 0,(0,0))
  | .inr h, .inl i =>
    if i=h.1.1.1.1 then (4,(i,h.1.1.1.2))
    else if i=h.1.1.1.2 then (4,(i,h.1.1.1.1))
    else (if i=h.1.2 then 1 else 0,(0,0))
  | .inr _, .inr _ => (0,(0,0))

def evalRule {t : ℕ} (D : ChoiceData t) (r : Fin 5 × (Fin t × Fin t)) (d e : ℕ) : Bool :=
  if r.1=0 then false else if r.1=1 then true
  else if r.1=2 then decide (D.label r.2.1 d r.2.2=D.label r.2.2 e r.2.1)
  else if r.1=3 then decide (D.label r.2.1 d r.2.2=e)
  else decide (D.label r.2.1 e r.2.2=d)

lemma eval_baseRule {t : ℕ} [NeZero t] (D : ChoiceData t) (a b : TemplateVertex t) (d e : ℕ) :
    evalRule D (baseRule a b) d e = D.baseTest a d b e := by
  cases a with
  | inl i =>
    cases b with
    | inl j => by_cases h : i=j <;> simp [evalRule,baseRule,ChoiceData.baseTest,h]
    | inr h =>
      by_cases h1 : i=h.1.1.1.1 <;> by_cases h2 : i=h.1.1.1.2 <;> by_cases h3 : i=h.1.2 <;>
        simp_all [evalRule,baseRule,ChoiceData.baseTest,ChoiceData.helperTest]
  | inr h =>
    cases b with
    | inl i =>
      by_cases h1 : i=h.1.1.1.1 <;> by_cases h2 : i=h.1.1.1.2 <;> by_cases h3 : i=h.1.2 <;>
        simp_all [evalRule,baseRule,ChoiceData.baseTest,ChoiceData.helperTest]
    | inr g => simp [evalRule,baseRule,ChoiceData.baseTest]

noncomputable def edgeRule {t : ℕ} [NeZero t] (b : TemplateVertex t → Bit) (x y : TagIndex t b) :
    Fin 5 × (Fin t × Fin t) :=
  if tagTest b (tagDecode t b x) (tagDecode t b y) then
    baseRule (tagDecode t b x).1 (tagDecode t b y).1 else (0,(0,0))

lemma eval_edgeRule {t : ℕ} [NeZero t] (D : ChoiceData t) (b : TemplateVertex t → Bit)
    (x y : TagIndex t b × ℕ) : evalRule D (edgeRule b x.1 y.1) x.2 y.2 = D.edgeTest b x y := by
  unfold edgeRule ChoiceData.edgeTest
  split
  · rw [eval_baseRule]; simp_all
  · simp_all [evalRule]

noncomputable def PolyProgram.evalRule (t : ℕ) :
    PolyProgram (ChoiceData t × ((Fin 5 × (Fin t × Fin t)) × (ℕ × ℕ))) Bool
      (fun x => Complexity.evalRule x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let K : PolyProgram (ChoiceData t × ((Fin 5 × (Fin t × Fin t)) × (ℕ × ℕ))) (Fin 5)
      (fun x => x.2.1.1) := .expr TExpr.input.right.left.left (by intro x; rfl)
  let L : PolyProgram (ChoiceData t × ((Fin 5 × (Fin t × Fin t)) × (ℕ × ℕ)))
      (ChoiceData t × (Fin t × (ℕ × Fin t)))
      (fun x => (x.1,(x.2.1.2.1,(x.2.2.1,x.2.1.2.2)))) :=
    .expr (.pair TExpr.input.left (.pair TExpr.input.right.left.right.left
      (.pair TExpr.input.right.right.left TExpr.input.right.left.right.right))) (by intro x; rfl)
  let R : PolyProgram (ChoiceData t × ((Fin 5 × (Fin t × Fin t)) × (ℕ × ℕ)))
      (ChoiceData t × (Fin t × (ℕ × Fin t)))
      (fun x => (x.1,(x.2.1.2.2,(x.2.2.2,x.2.1.2.1)))) :=
    .expr (.pair TExpr.input.left (.pair TExpr.input.right.left.right.right
      (.pair TExpr.input.right.right.right TExpr.input.right.left.right.left))) (by intro x; rfl)
  let R' : PolyProgram (ChoiceData t × ((Fin 5 × (Fin t × Fin t)) × (ℕ × ℕ)))
      (ChoiceData t × (Fin t × (ℕ × Fin t)))
      (fun x => (x.1,(x.2.1.2.1,(x.2.2.2,x.2.1.2.2)))) :=
    .expr (.pair TExpr.input.left (.pair TExpr.input.right.left.right.left
      (.pair TExpr.input.right.right.right TExpr.input.right.left.right.right))) (by intro x; rfl)
  let d : PolyProgram (ChoiceData t × ((Fin 5 × (Fin t × Fin t)) × (ℕ × ℕ))) ℕ
      (fun x => x.2.2.1) := .expr TExpr.input.right.right.left (by intro x; rfl)
  let e : PolyProgram (ChoiceData t × ((Fin 5 × (Fin t × Fin t)) × (ℕ × ℕ))) ℕ
      (fun x => x.2.2.2) := .expr TExpr.input.right.right.right (by intro x; rfl)
  let LL := L.comp (PolyProgram.choiceLabel t)
  let RR := R.comp (PolyProgram.choiceLabel t)
  let Rr := R'.comp (PolyProgram.choiceLabel t)
  let test := fun (n : Fin 5) => K.comp (PolyProgram.finite (fun i => decide (i=n)))
  refine ((test 0).ite (PolyProgram.const false) ((test 1).ite (PolyProgram.const true)
    ((test 2).ite ((LL.pair RR).comp (PolyProgram.equal ℕ))
      ((test 3).ite ((LL.pair e).comp (PolyProgram.equal ℕ)) ((Rr.pair d).comp (PolyProgram.equal ℕ)))))).congr ?_
  intro x
  change (if decide (_=0) then _ else _) = _
  simp [Complexity.evalRule]

noncomputable def PolyProgram.edgeTest (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    PolyProgram ((TagIndex t b × ℕ) × ((TagIndex t b × ℕ) × ChoiceData t)) Bool
      (fun x => x.2.2.edgeTest b x.1 x.2.1) := by
  let tags : PolyProgram ((TagIndex t b × ℕ) × ((TagIndex t b × ℕ) × ChoiceData t))
      (TagIndex t b × TagIndex t b) (fun x => (x.1.1,x.2.1.1)) :=
    .expr (.pair TExpr.input.left.left TExpr.input.right.left.left) (by intro x; rfl)
  let rule := tags.comp (PolyProgram.finite2 (edgeRule b))
  let nums : PolyProgram ((TagIndex t b × ℕ) × ((TagIndex t b × ℕ) × ChoiceData t))
      (ℕ × ℕ) (fun x => (x.1.2,x.2.1.2)) :=
    .expr (.pair TExpr.input.left.right TExpr.input.right.left.right) (by intro x; rfl)
  let D : PolyProgram ((TagIndex t b × ℕ) × ((TagIndex t b × ℕ) × ChoiceData t))
      (ChoiceData t) (fun x => x.2.2) := .expr TExpr.input.right.right (by intro x; rfl)
  exact ((D.pair (rule.pair nums)).comp (PolyProgram.evalRule t)).congr
    (by intro x; exact eval_edgeRule x.2.2 b x.1 x.2.1)

noncomputable def ChoiceData.matrix {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit) : List Bool :=
  (D.vertices b).flatMap (fun x => (D.vertices b).map (D.edgeTest b x))

noncomputable def PolyProgram.matrixRow (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    PolyProgram ((TagIndex t b × ℕ) × ChoiceData t) (List Bool)
      (fun x => (x.2.vertices b).map (x.2.edgeTest b x.1)) := by
  let swap : PolyProgram ((TagIndex t b × ℕ) × ((TagIndex t b × ℕ) × ChoiceData t))
      ((TagIndex t b × ℕ) × ((TagIndex t b × ℕ) × ChoiceData t))
      (fun x => (x.2.1,(x.1,x.2.2))) :=
    .expr (.pair TExpr.input.right.left (.pair TExpr.input.left TExpr.input.right.right)) (by intro x; rfl)
  let row := (((PolyProgram.snd (TagIndex t b × ℕ) (ChoiceData t)).comp (PolyProgram.vertices t b)).pair
    (PolyProgram.id ((TagIndex t b × ℕ) × ChoiceData t))).comp ((swap.comp (PolyProgram.edgeTest t b)).mapWith)
  exact row

noncomputable def PolyProgram.matrixRows (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    PolyProgram (List (TagIndex t b × ℕ) × ChoiceData t) (List (List Bool))
      (fun x => x.1.map (fun y => (x.2.vertices b).map (x.2.edgeTest b y))) :=
  (PolyProgram.matrixRow t b).mapWith

noncomputable def PolyProgram.rowMatrix (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    PolyProgram (ChoiceData t) (List (List Bool))
      (fun D => (D.vertices b).map (fun y => (D.vertices b).map (D.edgeTest b y))) :=
  ((PolyProgram.vertices t b).pair (PolyProgram.id (ChoiceData t))).comp (PolyProgram.matrixRows t b)

noncomputable def PolyProgram.matrix (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    PolyProgram (ChoiceData t) (List Bool) (fun D => D.matrix b) := by
  refine ((PolyProgram.rowMatrix t b).comp (PolyProgram.flatten Bool)).congr ?_
  intro D
  rfl

end ParityWL.Complexity

end OAI
