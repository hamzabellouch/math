import Mathlib
import OAI.Computability.MinUncut.Search.SampleEnumeration
import OAI.Computability.MinUncut.Graphs.GraphOutput
import OAI.Computability.MinUncut.PCP.Hastad

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.SourceBridge
open MinUncut.Inner MinUncut.Outer
open MinUncutGames.Reduction
attribute [local instance] Classical.propDecidable

def boolField (b : Bool) : F₂ := if b then 1 else 0

def fieldBool (x : F₂) : Bool := decide (x=1)

lemma boolField_fieldBool (x : F₂) : boolField (fieldBool x)=x := by
  fin_cases x <;> rfl

lemma fieldBool_boolField (b : Bool) : fieldBool (boolField b)=b := by
  cases b <;> rfl

def equation {N : Type} (e : CloneGap.Equation N) : Equation N :=
  ⟨![e.first,e.second,e.third],boolField e.rhs⟩

lemma satisfied_equation {N : Type} (e : CloneGap.Equation N) (b : N → Bool) :
    Satisfied (fun x => boolField (b x)) (equation e) ↔ CloneGap.satisfied e b=true := by
  change boolField (b e.first)+boolField (b e.second)+boolField (b e.third)=boolField e.rhs ↔
    ((b e.first ^^ b e.second ^^ b e.third)==e.rhs)=true
  cases e.rhs <;> cases b e.first <;> cases b e.second <;> cases b e.third <;> decide

def equations (input : SourceEncoding.Input) (i : Fin input.equations.length) :
    Equation (Fin input.«variables») := equation input.equations[i]

instance entriesNonempty (input : SourceEncoding.Input) : Nonempty (Fin input.equations.length) :=
  Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr input.nonempty)

lemma sum_list_count {A : Type*} (xs : List A) (f : A → Bool) :
    (∑ i : Fin xs.length, if f xs[i] then (1:ℝ) else 0)=(xs.countP f:ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons] at *
    rw [Fin.sum_univ_succ]
    change (if f x then (1:ℝ) else 0)+(∑ i : Fin xs.length, if f xs[i] then (1:ℝ) else 0)=_
    rw [ih,List.countP_cons]
    cases f x <;> simp [add_comm]

lemma sum_satisfied (input : SourceEncoding.Input) (bits : Fin input.«variables» → Bool) :
    (∑ i : Fin input.equations.length,
      if Satisfied (fun x => boolField (bits x)) (equations input i) then (1:ℝ) else 0)=
      (input.equations.countP (fun e => CloneGap.satisfied e bits):ℝ) := by
  simp_rw [equations,satisfied_equation]
  exact sum_list_count input.equations (fun e => CloneGap.satisfied e bits)

lemma fraction_eq (input : SourceEncoding.Input) (bits : Fin input.«variables» → Bool) :
    equationFraction (equations input) (fun x => boolField (bits x))=
      (MinUncutGames.Outer.HastadSource.success input bits:ℝ) := by
  unfold equationFraction MinUncutGames.Outer.HastadSource.success
  rw [sum_satisfied]
  simp

lemma fraction_eq_assignment (input : SourceEncoding.Input) (s : Fin input.«variables» → F₂) :
    equationFraction (equations input) s=
      (MinUncutGames.Outer.HastadSource.success input (fun x => fieldBool (s x)):ℝ) := by
  simpa only [boolField_fieldBool] using (fraction_eq input (fun x => fieldBool (s x)))

lemma source_sound {ξ : ℚ} (hξ : ξ≤1/2) (R : MinUncutGames.Outer.HastadSource.Reduction ξ)
    (F : MinUncutGames.Foundations.Target.Formula) (hF : ¬F.Satisfiable)
    (s : Fin (R.reduce F).«variables» → F₂) :
    equationFraction (equations (R.reduce F)) s≤3/4 := by
  rw [fraction_eq_assignment]
  have hh : (MinUncutGames.Outer.HastadSource.success (R.reduce F) (fun x => fieldBool (s x)):ℝ)≤
      ((1+ξ)/2:ℚ) := Rat.cast_le.mpr (R.soundness F hF _)
  have hξ' : (ξ:ℝ)≤1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le.mpr hξ : (ξ:ℝ) ≤ ((1/2:ℚ):ℝ))
  push_cast at hh
  linarith

lemma source_complete {ξ : ℚ} (R : MinUncutGames.Outer.HastadSource.Reduction ξ)
    (F : MinUncutGames.Foundations.Target.Formula) (hF : F.Satisfiable)
    (t : ℕ) (b : ℝ) (hξ : (t:ℝ)*(ξ:ℝ)≤b) :
    ∃ s : Fin (R.reduce F).«variables» → F₂,
      (t:ℝ)*(1-equationFraction (equations (R.reduce F)) s)≤b := by
  obtain ⟨bits,hb⟩ := R.completeness F hF
  refine ⟨fun x => boolField (bits x),?_⟩
  rw [fraction_eq]
  have hb' : 1-(ξ:ℝ)≤(MinUncutGames.Outer.HastadSource.success (R.reduce F) bits:ℝ) := by exact_mod_cast hb
  exact (mul_le_mul_of_nonneg_left (by linarith :
    1-(MinUncutGames.Outer.HastadSource.success (R.reduce F) bits:ℝ)≤(ξ:ℝ))
      (Nat.cast_nonneg t)).trans hξ

end MinUncut.SourceBridge

end
namespace MinUncut.Costed.SourceWords
open MinUncutGames.Reduction MinUncut.SourceBridge

lemma flatMap_word {N : ℕ} (xs : List (CloneGap.Equation (Fin N))) (i : ℕ) (hi : i<xs.length) (p : Fin 4) :
    ((xs.flatMap SourceEncoding.equationWords).drop (4*i+p.val)).headI=
      ((SourceEncoding.equationWords xs[i]).drop p.val).headI := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons e xs ih =>
    cases i with
    | zero =>
      fin_cases p <;> simp [SourceEncoding.equationWords]
    | succ i =>
      have hh : i<xs.length := by simpa using hi
      have he : 4*(i+1)+p.val=(((4*i+p.val)+1)+1)+1+1 := by omega
      rw [he]
      simpa only [List.flatMap_cons,SourceEncoding.equationWords,List.cons_append,
        List.nil_append,List.drop_succ_cons,List.getElem_cons_succ] using ih i hh

lemma input_word (input : SourceEncoding.Input) (i : Fin input.equations.length) (p : Fin 4) :
    ((SourceEncoding.inputWords input).drop (2+4*i.val+p.val)).headI=
      ((SourceEncoding.equationWords input.equations[i]).drop p.val).headI := by
  have he : 2+4*i.val+p.val=(4*i.val+p.val)+1+1 := by omega
  rw [he]
  simpa only [SourceEncoding.inputWords,List.cons_append,List.nil_append,List.drop_succ_cons,Fin.getElem_fin] using
    flatMap_word input.equations i.val i.isLt p

lemma input_name (input : SourceEncoding.Input) (i : Fin input.equations.length) (p : Fin 3) :
    ((SourceEncoding.inputWords input).drop (2+4*i.val+p.val)).headI=
      ((equations input i).names p).val := by
  rw [input_word input i ⟨p.val,by omega⟩]
  fin_cases p <;> rfl

lemma input_rhs (input : SourceEncoding.Input) (i : Fin input.equations.length) :
    ((SourceEncoding.inputWords input).drop (2+4*i.val+3)).headI=(equations input i).rhs.val := by
  rw [input_word input i ⟨3,by decide⟩]
  simp only [SourceEncoding.equationWords,List.drop_succ_cons,List.drop_zero,List.headI_cons,
    equations,equation,boolField,Fin.getElem_fin]
  cases input.equations[i.val].rhs <;> norm_num [ZMod.val_one_eq_one_mod]

end MinUncut.Costed.SourceWords

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable

variable {I Name : Type*}

def width (h : Bool) : ℕ := if h then 1 else 3
abbrev Alphabet (h : I → Bool) := (j : I) → Fin (width (h j)) → F₂

lemma slot_width (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) (j : I) :
    secondSlotCount (secondQuestion U h pos j)=width (h j) := by
  cases hh : h j <;> simp [secondQuestion,slotQuestion,hh,secondSlotCount,width]

def alphabetEquiv (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) :
    SecondAlphabet (secondQuestion U h pos) ≃ₗ[F₂] Alphabet h where
  toFun a j k := a j (Fin.cast (slot_width U h pos j).symm k)
  invFun a j k := a j (Fin.cast (slot_width U h pos j) k)
  left_inv a := by funext j k; simp
  right_inv a := by funext j k; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Transport
variable {V A W B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] {m n : ℕ}

def formsPull (e : A ≃ᵃ[F₂] B) : Forms B ≃ Forms A :=
  e.symm.arrowCongrEquiv (AffineEquiv.refl F₂ F₂)

@[simp] lemma formsPull_apply (e : A ≃ᵃ[F₂] B) (f : Forms B) (a : A) :
    formsPull e f a=f (e a) := rfl

def facesPull (e : A ≃ᵃ[F₂] B) : FaceArray B m n ≃ FaceArray A m n :=
  Equiv.piCongrRight (fun _=>formsPull e)

lemma facesPull_eq (e : A ≃ᵃ[F₂] B) (C : FaceArray B m n) :
    facesPull e C=pullbackFaces e.toAffineMap C := by
  funext r
  ext a
  rfl

@[simp] lemma facesPull_label (e : A ≃ᵃ[F₂] B) (C : FaceArray B m n) (a : A) :
    labelCode (facesPull e C) a=labelCode C (e a) := by
  rw [facesPull_eq]
  rfl

variable [Fintype A] [Fintype B]

def samplePull (e : A ≃ᵃ[F₂] B) (g : GridData) :
    LocalSample B m n g ≃ LocalSample A m n g :=
  (facesPull e).prodCongr ((facesPull e).prodCongr (Equiv.refl _))

lemma noiseWeight_pull (e : A ≃ᵃ[F₂] B) (a : ℚ) (C D : FaceArray B m n) (j : Test) :
    noiseWeight a (facesPull e C) (facesPull e D) j=noiseWeight a C D j := by
  cases j <;> try rfl
  simp only [noiseWeight,RowNoise.rationalDensity]
  apply Finset.prod_congr rfl
  intro r _
  have hc : Fintype.card (Forms A)=Fintype.card (Forms B) := (Fintype.card_congr (formsPull e)).symm
  have he : facesPull e D r=facesPull e C r ↔ D r=C r := (formsPull e).injective.eq_iff
  simp only [RowNoise.rationalRowDensity,hc,he]

lemma localWeight_pull (e : A ≃ᵃ[F₂] B) (g : GridData) (a b : ℚ) (j : Test)
    (p : LocalSample B m n g) : localWeight g a b j (samplePull e g p)=localWeight g a b j p := by
  have hc : Fintype.card (FaceArray A m n)=Fintype.card (FaceArray B m n) :=
    (Fintype.card_congr (facesPull (m:=m) (n:=n) e)).symm
  simp only [localWeight,samplePull,Equiv.prodCongr_apply,Prod.map,Equiv.refl_apply,hc,noiseWeight_pull]
end Transport

variable [Fintype I] {m n : ℕ}

def localSampleEquiv (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) (g : GridData) :
    LocalSample (Alphabet h) m n g ≃ LocalSample (SecondAlphabet (secondQuestion U h pos)) m n g :=
  samplePull (alphabetEquiv U h pos).toAffineEquiv g

lemma localSample_weight (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (g : GridData) (a b : ℚ) (j : Test) (p : LocalSample (Alphabet h) m n g) :
    localWeight g a b j (localSampleEquiv U h pos g p)=localWeight g a b j p :=
  localWeight_pull _ _ _ _ _ _

end MinUncut.Outer.LocalTemplate

end
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
namespace SampleEnumeration

local instance bridgeCodeDecidableEq (m n : ℕ) : DecidableEq (Code m n) := codeEq m n

def testQuery {N t m n : ℕ} (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n) (z : Code m n)
    (s : ScoreIndex m n → Bool) : Test → QueryDemand (A := FamilyAlphabet (Name := Fin N) (I := Fin t))
  | .first => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => s (false,labelCode B a)) (fun a => s (true,labelCode B a))
  | .second => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => s (true,labelCode B a)) (fun a => s (true,labelCode C a))
  | .third => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => Function.update (fun z => s (true,z)) z true (labelCode B a))
    (fun a => Function.update (fun z => s (true,z)) z false (labelCode B a))
  | .fourth => comparison (.inl U) (.inr (secondQuestion U h pos))
    (fun a => s (true,labelCode (pullbackFaces (projection U h pos) C) a))
    (fun a => s (true,labelCode C a))

lemma testQuery_eq {N t m n : ℕ} (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n) (z : Code m n)
    (s : ScoreIndex m n → Bool) (j : Test) : testQuery U h pos B C z s j=Outer.testQuery U h pos B C z s j := by
  cases j <;> try rfl
  simp only [testQuery,Outer.testQuery,Function.update_apply]
  apply congrArg₂ (comparison _ _)
  · funext a
    split_ifs <;> rfl
  · funext a
    split_ifs <;> rfl

def hidden {s t k : ℕ} (o : OuterSample (Fin t) (Fin s) k) : Fin t → Bool :=
  fun j => decide (j∈o.1.val)

lemma hidden_eq {s t k : ℕ} (o : OuterSample (Fin t) (Fin s) k) : hidden o=sampleHidden o := by
  funext j
  simp [hidden,sampleHidden,hiddenSet]

def rawQuery {N s t k m n : ℕ} (eqs : Fin s → Equation (Fin N)) (g : GridData) (σ η : ℚ)
    (o : OuterSample (Fin t) (Fin s) k) (j : Test)
    (p : LocalSample (SecondAlphabet (secondQuestion (sampleFirst eqs o) (hidden o) o.2.2)) m n g) :
    QueryDemand (A := FamilyAlphabet (Name := Fin N) (I := Fin t)) :=
  testQuery (sampleFirst eqs o) (hidden o) o.2.2 p.1 p.2.1 p.2.2.1
    (rationalScoreTable σ η (fun i => midpoint g.T g.L (p.2.2.2 i))) j

def query {N s t k m n : ℕ} (eqs : Fin s → Equation (Fin N)) (g : GridData) (σ η : ℚ)
    (j : Test) (e : Elementary (I := Fin t) eqs k m n g) :
    QueryDemand (A := FamilyAlphabet (Name := Fin N) (I := Fin t)) :=
  ((hidden_eq e.1) ▸ rawQuery eqs g σ η e.1 j) e.2

lemma query_eq {N s t k m n : ℕ} (eqs : Fin s → Equation (Fin N)) (g : GridData) (σ η : ℚ)
    (j : Test) (e : Elementary (I := Fin t) eqs k m n g) :
    query eqs g σ η j e=elementaryQuery eqs g σ η j e := by
  have helper (h h' : Fin t → Bool) (hh : h=h') :
      (hh ▸ (fun p : LocalSample (SecondAlphabet (secondQuestion (sampleFirst eqs e.1) h e.1.2.2)) m n g =>
        testQuery (sampleFirst eqs e.1) h e.1.2.2 p.1 p.2.1 p.2.2.1
          (rationalScoreTable σ η (fun i => midpoint g.T g.L (p.2.2.2 i))) j))=
      (fun p : LocalSample (SecondAlphabet (secondQuestion (sampleFirst eqs e.1) h' e.1.2.2)) m n g =>
        Outer.testQuery (sampleFirst eqs e.1) h' e.1.2.2 p.1 p.2.1 p.2.2.1
          (rationalScoreTable σ η (fun i => midpoint g.T g.L (p.2.2.2 i))) j) := by
    cases hh
    funext p
    exact testQuery_eq _ _ _ _ _ _ _ _
  exact congrFun (helper _ _ (hidden_eq e.1)) e.2

def demand {N s t k m n : ℕ} (eqs : Fin s → Equation (Fin N)) (g : GridData) (σ η : ℚ)
    (e : AllElementary (I := Fin t) eqs k m n g) : PathRealization.Demand (FamilyVariable (Fin N) (Fin t)) :=
  (query eqs g σ η e.1 e.2).signed familyBase

lemma demand_eq {N s t k m n : ℕ} (eqs : Fin s → Equation (Fin N)) (g : GridData) (σ η : ℚ)
    (e : AllElementary (I := Fin t) eqs k m n g) :
    demand eqs g σ η e=allDemand eqs g σ η e := by
  simp only [demand,allDemand,query_eq]

end SampleEnumeration
end MinUncut.Outer

noncomputable section
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*}

def projectSlot : (h : Bool) → Fin 3 → Triple → (Fin (width h) → F₂)
  | false,_,x => x
  | true,p,x => fun _=>x p

def project (h : I → Bool) (pos : I → Fin 3) (x : I → Triple) : Alphabet h :=
  fun j=>projectSlot (h j) (pos j) (x j)

def decode (h : I → Bool) (x : I → Triple) : Alphabet h :=
  project h (fun _=>0) x

def originTable (U : I → Equation Name) : I → Triple := fun j _=>(U j).rhs

lemma slotCount_width (E : Equation Name) (b : Bool) (p : Fin 3) :
    secondSlotCount (slotQuestion E b p)=width b := by cases b <;> rfl

lemma slotProjection_cast (E : Equation Name) (b : Bool) (p : Fin 3) (a : alphabet E)
    (k : Fin (width b)) :
    slotProjection E b p a (Fin.cast (slotCount_width E b p).symm k)=projectSlot b p a.val k := by
  cases b <;> rfl

lemma alphabetEquiv_projection (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (a : FirstAlphabet U) :
    alphabetEquiv U h pos (projection U h pos a)=project h pos (fun j=>(a j).val) := by
  funext j k
  exact slotProjection_cast (U j) (h j) (pos j) (a j) k

lemma alphabetEquiv_zero (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) :
    alphabetEquiv U h pos 0=0 := map_zero _

variable {N t : ℕ}

lemma decodeSlot (b : Bool) (x : Triple) (k : Fin (width b))
    (hk : k.val<3) : x ⟨k.val,hk⟩=projectSlot b 0 x k := by
  cases b
  · rfl
  · have he : k.val=0 := by have hi:=k.isLt; change k.val<1 at hi; omega
    change x ⟨k.val,hk⟩=x 0
    congr 1
    exact Fin.ext he

lemma alphabetEquiv_decode (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (x : Fin t → Triple) :
    alphabetEquiv U h pos (decodeSecond (secondQuestion U h pos) x)=decode h x := by
  funext j k
  exact decodeSlot (h j) (x j) k _

lemma extend_second_rep (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    extendTable (.inr (secondQuestion U h pos))
      (rep (familyBase (.inr (secondQuestion U h pos))) (fun a=>P (alphabetEquiv U h pos a))).val =
      (fun x=>P 0 == P (decode h x)) := by
  funext x
  simp only [extendTable,decodeAlphabet,rep,familyBase]
  change (P (alphabetEquiv U h pos 0) ==
    P (alphabetEquiv U h pos (decodeSecond (secondQuestion U h pos) x)))=_
  rw [alphabetEquiv_zero,alphabetEquiv_decode]

lemma extend_first_rep (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    extendTable (.inl U)
      (rep (familyBase (.inl U)) (fun a=>P (alphabetEquiv U h pos (projection U h pos a)))).val =
      (fun x=>if ∀j,Valid (U j) (x j) then
        P (project h pos (originTable U)) == P (project h pos x) else false) := by
  funext x
  simp only [extendTable,decodeAlphabet]
  by_cases hx : ∀j,Valid (U j) (x j)
  · simp only [decodeFirst,dite_eq_left hx,ite_eq_left hx,
      rep,familyBase,alphabetEquiv_projection]
    exact congrArg (fun a => P (project h pos (originTable U)) == P a)
      (alphabetEquiv_projection U h pos (fun j => ⟨x j,hx j⟩))
  · simp only [decodeFirst,dite_eq_right hx,ite_eq_right hx]
    rfl

lemma first_base (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    P (alphabetEquiv U h pos (projection U h pos (familyBase (.inl U))))=
      P (project h pos (originTable U)) := by
  exact congrArg P (alphabetEquiv_projection U h pos (familyBase (.inl U)))

lemma second_base (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    P (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos))))=P 0 := by
  exact congrArg P (alphabetEquiv_zero U h pos)

open scoped BigOperators
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable
variable {Name I S : Type} [Fintype I] [Fintype S] {k m n : ℕ} {g : GridData}

abbrev Index (I : Type) [Fintype I] (k m n : ℕ) (g : GridData) :=
  Test × Σ H : FixedSets I k, (I → Fin 3) × LocalSample (Alphabet (hiddenSet H.val)) m n g

instance indexFintype : Fintype (Index I k m n g) := by unfold Index; infer_instance

def occurrence (eqs : S → Equation Name) : ((I → S) × Index I k m n g) ≃ AllElementary (I := I) eqs k m n g where
  toFun p := (p.2.1,⟨(p.2.2.1,p.1,p.2.2.2.1),
    localSampleEquiv (fun i=>eqs (p.1 i)) (hiddenSet p.2.2.1.val) p.2.2.2.1 g p.2.2.2.2⟩)
  invFun p := (p.2.1.2.1,p.1,⟨p.2.1.1,p.2.1.2.2,
    (localSampleEquiv (sampleFirst eqs p.2.1) (sampleHidden p.2.1) p.2.1.2.2 g).symm p.2.2⟩)
  left_inv p := by
    rcases p with ⟨u,j,H,pos,p⟩
    simp only [localSampleEquiv]
    rfl
  right_inv p := by
    rcases p with ⟨j,⟨⟨H,u,pos⟩,p⟩⟩
    simp only [localSampleEquiv]
    rfl

def weight (a : ℚ) (b : Test → ℚ) (e : Index I k m n g) : ℚ :=
  localWeight g a (b e.1) e.1 e.2.2.2

def repetitions (a : ℚ) (b : Test → ℚ) (e : Index I k m n g) : ℕ :=
  multiplicity (innerDenominator (Fintype.card I) m n g a b) (weight a b e)

lemma occurrence_weight (eqs : S → Equation Name) (a : ℚ) (b : Test → ℚ)
    (u : I → S) (e : Index I k m n g) :
    allWeight eqs g a b (occurrence eqs (u,e))=
      (Fintype.card (OuterSample I S k):ℚ)⁻¹*weight a b e := by
  change _*localWeight g a (b e.1) e.1
    (localSampleEquiv (fun i=>eqs (u i)) (hiddenSet e.2.1.val) e.2.2.1 g e.2.2.2)=_
  rw [localSample_weight]
  rfl

lemma weight_nonneg (hT : 0<g.T) (hL : 0<g.L) {a : ℚ} (ha : 0≤a) (ha1 : a≤1)
    (b : Test → ℚ) (hb : ∀j,0<b j) (e : Index I k m n g) : 0≤weight a b e :=
  localWeight_nonneg g hT hL ha ha1 (hb e.1) e.1 e.2.2.2

omit [Fintype S] in
lemma weight_den (eqs : S → Equation Name) (u : I → S) (a : ℚ) (b : Test → ℚ)
    (e : Index I k m n g) : (weight a b e).den ∣ innerDenominator (Fintype.card I) m n g a b := by
  have hh := localWeight_den (secondQuestion (fun i=>eqs (u i)) (hiddenSet e.2.1.val) e.2.2.1)
    g a b e.1 (localSampleEquiv (fun i=>eqs (u i)) (hiddenSet e.2.1.val) e.2.2.1 g e.2.2.2)
  rw [localSample_weight] at hh
  exact hh

lemma occurrence_multiplicity [Nonempty S] (eqs : S → Equation Name) (hk : k≤Fintype.card I)
    (hT : 0<g.T) (hL : 0<g.L) {a : ℚ} (ha : 0≤a) (ha1 : a≤1)
    (b : Test → ℚ) (hb : ∀j,0<b j) (u : I → S) (e : Index I k m n g) :
    multiplicity (samplerDenominator I S k m n g a b)
      (allWeight eqs g a b (occurrence eqs (u,e)))=repetitions a b e := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  have hc : (0:ℚ)<Fintype.card (OuterSample I S k) := by exact_mod_cast Fintype.card_pos
  have hw := weight_nonneg hT hL ha ha1 b hb e
  have he := occurrence_weight eqs a b u e
  have hd := elementaryWeight_den eqs hk g a b e.1 (occurrence eqs (u,e)).2
  change (allWeight eqs g a b (occurrence eqs (u,e))).den ∣ _ at hd
  apply Nat.cast_injective (R := ℚ)
  rw [multiplicity_cast (by rw [he]; positivity) hd, repetitions,
    multiplicity_cast hw (weight_den eqs u a b e),he]
  simp only [samplerDenominator,Nat.cast_mul]
  field_simp

open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
variable {I Name : Type*} [Fintype I] {m n : ℕ}

structure Query (h : I → Bool) where
  first : Bool
  left : Alphabet h → Bool
  right : Alphabet h → Bool

def query (h : I → Bool) (B C : FaceArray (Alphabet h) m n) (z : Code m n)
    (s : ScoreIndex m n → Bool) : Test → Query h
  | .first => ⟨false,(fun a=>s (false,labelCode B a)),(fun a=>s (true,labelCode B a))⟩
  | .second => ⟨false,(fun a=>s (true,labelCode B a)),(fun a=>s (true,labelCode C a))⟩
  | .third => ⟨false,(fun a=>Function.update (fun z=>s (true,z)) z true (labelCode B a)),
                     (fun a=>Function.update (fun z=>s (true,z)) z false (labelCode B a))⟩
  | .fourth => ⟨true,(fun a=>s (true,labelCode C a)),(fun a=>s (true,labelCode C a))⟩

def Query.realize {h : I → Bool} (T : Query h) (U : I → Equation Name) (pos : I → Fin 3) :
    QueryDemand (A := FamilyAlphabet (Name := Name) (I := I)) :=
  if T.first then
    comparison (.inl U) (.inr (secondQuestion U h pos))
      (fun a=>T.left (alphabetEquiv U h pos (projection U h pos a)))
      (fun a=>T.right (alphabetEquiv U h pos a))
  else
    comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
      (fun a=>T.left (alphabetEquiv U h pos a))
      (fun a=>T.right (alphabetEquiv U h pos a))

omit [Fintype I] in
lemma query_realize (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B C : FaceArray (Alphabet h) m n) (z : Code m n) (s : ScoreIndex m n → Bool) (j : Test) :
    (query h B C z s j).realize U pos =
      testQuery U h pos (facesPull (alphabetEquiv U h pos).toAffineEquiv B)
        (facesPull (alphabetEquiv U h pos).toAffineEquiv C) z s j := by
  cases j <;> simp only [query,Query.realize,Bool.false_eq_true,ite_false,ite_true,testQuery]
  all_goals apply congrArg₂ (comparison _ _)
  all_goals funext a
  all_goals rfl

structure Signature (I : Type*) where
  rhs : I → F₂
  same : I → Fin 3 → Fin 3 → Bool

def signature (U : I → Equation Name) : Signature I :=
  ⟨fun i=>(U i).rhs,fun i p q=>decide ((U i).names p=(U i).names q)⟩

def Signature.Valid (s : Signature I) (x : I → Triple) : Prop :=
  ∀i, parity (x i)=s.rhs i ∧ ∀p q,s.same i p q=true → x i p=x i q

def Signature.origin (s : Signature I) : I → Triple := fun i _=>s.rhs i

omit [Fintype I] in
lemma signature_valid (U : I → Equation Name) (x : I → Triple) :
    (signature U).Valid x ↔ ∀i,Valid (U i) (x i) := by
  simp only [Signature.Valid,signature,Valid,decide_eq_true_eq]
omit [Fintype I] in
lemma signature_origin (U : I → Equation Name) : (signature U).origin=originTable U := rfl

variable {N t : ℕ}

def Query.leftBase {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3) (s : Signature (Fin t)) : Bool :=
  if T.first then T.left (project h pos s.origin) else T.left 0

def Query.leftTable {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3)
    (s : Signature (Fin t)) : (Fin t → Triple) → Bool :=
  if T.first then fun x=>if s.Valid x then T.leftBase pos s == T.left (project h pos x) else false
    else fun x=>T.left 0 == T.left (decode h x)

def Query.rightTable {h : Fin t → Bool} (T : Query h) : (Fin t → Triple) → Bool :=
  fun x=>T.right 0 == T.right (decode h x)

def Query.localSign {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3) (s : Signature (Fin t)) : Bool :=
  T.leftBase pos s == T.right 0

lemma Query.left_extended {h : Fin t → Bool} (T : Query h) (U : Fin t → Equation (Fin N))
    (pos : Fin t → Fin 3) :
    extendTable (T.realize U pos).left.1 (rep (familyBase (T.realize U pos).left.1)
      (T.realize U pos).left.2).val = T.leftTable pos (signature U) := by
  rcases T with ⟨first,left,right⟩
  cases first
  · exact extend_second_rep U h pos left
  · change extendTable (.inl U) (rep (familyBase (.inl U))
        (fun a=>left (alphabetEquiv U h pos (projection U h pos a)))).val =
        (fun x=>if (signature U).Valid x then
          left (project h pos (signature U).origin) == left (project h pos x) else false)
    simp_rw [signature_valid]
    exact extend_first_rep U h pos left

lemma Query.right_extended {h : Fin t → Bool} (T : Query h) (U : Fin t → Equation (Fin N))
    (pos : Fin t → Fin 3) :
    extendTable (T.realize U pos).right.1 (rep (familyBase (T.realize U pos).right.1)
      (T.realize U pos).right.2).val = T.rightTable := by
  rcases T with ⟨first,left,right⟩
  cases first <;> exact extend_second_rep U h pos right

lemma Query.signed_equal {h : Fin t → Bool} (T : Query h) (U : Fin t → Equation (Fin N))
    (pos : Fin t → Fin 3) :
    ((T.realize U pos).signed familyBase).equal=T.localSign pos (signature U) := by
  rcases T with ⟨first,left,right⟩
  cases first
  · change (left (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos)))) ==
      right (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos))))) = (left 0 == right 0)
    rw [second_base U h pos left,second_base U h pos right]
  · change (left (alphabetEquiv U h pos (projection U h pos (familyBase (.inl U)))) ==
      right (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos))))) =
      (left (project h pos (signature U).origin) == right 0)
    rw [first_base U h pos left,second_base U h pos right,signature_origin]

end MinUncut.Outer.LocalTemplate

end

end OAI
