import Mathlib
import OAI.Computability.MinUncut.Graphs.CanonicalSamplerGraph
import OAI.Computability.MinUncut.Estimates.LocalBodyEffectivity
import OAI.Computability.MinUncut.Search.EnumerationPlain
import OAI.Computability.MinUncut.Estimates.UniformSets

namespace OAI

noncomputable section
namespace MinUncut.Preprocess.DemandOrder
open MinUncut.OuterSmoothness MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteGaussian MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open MinUncut.Costed MinUncut.Costed.SourceWords
attribute [local irreducible] localWeight MinUncut.FiniteProof.multiplicity innerDenominator rationalScoreTable MinUncut.FiniteGaussian.midpoint
abbrev Body (t : ℕ) (h : Fin t → Bool) (m n : ℕ) (g : GridData) :=
  (LocalSample (Alphabet h) m n g × Test) × (Fin t → Fin 3)
def bodyEncoding (t : ℕ) (h : Fin t → Bool) (m n : ℕ) (hn : 0<n) (g : GridData) : Encoding (Body t h m n g) :=
  (DemandBody.samples (fun _ : Unit=>t) (ca_const t) (fun _=>h)
    (ca_const ((((Encoding.fin t).function Encoding.bool).code h).val))
    (fun _=>m) (fun _=>n) (ca_const m) (ca_const n) (fun _=>hn) (fun _=>g) (ca_const g)).enc ()
lemma samples_enc {P : Type} [Primcodable P] (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
    (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
    (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
    (g : P → GridData) (hg : Computable g) (p : P) :
    (DemandBody.samples t ht h hc m n hm hn hnpos g hg).enc p=
      bodyEncoding (t p) (h p) (m p) (n p) (hnpos p) (g p) := rfl

def bodyExpr {t m n : ℕ} {h : Fin t → Bool} {g : GridData} (σ η : ℚ) (x : Body t h m n g) : List AExpr :=
  let Q:=query h x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
    (rationalScoreTable σ η (fun i=>midpoint g.T g.L (x.1.1.2.2.2 i))) x.1.2
  [leftExpr Q x.2,rightExpr Q x.2,signExpr Q x.2]
def bodyRepetitions {t m n : ℕ} {h : Fin t → Bool} {g : GridData} (a : ℚ) (b : Test → ℚ) (x : Body t h m n g) :=
  multiplicity (innerDenominator t m n g a b) (localWeight g a (b x.1.2) x.1.2 x.1.1)
def bodyExpressions (t : ℕ) (h : Fin t → Bool) (m n : ℕ) (hn : 0<n) (g : GridData)
    (a : ℚ) (b : Test → ℚ) (σ η : ℚ) : List AExpr :=
  (bodyEncoding t h m n hn g).enumerate.flatMap (fun x=>
    (List.replicate (bodyRepetitions a b x) (bodyExpr σ η x)).flatten)
def indexEquiv (t k m n : ℕ) (g : GridData) :
    (ΣH:FixedSets (Fin t) k,Body t (hiddenSet H.val) m n g) ≃ Index (Fin t) k m n g where
  toFun x := (x.2.1.2,⟨x.1,x.2.2,x.2.1.1⟩)
  invFun x := ⟨x.2.1,((x.2.2.2,x.1),x.2.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def enumeration (t k m n : ℕ) (hn : 0<n) (g : GridData) : Enumeration (Index (Fin t) k m n g) :=
  ((Enumeration.ofEncoding (setEncoding t)).filterSubtype (fun S=>S.card=k) |>.bind
    (fun H=>Enumeration.ofEncoding (bodyEncoding t (hiddenSet H.val) m n hn g))).mapEquiv (indexEquiv t k m n g)
lemma localExpressions_eq (t k m n : ℕ) (hn : 0<n) (g : GridData) (a : ℚ) (b : Test → ℚ) (σ η : ℚ) :
    localExpressions (enumeration t k m n hn g) a b σ η=
      (setEncoding t).enumerate.flatMap (fun S=>if S.card=k then
        bodyExpressions t (hiddenSet S) m n hn g a b σ η else []) := by
  unfold localExpressions enumeration Enumeration.mapEquiv Enumeration.bind
  simp only [List.flatMap_map,List.flatMap_assoc]
  have he : ∀(H:FixedSets (Fin t) k) (x:Body t (hiddenSet H.val) m n g),
      repetitions a b ((indexEquiv t k m n g) ⟨H,x⟩)=bodyRepetitions a b x := by
    intro H x
    simp only [repetitions,weight,indexEquiv,Equiv.coe_fn_mk,bodyRepetitions,Fintype.card_fin]
    congr 2
    exact Subsingleton.elim _ _
  simp only [he]
  change ((Enumeration.ofEncoding (setEncoding t)).filterSubtype (fun S=>S.card=k)).values.flatMap
    (fun H=>bodyExpressions t (hiddenSet H.val) m n hn g a b σ η)=_
  exact Enumeration.filterSubtype_flatMap (Enumeration.ofEncoding (setEncoding t)) (fun S=>S.card=k)
    (fun S=>bodyExpressions t (hiddenSet S) m n hn g a b σ η)

lemma c_bodyExpressions {P : Type} [Primcodable P]
    (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
    (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
    (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
    (g : P → GridData) (hg : Computable g) (a : P → ℚ) (ha : Computable a)
    (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j))
    (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    Computable (fun p=>(bodyExpressions (t p) (h p) (m p) (n p) (hnpos p) (g p) (a p) (b p) (σ p) (η p)).map
      (fun e=>e.program.code)) := by
  have hh := Primrec.list_flatten.to_comp.comp
    (DemandBody.out_repeatedExpressions t ht h hc m n hm hn hnpos g hg a ha b hb σ η hσ hη).enumerate
  apply hh.of_eq
  intro p
  rw [samples_enc]
  simp only [bodyExpressions,List.flatMap_def,List.map_flatten,List.map_map,List.map_replicate,
    bodyRepetitions,bodyExpr,DemandBody.bodyQuery,Function.comp_def]

open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian MinUncut.Costed MinUncut.Costed.SourceWords UEncoding
variable {P : Type} [Primcodable P]
lemma out_bodyExpressions
    (t : P → ℕ) (ht : Computable t) (m n : P → ℕ) (hm : Computable m) (hn : Computable n)
    (hnpos : ∀p,0<n p) (g : P → GridData) (hg : Computable g) (a : P → ℚ) (ha : Computable a)
    (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j))
    (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    (sets t ht).Out (fun p S=>(bodyExpressions (t p) (hiddenSet S) (m p) (n p) (hnpos p)
      (g p) (a p) (b p) (σ p) (η p)).map (fun e=>e.program.code)) := by
  have hc := c_bodyExpressions (fun q : P × ℕ=>t q.1) (ht.comp Computable.fst)
    (fun q=>hiddenSet (rawSet (t q.1) q.2))
    (c_rawHidden _ (ht.comp Computable.fst) _ Computable.snd)
    (fun q=>m q.1) (fun q=>n q.1) (hm.comp Computable.fst) (hn.comp Computable.fst)
    (fun q=>hnpos q.1) (fun q=>g q.1) (hg.comp Computable.fst)
    (fun q=>a q.1) (ha.comp Computable.fst) (fun q=>b q.1) (hb.pullback Computable.fst)
    (fun q=>σ q.1) (fun q=>η q.1) (hσ.comp Computable.fst) (hη.comp Computable.fst)
  refine ⟨_,hc,?_⟩
  intro p S
  change (bodyExpressions _ (hiddenSet (rawSet _ ((setEncoding (t p)).code S).val)) _ _ _ _ _ _ _ _).map _=_
  rw [rawSet_code]
lemma c_localExpressions
    (t k : P → ℕ) (ht : Computable t) (hk : Computable k)
    (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
    (g : P → GridData) (hg : Computable g) (a : P → ℚ) (ha : Computable a)
    (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j))
    (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    Computable (fun p=>(localExpressions (enumeration (t p) (k p) (m p) (n p) (hnpos p) (g p))
      (a p) (b p) (σ p) (η p)).map (fun e=>e.program.code)) := by
  have how := out_bodyExpressions t ht m n hm hn hnpos g hg a ha b hb σ η hσ hη
  have cond := ((out_setCard t ht).pair (out_const (sets t ht) hk)).map Primrec.eq.computablePred.decide
  have hc := (Primrec.list_flatten.to_comp.comp
    (Out.cond cond.toBool how (out_const (sets t ht) (ca_const []))).enumerate)
  apply hc.of_eq
  intro p
  rw [localExpressions_eq]
  simp only [List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro S hS
  split_ifs <;> simp_all
end MinUncut.Preprocess.DemandOrder

end
namespace MinUncut.Costed.GraphRegisters
open PolyProgram

def vertexExpr : Expr := .add (.reg 0) (.mul (.reg 1) (.const 3))
def lastVertexExpr : Expr := .sub vertexExpr (.const 1)

def initRender (v : List ℕ) : List ℕ :=
  let V := v.headI+(v.drop 1).headI*3
  V^2::(queryState v.headI (v.drop 1).headI (v.drop 2).headI V (V-1) (V-1) [] (v.drop 3)).encode

noncomputable def initProgram : PolyProgram initRender :=
  ((vertexExpr.mul vertexExpr).program.cons ((projection 0).cons ((projection 1).cons
    ((projection 2).cons (vertexExpr.program.cons (lastVertexExpr.program.cons
      (lastVertexExpr.program.cons ((const 0).cons ((const 2).cons ((projection 2).cons (drop 3))))))))))).ofEq (by
        intro v
        simp only [Expr.eval,vertexExpr,lastVertexExpr,initRender,queryState,RenderState.encode,
          List.headI_cons,List.length_nil,List.nil_append,List.drop_zero,pow_two])

def rawGraphWords (N M k : ℕ) (data : List ℕ) : List ℕ :=
  let V := N+M*3
  V::(rawTable N M data V V++2::k::data)

def renderRaw (v : List ℕ) : List ℕ :=
  rawGraphWords v.headI (v.drop 1).headI (v.drop 2).headI (v.drop 3)

noncomputable def rawRenderer : PolyProgram renderRaw :=
  (((projection 3).cons (drop 7)).comp (renderLoop.comp initProgram)).ofEq (by
    intro v
    simp only [Function.comp_apply,initRender,List.headI_cons,List.tail_cons]
    rw [renderTick_iter_encode]
    change (RenderState.tick^[(_+_*3)^2] _).V::(RenderState.tick^[(_+_*3)^2] _).tape=_
    rw [tick_iter_V,tick_table]
    rfl)

lemma renderRaw_encode (N M k : ℕ) (data : List ℕ) :
    renderRaw (N::M::k::data)=rawGraphWords N M k data := rfl

open MinUncut.PathRealization

lemma length_packDemands {N : ℕ} (ds : List (Demand (Fin N))) :
    (packDemands ds).length=3*ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [packDemands,List.flatMap_cons,List.length_append,
      packDemand,List.length_cons,List.length_nil,List.length_cons] at ih ⊢; omega

lemma rawLocal_append (N d : ℕ) (data rest : List ℕ) (u v : ℕ) (h : 3*d+2<data.length) :
    rawLocal N d (data++rest) u v=rawLocal N d data u v := by
  simp only [rawLocal,drop_head_append data rest (3*d) (by omega),
    drop_head_append data rest (3*d+1) (by omega),drop_head_append data rest (3*d+2) h]

lemma rawCell_append (N M : ℕ) (data rest : List ℕ) (u v : ℕ) (h : 3*M≤data.length) :
    rawCell N M (data++rest) u v=rawCell N M data u v := by
  unfold rawCell
  congr 1
  apply propext
  constructor <;> rintro ⟨d,hd,he⟩ <;> refine ⟨d,hd,?_⟩
  · rwa [rawLocal_append N d data rest u v (by omega)] at he
  · rwa [rawLocal_append N d data rest u v (by omega)]

lemma rawTable_append (N M : ℕ) (data rest : List ℕ) (r c : ℕ) (h : 3*M≤data.length) :
    rawTable N M (data++rest) r c=rawTable N M data r c := by
  unfold rawTable rawRow
  have hh : rawCell N M (data++rest)=rawCell N M data := by
    funext u v
    exact rawCell_append N M data rest u v h
  rw [hh]

lemma renderer_pack {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (rest : List ℕ) :
    renderRaw (N::ds.length::k::(packDemands ds++rest))=
      (N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::(packDemands ds++rest)) := by
  rw [renderRaw_encode,rawGraphWords,rawTable_append N ds.length _ rest _ _ (by rw [length_packDemands]),
    rawTable_pack]
end MinUncut.Costed.GraphRegisters

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.Parameters
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name S : Type*} [Fintype Name] [Fintype S] [Nonempty S]

def graph {J : ℕ} (P : Parameters J) (equations : S → Equation Name) : MinUncut.Output :=
  rationalGraph (P.denominator S) P.denominator_pos (P.weight equations) (P.demand equations)

lemma graph_threshold {J : ℕ} (P : Parameters J) (equations : S → Equation Name) :
    (P.graph equations).threshold=5*P.denominator S := rfl

lemma graph_yes {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (s : Name → F₂)
    (hs : (P.o.t:ℝ)*(1-equationFraction equations s)≤P.o.b4) :
    (P.graph equations).opt≤(P.graph equations).threshold := by
  apply rationalGraph_yes _ _ _ (P.weight_nonneg equations) (P.weight_den equations) _
    (honestProof (I := Fin P.o.t) s).assignment
  rw [P.failure_eq,ProofFamily.variableProof_assignment]
  exact (finite_honest_cost P.hJ P.d P.hd P.o P.ho equations s (Fintype.card_fin _) hs).le

lemma graph_no {K J : ℕ} (hK : 2≤K) (hKJ : 8*K≤J) (P : Parameters J)
    (equations : S → Equation Name) (hs : ∀ s : Name → F₂, equationFraction equations s≤3/4) :
    K*(P.graph equations).threshold<(P.graph equations).opt := by
  let : NeZero P.o.t := ⟨ne_of_gt P.t_pos⟩
  apply rationalGraph_no hK _ _ _ (P.weight_nonneg equations) (P.weight_den equations)
  intro y
  rw [P.failure_eq]
  have hh := finite_unsound_cost P.hJ P.d P.hd P.o P.ho (variableProof y) equations
    (Fintype.card_fin _) hs
  change (J:ℝ)-1/2 < (variableProof y).finiteCost _ _ P.grid equations at hh
  have hJ' : 8*(K:ℝ)≤J := by exact_mod_cast hKJ
  linarith

lemma graph_vertices {J : ℕ} (P : Parameters J) (equations : S → Equation Name) :
    (P.graph equations).vertices = Fintype.card (FamilyVariable Name (Fin P.o.t))+
      3*Fintype.card (UnitDemand (P.denominator S) (P.weight equations)) := by
  rw [graph,rationalGraph_vertices,expanded_card]

omit [Fintype Name] in
lemma graph_demands {J : ℕ} (P : Parameters J) (equations : S → Equation Name) :
    (Fintype.card (UnitDemand (P.denominator S) (P.weight equations)):ℚ)=
      (P.denominator S:ℚ)*rationalWeight J P.d P.o := by
  rw [expanded_card_cast _ _ (P.weight_nonneg equations) (P.weight_den equations),P.weight_sum]

end MinUncut.Outer.Parameters

end

end OAI
