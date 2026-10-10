import Mathlib
import OAI.Computability.MinUncut.Search.ParameterFields
import OAI.Computability.MinUncut.Search.UniformRational
import OAI.Computability.MinUncut.Games.QuestionExpressions
import OAI.Computability.MinUncut.Estimates.UniformFaceArray
import OAI.Computability.MinUncut.Machines.UniformDemandAlphabet
import OAI.Computability.MinUncut.Estimates.UniformProduct

namespace OAI

noncomputable section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian
open scoped BigOperators
lemma c_coefficient : Computable coefficient :=
  ca_ratDiv (ca_ratPow (ca_const (-1)) Computable.id)
    (ca_ratMul (ca_ratPow (ca_const 2) Computable.id) (ca_ratCast (ca_factorial Computable.id)))
lemma c_primitive : Computable₂ primitive := by
  have hc : Computable₂ (fun (p : ℕ × ℚ) (j : ℕ)=>coefficient j*p.2^(2*j+1)/(2*j+1)) := by
    apply ca_ratDiv
    · exact ca_ratMul (c_coefficient.comp Computable.snd)
        (ca_ratPow (Computable.snd.comp Computable.fst) (ca_add (ca_mul (ca_const 2) Computable.snd) (ca_const 1)))
    · exact ca_ratAdd (ca_ratMul (ca_const 2) (ca_ratCast Computable.snd)) (ca_const 1)
  exact ((c_rangeSum hc computable_ratAdd).comp Computable.id
    (ca_add (ca_mul (ca_const 2) Computable.fst) (ca_const 1))).of_eq
      (by
        intro p
        dsimp only [primitive]
        rw [←List.sum_toFinset _ List.nodup_range,List.toFinset_range]
        rfl)
lemma c_qIntegral : Computable (fun p : ℕ × ℚ × ℚ=>qIntegral p.1 p.2.1 p.2.2) :=
  ca_ratSub (c_primitive.comp Computable.fst (Computable.snd.comp Computable.snd))
    (c_primitive.comp Computable.fst (Computable.fst.comp Computable.snd))
lemma c_endpoint : Computable (fun p : ℚ × ℕ × ℕ=>endpoint p.1 p.2.1 p.2.2) := by
  unfold endpoint
  exact ca_ratAdd (computable_ratNeg.comp Computable.fst)
    (ca_ratDiv (ca_ratMul (ca_ratMul (ca_const 2) Computable.fst)
      (ca_ratCast (Computable.snd.comp Computable.snd)))
      (ca_ratCast (Computable.fst.comp Computable.snd)))
attribute [local irreducible] endpoint qIntegral primitive
lemma ca_endpoint {X : Type} [Primcodable X] {t : X → ℚ} {l i : X → ℕ}
    (ht : Computable t) (hl : Computable l) (hi : Computable i) :
    Computable (fun x=>endpoint (t x) (l x) (i x)) := by
  have hh := @Computable.comp X (ℚ × ℕ × ℕ) ℚ _ _ _ _ _ c_endpoint (ht.pair (hl.pair hi))
  exact hh.of_eq (by intro x; rfl)
lemma ca_qIntegral {X : Type} [Primcodable X] {r : X → ℕ} {a b : X → ℚ}
    (hr : Computable r) (ha : Computable a) (hb : Computable b) :
    Computable (fun x=>qIntegral (r x) (a x) (b x)) := by
  have hh := @Computable.comp X (ℕ × ℚ × ℚ) ℚ _ _ _ _ _ c_qIntegral (hr.pair (ha.pair hb))
  exact hh.of_eq (by intro x; rfl)
lemma c_midpoint : Computable (fun p : ℚ × ℕ × ℕ=>midpoint p.1 p.2.1 p.2.2) := by
  unfold FiniteGaussian.midpoint
  exact ca_ratDiv (ca_ratAdd c_endpoint
    (ca_endpoint Computable.fst (Computable.fst.comp Computable.snd)
      (ca_add (Computable.snd.comp Computable.snd) (ca_const 1)))) (ca_const 2)
lemma c_rawCellWeight : Computable (fun p : GridData × ℕ=>
    qIntegral p.1.r (endpoint p.1.T p.1.L p.2) (endpoint p.1.T p.1.L (p.2+1)) /
      qIntegral p.1.r (-p.1.T) p.1.T) := by
  have hr:=c_gridData_r.comp (Computable.fst (α:=GridData) (β:=ℕ))
  have ht:=ca_ratCast (c_gridData_T.comp (Computable.fst (α:=GridData) (β:=ℕ)))
  have hl:=c_gridData_L.comp (Computable.fst (α:=GridData) (β:=ℕ))
  have he : Computable (fun p : GridData × ℕ=>endpoint p.1.T p.1.L p.2) :=
    ca_endpoint ht hl Computable.snd
  have he' : Computable (fun p : GridData × ℕ=>endpoint p.1.T p.1.L (p.2+1)) :=
    ca_endpoint ht hl (ca_add Computable.snd (ca_const 1))
  have ha : Computable (fun p : GridData × ℕ=>qIntegral p.1.r
      (endpoint p.1.T p.1.L p.2) (endpoint p.1.T p.1.L (p.2+1))) :=
    ca_qIntegral hr he he'
  have hb : Computable (fun p : GridData × ℕ=>qIntegral p.1.r (-p.1.T) p.1.T) :=
    ca_qIntegral hr (computable_ratNeg.comp ht) ht
  exact ca_ratDiv ha hb

namespace Grid
open UEncoding MinUncut.Inner
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def coordinates : UEncoding P (fun p=>TestCoordinates (m p) (n p)) :=
  (Face.points m n hm hn).sum ((Face.points m n hm hn).sum (Face.codes m n hm hn hnpos))
def cells := fin (fun p=>(g p).L) (c_gridData_L.comp hg)
def samples := (coordinates m n hm hn hnpos).function (cells g hg)
lemma out_midpoint : (cells g hg).Out (fun p i=>midpoint (g p).T (g p).L i.val) :=
  ((out_const _ (ca_ratCast (c_gridData_T.comp hg))).pair
    ((out_const _ (c_gridData_L.comp hg)).pair (out_code (cells g hg)))).map c_midpoint
lemma out_cellWeight : (cells g hg).Out (fun p i=>cellWeight (g p).r (g p).T (g p).L i) :=
  ((out_const _ hg).pair (out_code (cells g hg))).map c_rawCellWeight
lemma out_gridWeight : (samples m n hm hn hnpos g hg).Out (fun p q=>gridWeight (g p) q) := by
  let a:=samples m n hm hn hnpos g hg
  let i:=coordinates m n hm hn hnpos
  exact out_prod ((out_cellWeight g hg).comp (map_apply (map_fst a i) (map_snd a i))) computable_ratMul
end Grid
end MinUncut.Preprocess

namespace MinUncut.Preprocess.Grid
open MinUncut.Inner MinUncut.FiniteGaussian UEncoding
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def indices := bool.prod (Face.codes m n hm hn hnpos)
variable {Γ : P → Type} {c : UEncoding P Γ}
lemma out_coord {q : ∀p,Γ p → TestCoordinates (m p) (n p) → Fin (g p).L}
    {i : ∀p,Γ p → TestCoordinates (m p) (n p)}
    (hq : c.Map (samples m n hm hn hnpos g hg) q)
    (hi : c.Map (coordinates m n hm hn hnpos) i) :
    c.Out (fun p x=>midpoint (g p).T (g p).L (q p x (i p x))) :=
  (out_midpoint g hg).comp (map_apply hq hi)
lemma out_sign {z : ∀p,Γ p → Code (m p) (n p)} {i : ∀p,Γ p → Point (m p) (n p)}
    (hz : c.Map (Face.codes m n hm hn hnpos) z) (hi : c.Map (Face.points m n hm hn) i) :
    c.Out (fun p x=>qSign ((z p x).val (i p x))) :=
  (out_field c (map_apply (map_comp hz (Face.map_codeVal m n hm hn hnpos)) hi)).map
    (Primrec.dom_finite qSign).to_comp
lemma out_scoreSummand (σ : P → ℚ) (hσ : Computable σ) :
    (((samples m n hm hn hnpos g hg).prod (indices m n hm hn hnpos)).prod (Face.points m n hm hn)).Out
      (fun p x=>(midpoint (g p).T (g p).L (x.1.1 (.inl x.2))+
        (if x.1.2.1 then σ p else 0)*midpoint (g p).T (g p).L (x.1.1 (.inr (.inl x.2))))*
        qSign (x.1.2.2.val x.2)) := by
  let s:=samples m n hm hn hnpos g hg
  let z:=indices m n hm hn hnpos
  let pt:=Face.points m n hm hn
  let c:=(s.prod z).prod pt
  have hq : c.Map s (fun _ x=>x.1.1) := (map_fst _ _).first
  have hz : c.Map z (fun _ x=>x.1.2) := (map_snd _ _).first
  have hi : c.Map pt (fun _ x=>x.2) := map_snd _ _
  have hx := out_coord m n hm hn hnpos g hg hq
    (map_comp hi (map_inl pt (pt.sum (Face.codes m n hm hn hnpos))))
  have hy := out_coord m n hm hn hnpos g hg hq
    (map_comp (map_comp hi (map_inl pt (Face.codes m n hm hn hnpos)))
      (map_inr pt (pt.sum (Face.codes m n hm hn hnpos))))
  have hs : c.Out (fun p x=>if x.1.2.1 then σ p else 0) :=
    Out.cond (map_comp hz (map_fst _ _)) (out_const _ hσ) (out_const _ (ca_const 0))
  exact (hx.ratAdd (hs.ratMul hy)).ratMul
    (out_sign m n hm hn hnpos (map_comp hz (map_snd _ _)) hi)
lemma map_scoreTable (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    ((samples m n hm hn hnpos g hg).prod (indices m n hm hn hnpos)).Map bool
      (fun p x=>rationalScoreTable (σ p) (η p)
        (fun i=>midpoint (g p).T (g p).L (x.1 i)) x.2) := by
  let s:=samples m n hm hn hnpos g hg
  let z:=indices m n hm hn hnpos
  let pt:=Face.points m n hm hn
  let co:=Face.codes m n hm hn hnpos
  let c:=s.prod z
  have hq : c.Map s (fun _ x=>x.1) := map_fst _ _
  have hz : c.Map z (fun _ x=>x.2) := map_snd _ _
  have hc : c.Map co (fun _ x=>x.2.2) := map_comp hz (map_snd _ _)
  have hy := out_coord m n hm hn hnpos g hg hq
    (map_comp (map_comp hc (map_inr pt co)) (map_inr pt (pt.sum co)))
  have he : c.Out (fun p x=>if x.2.1 then η p else 0) :=
    Out.cond (map_comp hz (map_fst _ _)) (out_const _ hη) (out_const _ (ca_const 0))
  exact (out_sum (out_scoreSummand m n hm hn hnpos g hg σ hσ) computable_ratAdd).algebraicNonneg
    (he.ratMul hy) (out_const _ (ca_pow hn hm))
end MinUncut.Preprocess.Grid

namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian MinUncut.Outer
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open scoped BigOperators
attribute [local irreducible] gridWeight
namespace UEncoding
variable {P X : Type} [Primcodable P] [Primcodable X] {A : P → Type}
lemma Out.unit {f : P → X} (hf : (fixed (P:=P) Encoding.unit).Out (fun p _=>f p)) : Computable f := by
  obtain ⟨g,hg,hh⟩:=hf
  exact (hg.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>hh p ())
lemma computable_prod [CommMonoid X] (a : UEncoding P A) [∀p,Fintype (A p)]
    {f : ∀p,A p → X} (hf : a.Out f) (hmul : Computable₂ (fun x y : X=>x*y)) :
    Computable (fun p=>∏x,f p x) := (out_prod hf.second hmul).unit
end UEncoding
abbrev tests (P : Type) [Primcodable P] : UEncoding P (fun _=>Test) :=
  fixed SampleEnumeration.tests.encoding
instance primcodableTest : Primcodable Test :=
  Primcodable.ofEquiv (Fin SampleEnumeration.tests.encoding.size) SampleEnumeration.tests.encoding.code
namespace Weights
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def localSamples := (Alphabet.arrays t ht h hc m n hm hn hnpos).prod
  ((Alphabet.arrays t ht h hc m n hm hn hnpos).prod ((Face.codes m n hm hn hnpos).prod
    (Grid.samples m n hm hn hnpos g hg)))
lemma out_rationalRowDensity (a : P → ℚ) (ha : Computable a) :
    ((Alphabet.forms t ht h hc).prod (Alphabet.forms t ht h hc)).Out
      (fun p x=>RowNoise.rationalRowDensity (a p) x.1 x.2) := by
  classical
  let c:=(Alphabet.forms t ht h hc).prod (Alphabet.forms t ht h hc)
  have hc' : Computable (fun p=>Fintype.card (Forms (LocalTemplate.Alphabet (h p)))) :=
    computableCard (Alphabet.forms t ht h hc)
  have hi : c.Out (fun p x=>if x.2=x.1 then (Fintype.card (Forms (LocalTemplate.Alphabet (h p))):ℚ) else 0) := by
    apply (Out.cond (map_bool_eq (map_snd _ _) (map_fst _ _))
      (out_const c (ca_ratCast hc')) (out_const c (ca_const 0))).ofEq
    intro p x
    simp only [decide_eq_true_eq]
  exact ((out_const c (ca_const 1)).ratSub (out_const c ha)).ratMul hi |>.ratAdd (out_const c ha)
lemma out_rationalDensity (a : P → ℚ) (ha : Computable a) :
    ((Alphabet.arrays t ht h hc m n hm hn hnpos).prod (Alphabet.arrays t ht h hc m n hm hn hnpos)).Out
      (fun p x=>RowNoise.rationalDensity (a p) x.1 x.2) := by
  let ar:=Alphabet.arrays t ht h hc m n hm hn hnpos
  let ro:=Face.rows m n hm hn hnpos
  have hb : ((ar.prod ar).prod ro).Map ar (fun _ x=>x.1.1) := (map_fst _ _).first
  have hc' : ((ar.prod ar).prod ro).Map ar (fun _ x=>x.1.2) := (map_snd _ _).first
  have hr : ((ar.prod ar).prod ro).Map ro (fun _ x=>x.2) := map_snd _ _
  exact out_prod ((out_rationalRowDensity t ht h hc a ha).comp
    (map_pair (map_apply hb hr) (map_apply hc' hr))) computable_ratMul
lemma out_noiseWeight (a : P → ℚ) (ha : Computable a) :
    (((Alphabet.arrays t ht h hc m n hm hn hnpos).prod
      (Alphabet.arrays t ht h hc m n hm hn hnpos)).prod (tests P)).Out
      (fun p x=>noiseWeight (a p) x.1.1 x.1.2 x.2) := by
  let ar:=Alphabet.arrays t ht h hc m n hm hn hnpos
  let c:=(ar.prod ar).prod (tests P)
  have he : c.Map bool (fun _ x=>decide (x.2=Test.second)) :=
    map_fixed_apply SampleEnumeration.tests.encoding Encoding.bool (fun j=>decide (j=Test.second)) (map_snd _ _)
  exact (Out.cond he (out_rationalDensity t ht h hc m n hm hn hnpos a ha).first
    (out_const c (ca_const 1))).ofEq (by
      intro p x
      cases x.2 <;> simp only [noiseWeight,reduceCtorEq,decide_true,decide_false,Bool.false_eq_true,ite_false,ite_true]
      unfold RowNoise.rationalDensity
      apply Finset.prod_congr rfl
      intro r _
      unfold RowNoise.rationalRowDensity
      split_ifs <;> rfl)
lemma out_localWeight (a b : P → ℚ) (ha : Computable a) (hb : Computable b) :
    ((localSamples t ht h hc m n hm hn hnpos g hg).prod (tests P)).Out
      (fun p x=>localWeight (g p) (a p) (b p) x.2 x.1) := by
  let s:=localSamples t ht h hc m n hm hn hnpos g hg
  let c:=s.prod (tests P)
  let ar:=Alphabet.arrays t ht h hc m n hm hn hnpos
  have har : Computable (fun p=>(Fintype.card (FaceArray (LocalTemplate.Alphabet (h p)) (m p) (n p)):ℚ)⁻¹) :=
    computable_ratInv.comp (ca_ratCast (computableCard ar))
  have hco : Computable (fun p=>(Fintype.card (Code (m p) (n p)):ℚ)⁻¹) :=
    computable_ratInv.comp (ca_ratCast (computableCard (Face.codes m n hm hn hnpos)))
  have hs : c.Map s (fun _ x=>x.1) := map_fst _ _
  have hB : c.Map ar (fun _ x=>x.1.1) := map_comp hs (map_fst _ _)
  have hC : c.Map ar (fun _ x=>x.1.2.1) := map_comp (map_comp hs (map_snd _ _)) (map_fst _ _)
  have hq : c.Map (Grid.samples m n hm hn hnpos g hg) (fun _ x=>x.1.2.2.2) :=
    map_comp (map_comp (map_comp hs (map_snd _ _)) (map_snd _ _)) (map_snd _ _)
  exact ((((out_const c har).ratMul (out_const c har)).ratMul (out_const c hco)).ratMul
    ((Grid.out_gridWeight m n hm hn hnpos g hg).comp hq)).ratMul
      ((out_noiseWeight t ht h hc m n hm hn hnpos a ha).comp
        (map_pair (map_pair hB hC) (map_snd _ _))) |>.ratDiv (out_const c hb)
end Weights
namespace Denominator
variable {P : Type} [Primcodable P]
variable (t m n : P → ℕ) (ht : Computable t) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
include ht hm hn hnpos in
lemma c_faceCardBound : Computable (fun p=>faceCardBound (t p) (m p) (n p)) :=
  ca_pow (ca_pow (ca_const 2) (ca_pow (ca_const 2) (ca_mul (ca_const 3) ht)))
    (computableCard (Face.rows m n hm hn hnpos))
include hm hn hnpos hg in
lemma c_gridDenominator : Computable (fun p=>gridDenominator (m p) (n p) (g p)) := by
  let a : UEncoding P (fun p=>TestCoordinates (m p) (n p) → Fin (g p).L) :=
    Grid.samples m n hm hn hnpos g hg
  have hw : a.Out (fun p q=>(gridWeight (g p) q).den) :=
    (Grid.out_gridWeight m n hm hn hnpos g hg).map primrec_ratDen.to_comp
  have hh := @computable_prod P ℕ _ _ (fun p=>TestCoordinates (m p) (n p) → Fin (g p).L)
    _ a (fun _=>inferInstance) _ hw Primrec.nat_mul.to_comp
  apply hh.of_eq
  intro p
  unfold gridDenominator
  apply Finset.prod_congr (by ext; simp)
  intro q _
  rfl
lemma c_budgetDenominator (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j)) :
    Computable (fun p=>budgetDenominator (b p)) :=
  computable_prod _ (hb.ratInv.map primrec_ratDen.to_comp) Primrec.nat_mul.to_comp
include ht hm hn hnpos hg in
lemma c_innerDenominator (a : P → ℚ) (ha : Computable a)
    (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j)) :
    Computable (fun p=>innerDenominator (t p) (m p) (n p) (g p) (a p) (b p)) := by
  exact ca_mul (ca_mul (ca_mul (ca_mul (ca_mul
    (ca_factorial (c_faceCardBound t m n ht hm hn hnpos))
    (ca_factorial (c_faceCardBound t m n ht hm hn hnpos)))
    (computableCard (Face.codes m n hm hn hnpos)))
    (c_gridDenominator m n hm hn hnpos g hg))
    (ca_pow (primrec_ratDen.to_comp.comp ha) (computableCard (Face.rows m n hm hn hnpos))))
    (c_budgetDenominator b hb)
end Denominator

open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
namespace UEncoding
variable {P : Type} [Primcodable P] {A B : P → Type}
lemma map_testCases {c : UEncoding P A} {b : UEncoding P B} {j : ∀p,A p → Test}
    {f₁ f₂ f₃ f₄ : ∀p,A p → B p} (hj : c.Map (tests P) j)
    (h₁ : c.Map b f₁) (h₂ : c.Map b f₂) (h₃ : c.Map b f₃) (h₄ : c.Map b f₄) :
    c.Map b (fun p x=>match j p x with
      | .first => f₁ p x | .second => f₂ p x | .third => f₃ p x | .fourth => f₄ p x) := by
  have hq (k : Test) : c.Map bool (fun p x=>decide (j p x=k)) :=
    map_fixed_apply SampleEnumeration.tests.encoding Encoding.bool (fun l=>decide (l=k)) hj
  apply (map_cond (hq .first) h₁ (map_cond (hq .second) h₂ (map_cond (hq .third) h₃ h₄))).ofEq
  intro p x
  cases j p x <;> rfl
end UEncoding
namespace Queries
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
def table := (Alphabet.labels t ht h hc).function (bool (P:=P))
def queryEquiv (p : P) : Query (h p) ≃ Bool × (Alphabet (h p) → Bool) × (Alphabet (h p) → Bool) where
  toFun q := (q.first,q.left,q.right)
  invFun q := ⟨q.1,q.2.1,q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def queries : UEncoding P (fun p=>Query (h p)) :=
  (bool.prod ((table t ht h hc).prod (table t ht h hc))).ofEquiv (queryEquiv t h)
lemma map_first : (queries t ht h hc).Map bool (fun _ q=>q.first) := by
  have hh:=map_comp (map_to (bool.prod ((table t ht h hc).prod (table t ht h hc))) (queryEquiv t h)) (map_fst _ _)
  exact hh
lemma map_left : (queries t ht h hc).Map (table t ht h hc) (fun _ q=>q.left) := by
  have hh:=map_comp (map_comp (map_to (bool.prod ((table t ht h hc).prod (table t ht h hc))) (queryEquiv t h)) (map_snd _ _)) (map_fst _ _)
  exact hh
lemma map_right : (queries t ht h hc).Map (table t ht h hc) (fun _ q=>q.right) := by
  have hh:=map_comp (map_comp (map_to (bool.prod ((table t ht h hc).prod (table t ht h hc))) (queryEquiv t h)) (map_snd _ _)) (map_snd _ _)
  exact hh

variable {Γ : P → Type} {c : UEncoding P Γ}
variable {B C : ∀p,Γ p → FaceArray (Alphabet (h p)) (m p) (n p)}
variable {z : ∀p,Γ p → Code (m p) (n p)} {s : ∀p,Γ p → ScoreIndex (m p) (n p) → Bool}
variable {j : ∀p,Γ p → Test}
variable (hB : c.Map (Alphabet.arrays t ht h hc m n hm hn hnpos) B)
variable (hC : c.Map (Alphabet.arrays t ht h hc m n hm hn hnpos) C)
variable (hz : c.Map (Face.codes m n hm hn hnpos) z)
variable (hs : c.Map ((Grid.indices m n hm hn hnpos).function bool) s)
variable (hj : c.Map (tests P) j)
include hB hC hz hs hj in
lemma map_leftEval {a : ∀p,Γ p → Alphabet (h p)} (ha : c.Map (Alphabet.labels t ht h hc) a) :
    c.Map bool (fun p x=>(query (h p) (B p x) (C p x) (z p x) (s p x) (j p x)).left (a p x)) := by
  have hba := map_comp (map_pair hB ha) (Alphabet.map_labelCode t ht h hc m n hm hn hnpos)
  have hca := map_comp (map_pair hC ha) (Alphabet.map_labelCode t ht h hc m n hm hn hnpos)
  have hfalse : c.Map bool (fun _ _=>false) := map_const (Computable.const 0)
  have htrue : c.Map bool (fun _ _=>true) := map_const (Computable.const 1)
  have ha₀ := map_apply hs (map_pair hfalse hba)
  have ha₁ := map_apply hs (map_pair htrue hba)
  have ha₂ := map_apply hs (map_pair htrue hca)
  have ha₃ := map_cond (map_bool_eq hba hz) htrue ha₁
  apply (map_testCases hj ha₀ ha₁ ha₃ ha₂).ofEq
  intro p x
  cases j p x <;> simp only [LocalTemplate.query]
  · change (if decide (labelCode (B p x) (a p x)=z p x) then true else _) = _
    simp only [decide_eq_true_eq,Function.update_apply]
include hB hC hz hs hj in
lemma map_rightEval {a : ∀p,Γ p → Alphabet (h p)} (ha : c.Map (Alphabet.labels t ht h hc) a) :
    c.Map bool (fun p x=>(query (h p) (B p x) (C p x) (z p x) (s p x) (j p x)).right (a p x)) := by
  have hba := map_comp (map_pair hB ha) (Alphabet.map_labelCode t ht h hc m n hm hn hnpos)
  have hca := map_comp (map_pair hC ha) (Alphabet.map_labelCode t ht h hc m n hm hn hnpos)
  have hfalse : c.Map bool (fun _ _=>false) := map_const (Computable.const 0)
  have htrue : c.Map bool (fun _ _=>true) := map_const (Computable.const 1)
  have ha₁ := map_apply hs (map_pair htrue hba)
  have ha₂ := map_apply hs (map_pair htrue hca)
  have ha₃ := map_cond (map_bool_eq hba hz) hfalse ha₁
  apply (map_testCases hj ha₁ ha₂ ha₃ ha₂).ofEq
  intro p x
  cases j p x <;> simp only [LocalTemplate.query]
  · change (if decide (labelCode (B p x) (a p x)=z p x) then false else _) = _
    simp only [decide_eq_true_eq,Function.update_apply]
include hB hC hz hs hj in
lemma map_query : c.Map (queries t ht h hc)
    (fun p x=>query (h p) (B p x) (C p x) (z p x) (s p x) (j p x)) := by
  have hl := map_lambda (map_leftEval t ht h hc m n hm hn hnpos hB.first hC.first hz.first hs.first hj.first (map_snd _ _))
  have hr := map_lambda (map_rightEval t ht h hc m n hm hn hnpos hB.first hC.first hz.first hs.first hj.first (map_snd _ _))
  have hf : c.Map bool (fun p x=> (query (h p) (B p x) (C p x) (z p x) (s p x) (j p x)).first) := by
    apply (map_fixed_apply SampleEnumeration.tests.encoding Encoding.bool (fun j=>decide (j=Test.fourth)) hj).ofEq
    intro p x
    cases j p x <;> rfl
  exact map_comp (map_pair hf (map_pair hl hr)) (map_from _ (queryEquiv t h))
end Queries
end MinUncut.Preprocess

namespace MinUncut.Preprocess.Queries
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable {Γ : P → Type} {c : UEncoding P Γ}
variable {Q : ∀p,Γ p → Query (h p)} {pos : ∀p,Γ p → Fin (t p) → Fin 3}
variable {sig : ∀p,Γ p → Signature (Fin (t p))} {x : ∀p,Γ p → Fin (t p) → Triple}
variable (hQ : c.Map (queries t ht h hc) Q) (hp : c.Map (Alphabet.positionsList t ht) pos)
variable (hs : c.Map (Alphabet.signatures t ht) sig)
lemma zero_map : c.Map (Alphabet.labels t ht h hc) (fun _ _=>0) := by
  have hunit : c.Map (fixed Encoding.unit) (fun _ _=>()) := map_const (Computable.const 0)
  have hh := map_comp hunit (Alphabet.map_zeroLabel t ht h hc)
  exact hh
include hQ hp hs in
lemma map_leftBase : c.Map bool (fun p a=>(Q p a).leftBase (pos p a) (sig p a)) := by
  have hf:=map_comp hQ (map_first t ht h hc)
  have hl:=map_comp hQ (map_left t ht h hc)
  have ho:=map_comp hs (Alphabet.map_origin t ht)
  have hz:=map_comp (map_pair hp ho) (Alphabet.map_project t ht h hc)
  exact map_cond hf (map_apply hl hz) (map_apply hl (zero_map t ht h hc))
include hQ hp hs in
lemma map_leftTableEval (hx : c.Map (Alphabet.ambient t ht) x) :
    c.Map bool (fun p a=>(Q p a).leftTable (pos p a) (sig p a) (x p a)) := by
  have hf:=map_comp hQ (map_first t ht h hc)
  have hl:=map_comp hQ (map_left t ht h hc)
  have hv:=map_comp (map_pair hs hx) (Alphabet.map_valid t ht)
  have hproj:=map_comp (map_pair hp hx) (Alphabet.map_project t ht h hc)
  have hd:=map_comp hx (Alphabet.map_decode t ht h hc)
  have hfalse : c.Map bool (fun _ _=>false) := map_const (Computable.const 0)
  have hbase:=map_leftBase t ht h hc hQ hp hs
  have hzero:=map_apply hl (zero_map t ht h hc)
  apply (map_cond hf (map_cond hv (map_bool_eq hbase (map_apply hl hproj)) hfalse)
    (map_bool_eq hzero (map_apply hl hd))).ofEq
  intro p a
  simp only [Query.leftTable, Bool.beq_eq_decide_eq]
  split_ifs <;> simp_all only [decide_eq_true_eq, ite_true, ite_false]
include hQ in
lemma map_rightTableEval (hx : c.Map (Alphabet.ambient t ht) x) :
    c.Map bool (fun p a=>(Q p a).rightTable (x p a)) := by
  have hr:=map_comp hQ (map_right t ht h hc)
  have hd:=map_comp hx (Alphabet.map_decode t ht h hc)
  apply (map_bool_eq (map_apply hr (zero_map t ht h hc)) (map_apply hr hd)).ofEq
  intro p a
  simp only [Query.rightTable, Bool.beq_eq_decide_eq]
include hQ hp hs in
lemma map_localSign : c.Map bool (fun p a=>(Q p a).localSign (pos p a) (sig p a)) := by
  have hr:=map_comp hQ (map_right t ht h hc)
  apply (map_bool_eq (map_leftBase t ht h hc hQ hp hs) (map_apply hr (zero_map t ht h hc))).ofEq
  intro p a
  simp only [Query.localSign, Bool.beq_eq_decide_eq]
include hQ hp hs in
lemma map_leftTable : c.Map ((Alphabet.ambient t ht).function bool)
    (fun p a=>(Q p a).leftTable (pos p a) (sig p a)) :=
  map_lambda (map_leftTableEval t ht h hc hQ.first hp.first hs.first (map_snd _ _))
include hQ in
lemma map_rightTable : c.Map ((Alphabet.ambient t ht).function bool)
    (fun p a=>(Q p a).rightTable) :=
  map_lambda (map_rightTableEval t ht h hc hQ.first (map_snd _ _))
end MinUncut.Preprocess.Queries

open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction MinUncut.SourceBridge

def signatureExpr (t : ℕ) : AExpr :=
  AExpr.add
    (AExpr.sum (List.ofFn fun i : Fin t =>
      AExpr.mul
        (AExpr.sum (List.ofFn fun p : Fin 3 =>
          AExpr.mul
            (AExpr.sum (List.ofFn fun q : Fin 3 =>
              AExpr.mul (.eq (slotExpr i.val p.val) (slotExpr i.val q.val))
                (.const (2^q.val))))
            (.const ((2^3)^p.val))))
        (.const (((2^3)^3)^i.val))))
    (.mul (.const (((2^3)^3)^t))
      (.sum (List.ofFn fun i : Fin t=> .mul (slotExpr i.val 3) (.const (2^i.val)))))

lemma signatureExpr_eval {t : ℕ} (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) :
    (signatureExpr t).eval (inputTuple input u)=
      ((signatureEncoding t).code (signature (fun j=>equations input (u j)))).val := by
  rw [signature_code]
  simp only [signatureExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_name,slotExpr_rhs,signatureNumber,signature]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  by_cases h : (equations input (u i)).names p=(equations input (u i)).names q
  · simp only [h,decide_true,Bool.toNat_true,ite_true]
  · have h' : ((equations input (u i)).names p).val≠((equations input (u i)).names q).val :=
      fun e=>h (Fin.ext e)
    simp only [h,h',decide_false,Bool.toNat_false,ite_false]

def signatureLookup {t : ℕ} (f : Signature (Fin t) → ℕ) : AExpr :=
  (signatureExpr t).lookup (constantTable (signatureEncoding t) f)
lemma signatureLookup_eval {t : ℕ} (input : SourceEncoding.Input)
    (u : Fin t → Fin input.equations.length) (f : Signature (Fin t) → ℕ) :
    (signatureLookup f).eval (inputTuple input u)=f (signature (fun j=>equations input (u j))) := by
  exact constantTable_eval _ _ _ _ _ (signatureExpr_eval input u)

end MinUncut.Costed.SourceWords

end

end OAI
