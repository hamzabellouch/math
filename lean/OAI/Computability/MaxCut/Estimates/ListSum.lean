import Mathlib
import OAI.Computability.MaxCut.Encoding.BitValue
import OAI.Computability.MaxCut.Estimates.Divides

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def listSum {I : Type} (l : List I) (f : I → Expr) : Expr :=
  l.foldr (fun i s => .add (f i) s) (.const 0)
@[simp] theorem listSum_eval {I : Type} (l : List I) (f : I → Expr)
    (input : List Bool) (args : ℕ → ℕ) :
    (listSum l f).eval input args = (l.map (fun i => (f i).eval input args)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (f i).eval input args + (listSum l f).eval input args = _
    simp [ih]

noncomputable def finiteSum {I : Type} [Fintype I] (f : I → Expr) : Expr :=
  listSum Finset.univ.toList f
@[simp] theorem finiteSum_eval {I : Type} [Fintype I] (f : I → Expr)
    (input : List Bool) (args : ℕ → ℕ) :
    (finiteSum f).eval input args = ∑ i, (f i).eval input args := by
  simp [finiteSum]

/-- First successful bounded index. All searches are expanded into finite
counter loops, so the certificate does not postulate a search operation. -/
def least (bound predicate : Expr) : Expr :=
  .sum bound (.mul (.arg 0) (.mul (positive predicate)
    (.zero (.sum (.arg 0) (positive (predicate.rename (fun
      | 0 => 0
      | j+1 => j+2)))))))

 theorem least_eval (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (least bound predicate).eval input args =
      ∑ i ∈ range (bound.eval input args),
        if predicate.eval input (bind args i) ≠ 0 ∧
          ∀ j < i, predicate.eval input (bind args j) = 0 then i else 0 := by
  have hb (i j : ℕ) : (fun k => bind (bind args i) j (match k with
      | 0 => 0
      | k+1 => k+2)) = bind args j := by
    funext k; cases k <;> rfl
  simp only [least, eval, positive_eval, rename_eval, hb]
  apply sum_congr rfl
  intro i hi
  have hz : (∑ j ∈ range i,
      if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0) = 0 ↔
      ∀ j < i, predicate.eval input (bind args j)=0 := by
    simp only [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _), mem_range]
    simp
  change i * ((if predicate.eval input (bind args i) ≠ 0 then 1 else 0) *
    (if (∑ j ∈ range i, if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0)=0 then 1 else 0)) = _
  simp only [hz]
  rw [indicator_and]
  split_ifs <;> simp

end OptimalMaxCut.CounterMachine.Expr

namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem least_eq (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) (k : ℕ)
    (hk : k < bound.eval input args)
    (hp : predicate.eval input (bind args k) ≠ 0)
    (he : ∀ j < k, predicate.eval input (bind args j) = 0) :
    (least bound predicate).eval input args = k := by
  rw [least_eval, sum_eq_single_of_mem k (mem_range.mpr hk)]
  · exact ite_eq_left ⟨hp, he⟩
  · intro j hj hne
    by_cases h : j < k
    · simp [he j h]
    · have hkj : k < j := by omega
      split_ifs with hgood
      · exact False.elim (hp (hgood.2 k hkj))
      · rfl

end OptimalMaxCut.CounterMachine.Expr
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def Represented (f : List Bool → (ℕ → ℕ) → ℕ) : Prop :=
  ∃ e : Expr, ∀ input args, e.eval input args = f input args

namespace Represented
variable {f g h : List Bool → (ℕ → ℕ) → ℕ}
theorem const (n : ℕ) : Represented (fun _ _ => n) := ⟨.const n, by intros; rfl⟩
theorem arg (k : ℕ) : Represented (fun _ a => a k) := ⟨.arg k, by intros; rfl⟩
theorem word (hf : Represented f) : Represented (fun s a => wordValue s (f s a)) := by
  obtain ⟨e,he⟩ := hf; exact ⟨Expr.word e, by intros; simp [he]⟩
theorem add (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a+g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.add e d, by intros; simp [eval,he,hd]⟩
theorem sub (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a-g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.sub e d, by intros; simp [eval,he,hd]⟩
theorem mul (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a*g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.mul e d, by intros; simp [eval,he,hd]⟩
theorem div (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a/g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨quotient e d, by intros; simp [he,hd]⟩
theorem mod (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a%g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨remainder e d, by intros; simp [he,hd]⟩
theorem pow (hf : Represented f) (n : ℕ) : Represented (fun s a => f s a^n) := by
  obtain ⟨e,he⟩ := hf; exact ⟨power e n, by intros; simp [he]⟩
theorem eq (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if f s a=g s a then 1 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨equal e d, by intros; simp [he,hd]⟩
theorem lt (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if f s a<g s a then 1 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨Expr.lt e d, by intros; simp [he,hd]⟩
theorem cond (hf : Represented f) (hg : Represented g) (hh : Represented h) :
    Represented (fun s a => if f s a ≠ 0 then g s a else h s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; obtain ⟨c,hc⟩ := hh
  exact ⟨Expr.cond e d c, by intros; simp [he,hd,hc]⟩
theorem sum (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => ∑ i ∈ range (f s a), g s (bind a i)) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.sum e d, by intros; simp [eval,he,hd]⟩
theorem finiteSum {I : Type} [Fintype I] {f : I → List Bool → (ℕ → ℕ) → ℕ}
    (hf : ∀ i, Represented (f i)) : Represented (fun s a => ∑ i, f i s a) := by
  choose e he using hf
  exact ⟨Expr.finiteSum e, by intros; simp [he]⟩
theorem rename (hf : Represented f) (r : ℕ → ℕ) :
    Represented (fun s a => f s (fun k => a (r k))) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e.rename r, by intros; simp [he]⟩
theorem subst (hf : Represented f) {v : ℕ → List Bool → (ℕ → ℕ) → ℕ}
    (hv : ∀ k, Represented (v k)) : Represented (fun s a => f s (fun k => v k s a)) := by
  obtain ⟨e,he⟩ := hf; choose d hd using hv
  exact ⟨e.subst d, by intros; simp [he,hd]⟩
theorem congr (hf : Represented f) (h : ∀ s a, f s a=g s a) : Represented g := by
  obtain ⟨e,he⟩ := hf; exact ⟨e, fun s a => (he s a).trans (h s a)⟩
end Represented
end OptimalMaxCut.CounterMachine.Expr
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted
attribute [local instance] Classical.propDecidable

 theorem roundedWeights_integer {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (endpoints : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) (u v : Fin N) :
    roundedWeights p endpoints v0 P hP u v =
      if u=v then 0 else
        ((∑ i : I, ((if endpoints i = (u,v) then ⌊(P:ℚ)*p.weight i⌋₊ else 0) +
          (if endpoints i = (v,u) then ⌊(P:ℚ)*p.weight i⌋₊ else 0)) : ℕ) : ℚ) / P := by
  by_cases huv : u=v
  · simp [roundedWeights, aggregate, huv]
  · simp only [roundedWeights, aggregate, huv, ↓reduceIte, Law.push, Fintype.sum_option,
      Law.grid, Law.gridWeight]
    have hn : (v0,v0) ≠ (u,v) := by rintro ⟨⟩; exact huv rfl
    have hn' : (v0,v0) ≠ (v,u) := by rintro ⟨⟩; exact huv rfl
    simp only [hn, hn', ↓reduceIte, zero_add, Nat.cast_sum, Nat.cast_add]
    rw [Finset.sum_add_distrib, add_div, Finset.sum_div, Finset.sum_div]
    congr 1 <;> (apply Finset.sum_congr rfl; intro i hi; split_ifs <;> simp)

namespace InstanceAdapter
variable {q : ℕ}

def degree (g : MaxCutGames.Foundations.Target.Instance q) (y : Fin g.vertices) : ℕ :=
  ∑ e : Fin g.constraints.length, if g.constraints[e].target = y then 1 else 0

 theorem degree_eq (g : MaxCutGames.Foundations.Target.Instance q) (y : Fin g.vertices) :
    degree g y = Law.fiberSize (fun e : Fin g.constraints.length => g.constraints[e].target) y := by
  let : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  simp only [degree, Law.fiberSize_eq_sum, Fin.getElem_fin]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp_all

 theorem sampleLaw_weight (g : MaxCutGames.Foundations.Target.Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (y : Fin g.vertices) (e f : Fin g.constraints.length)
    (x z : Cube (Fin q)) :
    ((ofInstance g).sampleLaw t ht).weight (y,e,f,x,z) =
      if g.constraints[e].target=y ∧ g.constraints[f].target=y then
        (degree g y : ℚ) * (jointLaw t ht q).weight (x,z) /
          ((g.constraints.length:ℚ)*(degree g y:ℚ)^2)
      else 0 := by
  let : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  simp only [Game.sampleLaw, Law.bind, ofInstance, Law.fiberMarginal, Law.fiberConditional,
    Fintype.card_fin, ← degree_eq]
  simp only [Fin.getElem_fin] at *
  by_cases hd : degree g y = 0
  · simp [hd]
  · have hdQ : (degree g y:ℚ) ≠ 0 := by exact_mod_cast hd
    by_cases he : g.constraints[e.val].target=y <;> by_cases hf : g.constraints[f.val].target=y <;>
      simp [hd,he,hf] ; field_simp

end InstanceAdapter
end OptimalMaxCut.LongCode
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open CounterMachine.Expr
attribute [local instance] Classical.propDecidable

/-- Exact unary game codec used by the supplied binary reduction. -/
def rowWords {n q : ℕ} (c : Constraint n q) : List ℕ :=
  [c.source.val,c.target.val] ++ c.permutation.images.toList.map Fin.val
def words {q : ℕ} (g : Instance q) : List ℕ :=
  [g.vertices,q,g.constraints.length] ++ g.constraints.flatMap rowWords
def bits {q : ℕ} (g : Instance q) : List Bool := unaryWords (words g)

@[simp] theorem rowWords_length {n q : ℕ} (c : Constraint n q) :
    (rowWords c).length = q+2 := by simp [rowWords]

theorem flatMap_getD {A B : Type} (l : List A) (f : A → List B) (d : B) (r : ℕ)
    (hf : ∀ a ∈ l, (f a).length=r) (e : Fin l.length) (j : ℕ) (hj : j<r) :
    ((l.flatMap f)[e.val*r+j]?).getD d = ((f l[e])[j]?).getD d := by
  induction l with
  | nil => exact e.elim0
  | cons a l ih =>
    rcases e with ⟨e,he⟩
    simp only [Fin.getElem_fin] at *
    cases e with
    | zero => simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
              rw [List.getElem?_append_left (by simpa [hf a (by simp)] using hj)]
    | succ e =>
      have ha := hf a (by simp)
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [ha]; nlinarith)]
      have hx : (e+1)*r+j-(f a).length=e*r+j := by rw [ha, Nat.add_mul]; omega
      rw [hx]
      exact ih (fun b hb => hf b (by simp [hb])) ⟨e,by simpa using he⟩

theorem word_header {q : ℕ} (g : Instance q) :
    wordValue (bits g) 0 = g.vertices ∧ wordValue (bits g) 1 = q ∧
      wordValue (bits g) 2 = g.constraints.length := by
  simp [bits,wordValue_encoded,words]

theorem word_row {q : ℕ} (g : Instance q) (e : Fin g.constraints.length)
    (j : ℕ) (hj : j<q+2) :
    wordValue (bits g) (3+e.val*(q+2)+j) = ((rowWords g.constraints[e])[j]?).getD 0 := by
  rw [bits, wordValue_encoded]
  simp only [words, List.cons_append, List.nil_append]
  have hx : 3+e.val*(q+2)+j = (e.val*(q+2)+j)+1+1+1 := by omega
  rw [hx]
  simp only [List.getElem?_cons_succ]
  exact flatMap_getD g.constraints rowWords 0 (q+2) (by intros; simp) e j hj

 theorem row_source {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    wordValue (bits g) (3+e.val*(q+2)) = g.constraints[e].source.val := by
  simpa [rowWords] using word_row g e 0 (by omega)
 theorem row_target {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    wordValue (bits g) (3+e.val*(q+2)+1) = g.constraints[e].target.val := by
  simpa [rowWords] using word_row g e 1 (by omega)
 theorem row_image {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) (i : Fin q) :
    wordValue (bits g) (3+e.val*(q+2)+(2+i.val)) = g.constraints[e].permutation.images[i].val := by
  have h := word_row g e (2+i.val) (by omega)
  simpa [rowWords, Nat.add_comm 2] using h

end OptimalMaxCut.LongCode.InstanceAdapter
namespace OptimalMaxCut.CounterMachine.Expr.Represented
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {f g h j : List Bool → (ℕ → ℕ) → ℕ}
theorem iteEq (hf : Represented f) (hg : Represented g) (hh : Represented h) (hj : Represented j) :
    Represented (fun s a => if f s a=g s a then h s a else j s a) := by
  exact (cond (eq hf hg) hh hj).congr (by intros; split_ifs <;> simp_all)
theorem iteAndEq {v w : List Bool → (ℕ → ℕ) → ℕ}
    (hf : Represented f) (hg : Represented g) (hh : Represented h) (hj : Represented j)
    (hv : Represented v) (hw : Represented w) :
    Represented (fun s a => if f s a=g s a ∧ h s a=j s a then v s a else w s a) := by
  exact (cond ((eq hf hg).mul (eq hh hj)) hv hw).congr (by intros; split_ifs <;> simp_all)
theorem indicatorAnd {P Q : List Bool → (ℕ → ℕ) → Prop}
    (hp : Represented (fun s a => if P s a then 1 else 0))
    (hq : Represented (fun s a => if Q s a then 1 else 0)) :
    Represented (fun s a => if P s a ∧ Q s a then 1 else 0) :=
  (hp.mul hq).congr (fun _ _ => indicator_and _ _)
theorem iteProp {P : List Bool → (ℕ → ℕ) → Prop}
    (hp : Represented (fun s a => if P s a then 1 else 0))
    (hh : Represented h) (hj : Represented j) :
    Represented (fun s a => if P s a then h s a else j s a) := by
  exact (cond hp hh hj).congr (by intros; split_ifs <;> simp_all)
theorem bounded {F : List Bool → (ℕ → ℕ) → ℕ → ℕ}
    (hb : Represented f)
    (hF : Represented (fun s a => F s (fun k => a (k+1)) (a 0))) :
    Represented (fun s a => ∑ i ∈ range (f s a), F s a i) := by
  exact (sum hb hF).congr (by intros; rfl)
end OptimalMaxCut.CounterMachine.Expr.Represented

namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open CounterMachine.Expr LongCode
attribute [local instance] Classical.propDecidable

def vertices (s : List Bool) : ℕ := wordValue s 0
def edges (s : List Bool) : ℕ := wordValue s 2
def row (q : ℕ) (s : List Bool) (e j : ℕ) := wordValue s (3+e*(q+2)+j)
def degree (q : ℕ) (s : List Bool) (y : ℕ) :=
  ∑ e ∈ range (edges s), if row q s e 1=y then 1 else 0
def lookup {q : ℕ} (x : Cube (Fin q)) (j : ℕ) : ℕ :=
  ∑ i : Fin q, if i.val=j then (finTwoEquiv.symm (x i)).val else 0
def permCode {q : ℕ} (s : List Bool) (e : ℕ) (x : Cube (Fin q)) : ℕ :=
  ∑ i : Fin q, lookup x (row q s e (2+i.val)) * 2^i.val
def query {q : ℕ} (s : List Bool) (e : ℕ) (x : Cube (Fin q)) : ℕ :=
  permCode s e x+2^q*row q s e 0
def gridSize (q K : ℕ) (s : List Bool) : ℕ :=
  (K+1)*(vertices s * (edges s * (edges s * (2^q*2^q)))+1)
def atom {q : ℕ} (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (s : List Bool) (y e f : ℕ) (x z : Cube (Fin q)) : ℕ :=
  if row q s e 1=y ∧ row q s f 1=y then
    gridSize q K s*degree q s y*((jointLaw t ht q).weight (x,z)).num.toNat /
     (((jointLaw t ht q).weight (x,z)).den*edges s*(degree q s y)^2)
  else 0

noncomputable def weights (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (s : List Bool) (u v : ℕ) : ℕ :=
  if u=v then 0 else
    ∑ y ∈ range (vertices s), ∑ e ∈ range (edges s), ∑ f ∈ range (edges s),
      ∑ x : Cube (Fin q), ∑ z : Cube (Fin q),
        ((if query s e x=u ∧ query s f (antipode z)=v then atom t ht K s y e f x z else 0)+
        (if query s e x=v ∧ query s f (antipode z)=u then atom t ht K s y e f x z else 0))

namespace Rep
open CounterMachine.Expr.Represented
variable {f g h : List Bool → (ℕ → ℕ) → ℕ}
theorem vertices : Represented (fun s _ => RawGrid.vertices s) := word (Represented.const 0)
theorem edges : Represented (fun s _ => RawGrid.edges s) := word (Represented.const 2)
theorem row (q : ℕ) (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => RawGrid.row q s (f s a) (g s a)) :=
  word (((Represented.const 3).add (hf.mul (Represented.const (q+2)))).add hg)
theorem degree (q : ℕ) (hy : Represented f) : Represented (fun s a => RawGrid.degree q s (f s a)) := by
  apply bounded edges
  exact eq (row q (Represented.arg 0) (Represented.const 1)) (hy.rename Nat.succ)
theorem lookup {q : ℕ} (x : Cube (Fin q)) (hj : Represented f) :
    Represented (fun s a => RawGrid.lookup x (f s a)) := by
  exact Represented.finiteSum (fun i => iteEq (Represented.const i.val) hj (Represented.const (finTwoEquiv.symm (x i)).val) (Represented.const 0))
theorem permCode {q : ℕ} (x : Cube (Fin q)) (he : Represented f) :
    Represented (fun s a => RawGrid.permCode s (f s a) x) := by
  exact Represented.finiteSum (fun i => (lookup x (row q he (Represented.const (2+i.val)))).mul (Represented.const (2^i.val)))
theorem query {q : ℕ} (x : Cube (Fin q)) (he : Represented f) :
    Represented (fun s a => RawGrid.query s (f s a) x) :=
  (permCode x he).add ((Represented.const (2^q)).mul (row q he (Represented.const 0)))
theorem gridSize (q K : ℕ) : Represented (fun s _ => RawGrid.gridSize q K s) :=
  (Represented.const (K+1)).mul ((vertices.mul (edges.mul (edges.mul (Represented.const (2^q*2^q))))).add (Represented.const 1))
theorem atom {q : ℕ} (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (x z : Cube (Fin q)) (hy : Represented f) (he : Represented g) (hf : Represented h) :
    Represented (fun s a => RawGrid.atom t ht K s (f s a) (g s a) (h s a) x z) := by
  refine iteAndEq (row q he (Represented.const 1)) hy (row q hf (Represented.const 1)) hy ?_ (Represented.const 0)
  exact ((gridSize q K).mul (degree q hy) |>.mul (Represented.const ((jointLaw t ht q).weight (x,z)).num.toNat)).div
    (((Represented.const ((jointLaw t ht q).weight (x,z)).den).mul edges).mul ((degree q hy).pow 2))

theorem weights (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (hu : Represented f) (hv : Represented g) :
    Represented (fun s a => RawGrid.weights q t ht K s (f s a) (g s a)) := by
  refine iteEq hu hv (Represented.const 0) ?_
  apply bounded vertices
  apply bounded edges
  apply bounded edges
  apply Represented.finiteSum
  intro x
  apply Represented.finiteSum
  intro z
  let hu' := hu.rename (fun j => j+3)
  let hv' := hv.rename (fun j => j+3)
  have hA := atom t ht K x z (Represented.arg 2) (Represented.arg 1) (Represented.arg 0)
  exact (iteAndEq (query x (Represented.arg 1)) hu' (query (antipode z) (Represented.arg 0)) hv' hA (Represented.const 0)).add
    (iteAndEq (query x (Represented.arg 1)) hv' (query (antipode z) (Represented.arg 0)) hu' hA (Represented.const 0))
end Rep
end OptimalMaxCut.RawGrid

end

end OAI
