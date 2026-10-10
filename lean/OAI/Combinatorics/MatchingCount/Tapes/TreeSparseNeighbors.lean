import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptionsMaps
import OAI.Combinatorics.MatchingCount.Machines.TreeCertify
import OAI.Combinatorics.MatchingCount.Machines.TreeColorRaw
import OAI.Combinatorics.MatchingCount.Graphs.TreeSwitchRaw

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder
abbrev TableInput (C E V : Type) := (C×(Finset V×Finset E))×Finset E

def colorTable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (x : TableInput C E V) : Options (Finset E) :=
  neighbors ((x.2,(certify p ((x.1.1,x.1.2.1),colorRaw q ((x.1.1,x.1.2.2),x.2))).erase x.2),x.1.2.1.card)
def colorTableRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool}
    (P : Realizer p) (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (colorTable p q) :=
  (composition (pair (pair second (composition (pair second (composition
    (pair (pair first.fst first.snd.fst) (composition (pair (pair first.fst first.snd.snd) second)
      (colorRawRealizer Q Eq Le))) (certifyRealizer P))) (finsetErase (orderedSetEqual Eq))))
    (composition first.snd.fst finsetCard)) neighborsRealizer).congr (by
      intro x
      apply congrArg neighbors
      dsimp only [Function.comp_apply]
      congr 2
      ext b
      simp only [Finset.mem_erase])
lemma polynomial_colorTable {p : C×(E×V)→Bool} {q : C×(E×E)→Bool}
    {P : Realizer p} {Q : Realizer q}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hQ : PolynomialTime Q) (hE : PolynomialTime Eq) (hL : PolynomialTime Le) :
    PolynomialTime (colorTableRealizer P Q Eq Le) := by
  unfold colorTableRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_colorRaw hQ hE hL
  have := polynomial_certify hP
  have := polynomial_orderedSetEqual hE
  have := ExecutableOptions.polynomial_neighbors (A:=Finset E)
  tree_cost

def degree (n : ℕ) : ℕ := 8*(n/2).choose 2
def degreeRealizer : Realizer degree := by
  let half : Realizer (fun n : ℕ=>n/2) := composition (pair identity (constant 2)) quotient
  let chooseTwo : Realizer (fun n : ℕ=>n.choose 2) :=
    (composition (pair (composition (pair identity (composition (pair identity (constant 1)) subtract)) multiply)
      (constant 2)) quotient).congr (fun n=>Nat.choose_two_right n |>.symm)
  exact (composition (pair (constant 8) (composition half chooseTwo)) multiply).congr (fun _=>rfl)
lemma polynomial_degree : PolynomialTime degreeRealizer := by
  unfold degreeRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_quotient
  tree_cost

def switchTable (p : C×(E×V)→Bool) (q : C×(E×(V×V))→Bool) (x : TableInput C E V) : Options (Finset E) :=
  neighbors ((x.2,(certify p ((x.1.1,x.1.2.1),switchRaw q x)).erase x.2),degree x.1.2.1.card)
def switchTableRealizer {p : C×(E×V)→Bool} {q : C×(E×(V×V))→Bool}
    (P : Realizer p) (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchTable p q) :=
  (composition (pair (pair second (composition (pair second (composition
    (pair (pair first.fst first.snd.fst) (switchRawRealizer Q Eq Le EqV LeV)) (certifyRealizer P)))
    (finsetErase (orderedSetEqual Eq))))
    (composition (composition first.snd.fst finsetCard) degreeRealizer)) neighborsRealizer).congr (by
      intro x
      apply congrArg neighbors
      dsimp only [Function.comp_apply]
      congr 2
      ext b
      simp only [Finset.mem_erase])
lemma polynomial_switchTable {p : C×(E×V)→Bool} {q : C×(E×(V×V))→Bool}
    {P : Realizer p} {Q : Realizer q}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hQ : PolynomialTime Q) (hE : PolynomialTime Eq) (hL : PolynomialTime Le)
    (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (switchTableRealizer P Q Eq Le EqV LeV) := by
  unfold switchTableRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_switchRaw hQ hE hL hV hlV
  have := polynomial_certify hP
  have := polynomial_orderedSetEqual hE
  have := polynomial_degree
  have := ExecutableOptions.polynomial_neighbors (A:=Finset E)
  tree_cost

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder
variable (hloop : ∀ e,¬(ends e).IsDiag) (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
omit [Codec E] [Codec V] [Codec C] in
lemma colorTable_eq (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e f,q (c,(e,f))=decide (ends e=ends f))
    (a : Transport.PM (fun e v=>v∈ends e)) :
    colorTable p q ((c,(Finset.univ,Finset.univ)),a.val)=repr Subtype.val (Transport.Sparse.colorTable ends hloop hpar a) := by
  unfold colorTable
  have hraw : colorRaw q ((c,Finset.univ),a.val)=Transport.Sparse.colorRaw ends a.val := by
    simp only [colorRaw,Transport.Sparse.colorRaw,hq,decide_eq_true_eq]
  rw [hraw,certify_eq ends p c hp,Finset.card_univ]
  have he:=Finset.map_erase (pmEmbedding ends).toEmbedding (Transport.Sparse.colors ends a) a
  have hn:=neighbors_repr_map (pmEmbedding ends) a ((Transport.Sparse.colors ends a).erase a)
    (Fintype.card V) (Transport.Sparse.color_degree ends hloop hpar a)
  rw [he] at hn
  exact hn
omit [Codec E] [Codec V] [Codec C] in
lemma switchTable_eq (p : C×(E×V)→Bool) (q : C×(E×(V×V))→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e v w,q (c,(e,(v,w)))=decide (ends e=s(v,w)))
    (a : Transport.PM (fun e v=>v∈ends e)) :
    switchTable p q ((c,(Finset.univ,Finset.univ)),a.val)=repr Subtype.val (Transport.Sparse.switchTable ends hloop hpar a) := by
  unfold switchTable
  rw [switchRaw_eq ends q c hq,certify_eq ends p c hp,Finset.card_univ]
  have he:=Finset.map_erase (pmEmbedding ends).toEmbedding (Transport.Sparse.switches ends a) a
  have hn:=neighbors_repr_map (pmEmbedding ends) a ((Transport.Sparse.switches ends a).erase a)
    (degree (Fintype.card V)) (Transport.Sparse.switch_degree ends hloop hpar a)
  rw [he] at hn
  exact hn
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
