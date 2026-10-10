import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.Rational

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open SourceProbability FiniteDistribution Games RankGraph
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev AllVertex (U V E X Y : Type) [Fintype X] [Fintype Y] (M T N : Nat) := TestGraph.Vertex U V X Y (Wild U V X Y M T N) (Compare U E X Y M T N) T N
instance rawFullFintype : Fintype (Full U X M T N) := inferInstance
instance rawBigFintype : Fintype (Big U X M T N) := inferInstance
instance rawSmallFintype : Fintype (Small U V X Y M T N) := inferInstance
instance rawCompareFintype : Fintype (Compare U E X Y M T N) := inferInstance
instance allVertexFintype : Fintype (AllVertex U V E X Y M T N) := by
  unfold AllVertex TestGraph.Vertex Wild
  infer_instance

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

def supportEmbed : OutputVertex (M:=M) G ψLaw → AllVertex U V E X Y M T N
  | .inl r => .inl r
  | .inr (.inl w) => .inr (.inl (forgetWild G ψLaw w))
  | .inr (.inr c) => .inr (.inr c.val)

def allCost (D H K : ℝ) : AllVertex U V E X Y M T N → ℝ
  | .inl _ => D+1
  | .inr (.inl (.inl d)) => H*(fullLaw G ψLaw).weight d
  | .inr (.inl (.inr (.inl d))) => Fintype.card X*(bigLaw G ψLaw).weight d
  | .inr (.inl (.inr (.inr d))) => Fintype.card Y*(smallLaw G ψLaw).weight d
  | .inr (.inr d) => K*(comparisonLaw G ψLaw).weight d

def AllArc (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool) :=
  TestGraph.Arc (wildcard (M:=M) (T:=T) (N:=N) (U:=U) (V:=V) hYX) (comparison (M:=M) G fiber)

theorem supportEmbed_injective : Function.Injective (supportEmbed (M:=M) G ψLaw) := by
  intro a b h
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp only [supportEmbed,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact h
  · rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
      simp_all [forgetWild,Subtype.ext_iff]
  · exact Subtype.ext h

theorem embed_arc (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
    {a b : OutputVertex (M:=M) G ψLaw} (h : OutputArc G ψLaw hYX fiber a b) :
    AllArc G hYX fiber (supportEmbed G ψLaw a) (supportEmbed G ψLaw b) := by
  cases h with
  | rank h => exact .rank h
  | wild_in w x h => exact .wild_in (forgetWild G ψLaw w) x h
  | wild_out w x h => exact .wild_out (forgetWild G ψLaw w) x h
  | comp_in c => exact .comp_in c.val
  | comp_out c => exact .comp_out c.val

theorem allCost_sum (D H K : ℝ) (f : AllVertex U V E X Y M T N → Bool) :
    (∑ v, if f v then allCost G ψLaw D H K v else 0) =
      totalDeletionCost G ψLaw D H K (fun v => f (supportEmbed G ψLaw v)) := by
  simp only [totalDeletionCost,Fintype.sum_sum_type,allCost,vertexCost,supportEmbed,forgetWild]
  have hs {A : Type} [Fintype A] (μ : FiniteDistribution A) (c : ℝ) (g : A → Bool) :
      (∑ a, if g a then c*μ.weight a else 0) =
      ∑ a : μ.Support, if g a.val then c*μ.weight a.val else 0 := by
    simpa only [Finset.mul_sum,mul_ite,mul_one,mul_zero,mul_assoc] using
      congrArg (fun z => c*z) (μ.sum_support (fun a => if g a then 1 else 0)).symm
  rw [hs (fullLaw G ψLaw),hs (bigLaw G ψLaw),hs (smallLaw G ψLaw),hs (comparisonLaw G ψLaw)]
  congr 3

theorem all_soundness {D : Nat} (P : Parameters D) (R : RankParameters P X)
    (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1=G.project e x) (hsound : G.Sound P.theta)
    (F : Finset (AllVertex U V E X Y P.M P.T R.N))
    (hF : FeedbackR (AllArc G hYX fiber) F) :
    (D:ℝ) < ∑ v ∈ F, allCost G R.law D (8*((D:ℝ)+1)) P.K v := by
  let Q := Finset.univ.filter (fun v => supportEmbed G R.law v ∈ F)
  have hQ : FeedbackR (OutputArc G R.law hYX fiber) Q := by
    intro n f hi ha
    obtain ⟨i,hi⟩ := hF n (fun i => supportEmbed G R.law (f i))
      ((supportEmbed_injective G R.law).comp hi) (fun i => embed_arc G R.law hYX fiber (ha i))
    exact ⟨i,by simpa [Q] using hi⟩
  have h := parameterized_soundness P R G hYX fiber hproj hsound Q hQ
  have hv : (fun v => decide (v ∈ Q))=(fun v => decide (supportEmbed G R.law v ∈ F)) := by
    funext v
    simp [Q]
  rw [hv] at h
  rw [← allCost_sum G R.law (D:ℝ) (8*((D:ℝ)+1)) P.K (fun v => decide (v ∈ F))] at h
  simpa using h

end DirectedFeedback.Construction

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.GraphPrinter
open BoundedExpr

structure Family where
  n : List Bool → Nat
  k : List Bool → Nat
  arc : List Bool → Nat → Nat → Prop
  n_def : Def (r:=0) (fun x _ => n x)
  k_def : Def (r:=0) (fun x _ => k x)
  arc_def : PDef (r:=2) (fun x a => arc x (a 0) (a 1))
  k_pos : ∀ x, 0 < k x
  irrefl : ∀ x i, ¬arc x i i

namespace Family
variable (F : Family)

def pairs (x : List Bool) : List (Fin (F.n x) × Fin (F.n x)) :=
  ((List.finRange (F.n x)).product (List.finRange (F.n x))).filter
    (fun p => decide (F.arc x p.1.val p.2.val))

@[simp] theorem mem_pairs (x : List Bool) (a b : Fin (F.n x)) :
    (a,b) ∈ F.pairs x ↔ F.arc x a.val b.val := by simp [pairs]

def graph (x : List Bool) : Digraph where
  n := F.n x
  arcs := F.pairs x
  loopless := by
    rintro ⟨a,b⟩ hab he
    have h := (F.mem_pairs x a b).mp hab
    change a=b at he
    subst b
    exact F.irrefl x a.val h
  nodup := (List.nodup_finRange _).product (List.nodup_finRange _) |> fun h => h.filter _

def inst (x : List Bool) : GapInstance := ⟨F.graph x,F.k x,F.k_pos x⟩

def count (x : List Bool) : Nat :=
  ∑ i ∈ Finset.range (F.n x), ∑ j ∈ Finset.range (F.n x), if F.arc x i j then 1 else 0

theorem count_eq (x : List Bool) : F.count x=(F.pairs x).length := by
  have he : (F.pairs x).toFinset = Finset.univ.filter
      (fun p : Fin (F.n x) × Fin (F.n x) => F.arc x p.1.val p.2.val) := by
    ext ⟨a,b⟩
    simp [pairs]
  have hnd : (F.pairs x).Nodup := (F.graph x).nodup
  rw [← List.toFinset_card_of_nodup hnd,he,Finset.card_filter]
  simp only [count,Finset.sum_range,Fintype.sum_prod_type]

private theorem flatMap_filter {A B : Type} (l : List A) (p : A → Bool) (f : A → List B) :
    (l.filter p).flatMap f = l.flatMap (fun a => if p a then f a else []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a=true <;> simp [h,ih]

private theorem map_fin_values (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

def edgeBits (x : List Bool) : List Bool :=
  (List.range (F.n x)).flatMap (fun i => (List.range (F.n x)).flatMap
    (fun j => if F.arc x i j then natBits i++natBits j else []))

theorem edgeBits_eq (x : List Bool) : F.edgeBits x=
    (F.pairs x).flatMap (fun e => natBits e.1.val++natBits e.2.val) := by
  rw [edgeBits,pairs,flatMap_filter]
  change _ = (List.flatMap (fun i => (List.finRange (F.n x)).map (fun j => (i,j)))
    (List.finRange (F.n x))).flatMap _
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  rw [← map_fin_values (F.n x),List.flatMap_map]
  congr 1
  funext i
  simp only [List.flatMap_map,decide_eq_true_eq]

theorem n_def_any (r : Nat) : Def (r:=r) (fun x _ => F.n x) :=
  F.n_def.subst Fin.elim0 (fun i => i.elim0)

theorem count_def : Def (r:=0) (fun x _ => F.count x) := by
  have ha : Def (r:=2) (fun x a => if F.arc x (a 1) (a 0) then 1 else 0) :=
    F.arc_def.rename ![1,0]
  simpa only [count,Fin.cons_zero,Fin.cons_one] using
    (F.n_def_any 0).sum ((F.n_def_any 1).sum ha)

theorem edgeBits_def : OutDef (r:=0) (fun x _ => F.edgeBits x) := by
  have ha : PDef (r:=2) (fun x a => F.arc x (a 1) (a 0)) :=
    F.arc_def.rename ![1,0]
  have hb : OutDef (r:=2) (fun x a => if F.arc x (a 1) (a 0)
      then natBits (a 1)++natBits (a 0) else []) :=
    ((OutDef.nat (Def.arg 1)).append (OutDef.nat (Def.arg 0))).when ha
  simpa only [edgeBits,Fin.cons_zero,Fin.cons_one] using
    OutDef.loop (F.n_def_any 0) (OutDef.loop (F.n_def_any 1) hb)

def bits (x : List Bool) : List Bool := natBits (F.k x)++natBits (F.n x)++
  (List.range (F.n x)).flatMap natBits++natBits (F.count x)++F.edgeBits x

theorem bits_def : OutDef (r:=0) (fun x _ => F.bits x) := by
  have hv : OutDef (r:=0) (fun x _ => (List.range (F.n x)).flatMap natBits) := by
    change OutDef (fun x (_ : Fin 0 → Nat) => (List.range (F.n x)).flatMap (fun i => List.replicate i true++[false]))
    simpa only [Fin.cons_zero] using OutDef.loop (F.n_def_any 0) (OutDef.nat (Def.arg 0))
  exact ((((OutDef.nat F.k_def).append (OutDef.nat F.n_def)).append hv).append
    (OutDef.nat F.count_def)).append F.edgeBits_def

theorem bits_correct (x : List Bool) : F.bits x=(F.inst x).bits := by
  simp only [bits,GapInstance.bits,inst,Digraph.bits,graph]
  rw [count_eq,edgeBits_eq]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.flatMap_assoc,List.append_assoc]

noncomputable def computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    GapInstance.bits F.inst := by
  let o := F.bits_def.choose
  have ho : ∀ x, o.eval x Fin.elim0=(F.inst x).bits := fun x =>
    (F.bits_def.choose_spec x Fin.elim0).trans (F.bits_correct x)
  exact Output.realizes _ _ o ho

theorem computation_finite (k : F.computation.tm.K) : Finite (F.computation.tm.Γ k) := by
  unfold computation
  exact Output.realizes_alphabet _ _ _ _ k

end Family
end DirectedFeedback.GraphPrinter

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.LocalAssignments

def Consistent {S A : Type} (coords : S → Nat) (labels : S → A) : Prop :=
  ∀ i j, coords i=coords j → labels i=labels j

theorem extend_global {S A : Type} [Nonempty A] (coords : S → Nat) (labels : S → A)
    (hc : Consistent coords labels) : ∃ all : Nat → A, all ∘ coords=labels := by
  let all : Nat → A := fun v => if h : ∃ i, coords i=v then labels h.choose
    else Classical.choice inferInstance
  exact ⟨all,funext (fun i => by
    dsimp [all]
    split_ifs with h
    · exact hc _ _ h.choose_spec
    · exact False.elim (h ⟨i,rfl⟩))⟩

theorem restriction_consistent {S A : Type} (coords : S → Nat) (all : Nat → A) :
    Consistent coords (all ∘ coords) := fun _ _ h => congrArg all h

theorem forall_iff {S T X Y : Type} [Nonempty X] [Nonempty Y]
    (u : S → Nat) (v : T → Nat) (P : (S → X) → (T → Y) → Prop) :
    (∀ a : Nat → X, ∀ b : Nat → Y, P (a ∘ u) (b ∘ v)) ↔
      ∀ a b, Consistent u a → Consistent v b → P a b := by
  constructor
  · intro h a b ha hb
    obtain ⟨la,hla⟩ := extend_global u a ha
    obtain ⟨lb,hlb⟩ := extend_global v b hb
    simpa only [hla,hlb] using h la lb
  · intro h a b
    exact h _ _ (restriction_consistent u a) (restriction_consistent v b)

namespace Definability
open BoundedExpr
variable {r : Nat} {S A : Type} [Fintype S] [Fintype A]

omit [Fintype A] in
 theorem consistent_def (c : S → List Bool → (Fin r → Nat) → Nat)
    (hc : ∀ i, Def (c i)) (a : S → A) :
    PDef (fun x z => Consistent (fun i => c i x z) a) := by
  exact PDef.all (fun i => PDef.all (fun j =>
    (PDef.nat_eq (hc i) (hc j)).imp (PDef.const (a i=a j))))

end Definability
end DirectedFeedback.LocalAssignments

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LocalPrinter
open BoundedExpr LocalAssignments

abbrev Rule (S T X Y : Type) (H : Nat) := (S → X) → (T → Y) → Option (Fin H)

def Ordered {H : Nat} : Option (Fin H) → Option (Fin H) → Prop
  | some a,some b => a < b
  | _,_ => True

def potential {H : Nat} (a : Option (Fin H)) : Nat := (a.map Fin.val).getD 0

theorem ordered_iff {H : Nat} (a b : Option (Fin H)) :
    Ordered a b ↔ (a ≠ none → b ≠ none → potential a < potential b) := by
  cases a <;> cases b <;> simp [Ordered,potential]

structure Family (S T X Y : Type) [Fintype S] [Fintype T] [Fintype X] [Fintype Y]
    (H : Nat) where
  n : List Bool → Nat
  k : List Bool → Nat
  valid : List Bool → Nat → Prop
  u : List Bool → Nat → S → Nat
  v : List Bool → Nat → T → Nat
  rule : List Bool → Nat → Rule S T X Y H
  n_def : Def (r:=0) (fun x _ => n x)
  k_def : Def (r:=0) (fun x _ => k x)
  valid_def : PDef (r:=1) (fun x a => valid x (a 0))
  u_def : ∀ s, Def (r:=1) (fun x a => u x (a 0) s)
  v_def : ∀ t, Def (r:=1) (fun x a => v x (a 0) t)
  rule_def : FDef (r:=1) (fun x a => rule x (a 0))
  k_pos : ∀ x, 0 < k x

namespace Family
variable {S T X Y : Type} [Fintype S] [Fintype T] [Fintype X] [Fintype Y]
  [Nonempty X] [Nonempty Y] {H : Nat} (F : Family S T X Y H)

def Arc (x : List Bool) (i j : Nat) : Prop :=
  i ≠ j ∧ F.valid x i ∧ F.valid x j ∧
    ∀ a : S ⊕ S → X, ∀ b : T ⊕ T → Y,
      Consistent (Sum.elim (F.u x i) (F.u x j)) a →
      Consistent (Sum.elim (F.v x i) (F.v x j)) b →
      Ordered (F.rule x i (a ∘ Sum.inl) (b ∘ Sum.inl))
        (F.rule x j (a ∘ Sum.inr) (b ∘ Sum.inr))

def value (x : List Bool) (i : Nat) (a : Nat → X) (b : Nat → Y) : Option (Fin H) :=
  F.rule x i (a ∘ F.u x i) (b ∘ F.v x i)

theorem arc_global (x : List Bool) (i j : Nat) : F.Arc x i j ↔
    i ≠ j ∧ F.valid x i ∧ F.valid x j ∧
    ∀ a : Nat → X, ∀ b : Nat → Y, Ordered (F.value x i a b) (F.value x j a b) := by
  unfold Arc value
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact (forall_iff (Sum.elim (F.u x i) (F.u x j)) (Sum.elim (F.v x i) (F.v x j))
    (fun a b => Ordered (F.rule x i (a ∘ Sum.inl) (b ∘ Sum.inl))
      (F.rule x j (a ∘ Sum.inr) (b ∘ Sum.inr)))).symm

omit [Nonempty X] [Nonempty Y] in
theorem arc_def : PDef (r:=2) (fun x a => F.Arc x (a 0) (a 1)) := by
  have hu (s : S ⊕ S) : Def (r:=2) (fun x a => Sum.elim (F.u x (a 0)) (F.u x (a 1)) s) := by
    cases s with
    | inl s => exact (F.u_def s).rename (fun _ => 0)
    | inr s => exact (F.u_def s).rename (fun _ => 1)
  have hv (t : T ⊕ T) : Def (r:=2) (fun x a => Sum.elim (F.v x (a 0)) (F.v x (a 1)) t) := by
    cases t with
    | inl t => exact (F.v_def t).rename (fun _ => 0)
    | inr t => exact (F.v_def t).rename (fun _ => 1)
  have hr0 := F.rule_def.rename (s:=2) (fun _ => 0)
  have hr1 := F.rule_def.rename (s:=2) (fun _ => 1)
  have hv0 : PDef (r:=2) (fun x a => F.valid x (a 0)) := F.valid_def.rename (fun _ => 0)
  have hv1 : PDef (r:=2) (fun x a => F.valid x (a 1)) := F.valid_def.rename (fun _ => 1)
  exact ((PDef.nat_eq (Def.arg 0) (Def.arg 1)).not).and
    (hv0.and (hv1.and
      (PDef.all (fun a => PDef.all (fun b =>
        (Definability.consistent_def _ hu a).imp
          ((Definability.consistent_def _ hv b).imp
            ((hr0.pair hr1).toDef (fun r => if Ordered (r.1 (a ∘ Sum.inl) (b ∘ Sum.inl))
              (r.2 (a ∘ Sum.inr) (b ∘ Sum.inr)) then 1 else 0))))))))

def printer : GraphPrinter.Family where
  n := F.n
  k := F.k
  arc := F.Arc
  n_def := F.n_def
  k_def := F.k_def
  arc_def := F.arc_def
  k_pos := F.k_pos
  irrefl := fun _ _ h => h.1 rfl

def deleted (x : List Bool) (a : Nat → X) (b : Nat → Y) : Finset (Fin (F.n x)) :=
  Finset.univ.filter (fun i => F.valid x i.val ∧ F.value x i.val a b=none)

theorem deleted_feedback (x : List Bool) (a : Nat → X) (b : Nat → Y) :
    FeedbackR (fun i j : Fin (F.n x) => F.Arc x i.val j.val) (F.deleted x a b) := by
  intro n f _ ha
  by_contra hn
  have hv (j) : F.valid x (f j).val := (ha j).2.1
  have hs (j) : F.value x (f j).val a b ≠ none := by
    intro h
    exact hn ⟨j,by simp [deleted,h,hv]⟩
  have hi (j) : potential (F.value x (f j).val a b) < potential (F.value x (f (j+1)).val a b) :=
    (ordered_iff _ _).mp (((F.arc_global x _ _).mp (ha j)).2.2.2 a b) (hs j) (hs (j+1))
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hi j)
  have he : (∑ j : Fin (n+1), potential (F.value x (f (j+1)).val a b)) =
      ∑ j : Fin (n+1), potential (F.value x (f j).val a b) :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin (n+1))) _ _ (fun _ => rfl)
  rw [he] at hsum
  exact (lt_irrefl _ hsum)

end Family
end DirectedFeedback.LocalPrinter

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.AllLabels
open Construction SourceProbability FiniteDistribution Games RankGraph
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)

abbrev deleted (a : U → X) (b : V → Y) : AllVertex U V E X Y M T N → Prop :=
  TestGraph.LabelDeleted (wildcard (M:=M) (T:=T) (N:=N) hYX) (comparison G fiber) a b
abbrev pot (a : U → X) (b : V → Y) : AllVertex U V E X Y M T N → ℚ :=
  TestGraph.labelPotential (wildcard (M:=M) (T:=T) (N:=N) hYX) (comparison G fiber) a b

def height (a : U → X) (b : V → Y) : AllVertex U V E X Y M T N → Nat
  | .inl r => 2*(eval a b r).val
  | .inr (.inl w) => 2*((wildcard hYX w).level ((wildcard hYX w).cell (labels a b (wildcard hYX w).tuple))).val
  | .inr (.inr c) => (eval a b (comparison G fiber c).source).val+(eval a b (comparison G fiber c).target).val

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem height_bound (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) :
    height G hYX fiber a b v<2*N+1 := by
  rcases v with r | (w | c)
  · have := (eval a b r).isLt
    dsimp [height]
    omega
  · have := ((wildcard hYX w).level ((wildcard hYX w).cell (labels a b (wildcard hYX w).tuple))).isLt
    dsimp [height]
    omega
  · have := (eval a b (comparison G fiber c).source).isLt
    have := (eval a b (comparison G fiber c).target).isLt
    dsimp [height]
    omega

def code (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) : Option (Fin (2*N+1)) :=
  if deleted G hYX fiber a b v then none else some ⟨height G hYX fiber a b v,height_bound G hYX fiber a b v⟩

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem code_none (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) :
    code G hYX fiber a b v=none ↔ deleted G hYX fiber a b v := by simp [code]

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem height_potential (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) :
    (height G hYX fiber a b v:ℚ)=2*pot G hYX fiber a b v := by
  rcases v with r | (w | c) <;> simp [height,pot,TestGraph.labelPotential]; ring

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem ordered_arc (a : U → X) (b : V → Y) {v w : AllVertex U V E X Y M T N}
    (h : AllArc G hYX fiber v w) : LocalPrinter.Ordered (code G hYX fiber a b v) (code G hYX fiber a b w) := by
  by_cases hv : deleted G hYX fiber a b v
  · simp [code,hv,LocalPrinter.Ordered]
  by_cases hw : deleted G hYX fiber a b w
  · simp [code,hw,LocalPrinter.Ordered]
  simp only [code,hv,hw,ite_false,LocalPrinter.Ordered]
  change height G hYX fiber a b v<height G hYX fiber a b w
  have hi := TestGraph.labelPotential_increases (wildcard hYX) (comparison G fiber) a b h hv hw
  have hi' : (height G hYX fiber a b v:ℚ)<height G hYX fiber a b w := by
    rw [height_potential,height_potential]
    exact mul_lt_mul_of_pos_left hi (by norm_num)
  exact_mod_cast hi'

theorem embed_deleted (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) (a : U → X) (b : V → Y)
    (v : OutputVertex (M:=M) G ψLaw) :
    decide (deleted G hYX fiber a b (supportEmbed G ψLaw v))=labelDeleted G ψLaw hYX fiber a b v := by
  rcases v with r | (w | c)
  · rfl
  · rcases w with w | (w | w) <;> rfl
  · rfl

theorem completeness {D : Nat} (P : Parameters D) (R : RankParameters P X)
    (G : Game U V E X Y) (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1=G.project e x)
    (a : U → X) (b : V → Y) (hscore : 1-(P.theta:ℝ)≤G.score a b) :
    (∑ v : AllVertex U V E X Y P.M P.T R.N,
      if deleted G hYX fiber a b v then allCost G R.law D (8*((D:ℝ)+1)) P.K v else 0) ≤ 4 := by
  have hh := weighted_completeness (M:=P.M) G R.law hYX fiber a b hproj
      D (8*((D:ℝ)+1)) P.K (by positivity) (by exact_mod_cast P.K_pos.le)
  have hloss : (P.K:ℝ)*(1-G.score a b) ≤ (P.K:ℝ)*P.theta :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have he := allCost_sum (M:=P.M) G R.law (D:ℝ) (8*((D:ℝ)+1)) P.K
    (fun v => decide (deleted G hYX fiber a b v))
  simp only [decide_eq_true_eq] at he
  rw [he]
  simp only [embed_deleted]
  linarith [P.fullChernoff,P.Ktheta]

end DirectedFeedback.AllLabels

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution

theorem fixed_denominator {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ x, Rational (w x)) (hn : ∀ x, 0 ≤ w x) :
    ∃ C : Nat, 0 < C ∧ ∃ c : Ω → Nat, ∀ x, (C:ℝ)*w x=c x := by
  choose q hq using hw
  let C := ∏ x, (q x).den
  have hC : 0 < C := Finset.prod_pos (fun x _ => (q x).den_pos)
  have hd (x : Ω) : (q x).den ∣ C := Finset.dvd_prod_of_mem _ (Finset.mem_univ x)
  choose k hk using hd
  refine ⟨C,hC,fun x => (q x).num.toNat*k x,?_⟩
  intro x
  have hnum : 0 ≤ (q x).num := Rat.num_nonneg.mpr (by exact_mod_cast hq x ▸ hn x)
  rw [hq x,Rat.cast_def,hk x,Nat.cast_mul,Nat.cast_mul]
  have hden : ((q x).den:ℝ) ≠ 0 := by exact_mod_cast (q x).den_ne_zero
  have hh : (((q x).num.toNat:Nat):ℝ)=((q x).num:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  rw [hh]
  field_simp

theorem integral_realization {Ω : Type} [Fintype Ω] (μ : FiniteDistribution Ω)
    (hμ : μ.RationalMass) :
    ∃ C : Nat, 0 < C ∧ ∃ c : Ω → Nat,
      (∀ x, (C:ℝ)*μ.weight x=c x) ∧ ∑ x, c x=C := by
  obtain ⟨C,hC,c,hc⟩ := fixed_denominator μ.weight hμ μ.nonnegative
  refine ⟨C,hC,c,hc,?_⟩
  have hh : (∑ x, (c x:ℝ)) = C := by
    simp only [← hc,← Finset.mul_sum,μ.normalized,mul_one]
  exact_mod_cast hh

theorem pushforward_comp {Ω Γ Ξ : Type} [Fintype Ω] [Fintype Γ] [Fintype Ξ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (g : Γ → Ξ) :
    (μ.pushforward f).pushforward g=μ.pushforward (g ∘ f) := by
  apply eq_of_weight_eq
  intro z
  simp only [pushforward]
  calc
    _ = ∑ y, ∑ x, if f x=y then (if g y=z then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : g y=z <;> simp [h]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem pushforward_product {Ω Γ A B : Type} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (Prod.map f g) = (μ.pushforward f).product (ν.pushforward g) := by
  apply eq_of_weight_eq
  rintro ⟨a,b⟩
  simp only [pushforward,product,Fintype.sum_prod_type,Prod.map_apply,Prod.mk.injEq]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hf : f x=a <;> by_cases hg : g y=b <;> simp [hf,hg]

theorem pushforward_fst {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    (μ.product ν).pushforward Prod.fst=μ := by
  apply eq_of_weight_eq
  intro x
  simp only [pushforward,product,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum,ν.normalized]

end DirectedFeedback.SourceProbability.FiniteDistribution

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution

 theorem eq_of_expectation_eq {A : Type} [Fintype A]
    (μ ν : FiniteDistribution A) (h : ∀ f : A → ℝ, μ.expectation f=ν.expectation f) : μ=ν := by
  apply eq_of_weight_eq
  intro a
  simpa [expectation,mul_ite] using h (fun x => if x=a then 1 else 0)

def zipEquiv (A B : Type) (n : Nat) :
    ((Fin n → A) × (Fin n → B)) ≃ (Fin n → A × B) where
  toFun p i := (p.1 i,p.2 i)
  invFun p := (fun i => (p i).1,fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem iid_zip {A B : Type} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (n : Nat) :
    ((μ.iid n).product (ν.iid n)).transport (zipEquiv A B n)=(μ.product ν).iid n := by
  apply eq_of_weight_eq
  intro z
  change (∏ i, μ.weight (z i).1)*(∏ i,ν.weight (z i).2)=
    ∏ i, μ.weight (z i).1*ν.weight (z i).2
  exact (Finset.prod_mul_distrib).symm

theorem expectation_iid_zip {A B : Type} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (n : Nat)
    (f : (Fin n → A × B) → ℝ) :
    (μ.iid n).expectation (fun a => (ν.iid n).expectation (fun b => f (fun i => (a i,b i)))) =
      ((μ.product ν).iid n).expectation f := by
  rw [← iid_zip,expectation_transport,expectation_product]
  rfl

theorem expectation_iid_map {A B : Type} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (g : A → B) (n : Nat) (f : (Fin n → B) → ℝ) :
    (μ.iid n).expectation (fun a => f (fun i => g (a i))) =
      ((μ.pushforward g).iid n).expectation f := by
  rw [iid_pushforward,expectation_pushforward]

theorem sample_prefix {E U S : Type} [Fintype E] [Fintype U] [Fintype S]
    (μ : FiniteDistribution E) (left : E → U) (ν : FiniteDistribution S)
    {t L : Nat} (ht : t≤L) (f : (Fin t → U × S) → ℝ) :
    (ν.iid t).expectation (fun s => (μ.iid L).expectation
      (fun e => f (fun j => (left (e (Fin.castLE ht j)),s j)))) =
      (((μ.pushforward left).product ν).iid t).expectation f := by
  rw [expectation_comm]
  change (μ.iid L).expectation (fun e => (ν.iid t).expectation
      (fun s => f (fun j => (left (takePrefix ht e j),s j)))) = _
  rw [expectation_iid_take μ ht (fun e => (ν.iid t).expectation
    (fun s => f (fun j => (left (e j),s j))))]
  rw [expectation_iid_map μ left t (fun a => (ν.iid t).expectation
    (fun s => f (fun j => (a j,s j))))]
  exact expectation_iid_zip _ _ _ _

theorem sample_prefix_fresh {E U S : Type} [Fintype E] [Fintype U] [Fintype S]
    (μ : FiniteDistribution E) (left : E → U) (ν : FiniteDistribution S)
    {t L : Nat} (ht : t<L) (f : (Fin t → U × S) → E → ℝ) :
    (ν.iid t).expectation (fun s => (μ.iid L).expectation
      (fun e => f (fun j => (left (e (Fin.castLE (Nat.le_of_lt ht) j)),s j)) (e ⟨t,ht⟩))) =
      (((μ.pushforward left).product ν).iid t).expectation
        (fun a => μ.expectation (f a)) := by
  have h (s : Fin t → S) := expectation_iid_prefix_fresh μ ht
    (fun e fresh => f (fun j => (left (e j),s j)) fresh)
  calc
    _ = (ν.iid t).expectation (fun s => (μ.iid t).expectation
      (fun e => μ.expectation (fun fresh => f (fun j => (left (e j),s j)) fresh))) :=
        expectation_congr _ h
    _ = _ := sample_prefix μ left ν le_rfl (fun a => μ.expectation (f a))

end DirectedFeedback.SourceProbability.FiniteDistribution

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution Construction PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev SlotSeed (X : Type) (M : Nat) := Σ _ : Fin M, X → Bool
abbrev PrefixSeed (X : Type) (M t : Nat) := Fin t → SlotSeed X M
abbrev FullSeed (X : Type) [Fintype X] (M T N : Nat) :=
  Emb (rankLength X T) N × PrefixSeed X M T
abbrev CommonSeed (X : Type) [Fintype X] (M T N : Nat) :=
  Emb (rankLength X T) N × (Σ t : Fin T, PrefixSeed X M t.val)
abbrev BigSeed (X : Type) [Fintype X] (M T N : Nat) :=
  CommonSeed X M T N × Pivotal.LabelOrder X
abbrev SmallSeed (X Y : Type) [Fintype X] [Fintype Y] (M T N : Nat) :=
  CommonSeed X M T N × Pivotal.LabelOrder Y
abbrev CompareSeed (X Y : Type) [Fintype X] (M T N : Nat) :=
  Σ d : CommonSeed X M T N, Σ _ : Fin M, Fin (Prefix.cellCount d.2.1.val) × (Y → Coupling.Block)

abbrev Seed (X Y : Type) [Fintype X] [Fintype Y] (M T N : Nat) :=
  FullSeed X M T N ⊕ (BigSeed X M T N ⊕ (SmallSeed X Y M T N ⊕ CompareSeed X Y M T N))
instance seedFullFintype : Fintype (FullSeed X M T N) := inferInstance
instance seedCommonFintype : Fintype (CommonSeed X M T N) := inferInstance
instance seedBigFintype : Fintype (BigSeed X M T N) := inferInstance
instance seedSmallFintype : Fintype (SmallSeed X Y M T N) := inferInstance
instance seedCompareFintype : Fintype (CompareSeed X Y M T N) := inferInstance
instance seedFintype : Fintype (Seed X Y M T N) := by unfold Seed; infer_instance

def slotLaw : FiniteDistribution (SlotSeed X M) := (uniform (Fin M)).sigma subsetLaw
variable (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

def fullLaw : FiniteDistribution (FullSeed X M T N) := ψLaw.product (slotLaw.iid T)
def commonLaw : FiniteDistribution (CommonSeed X M T N) :=
  ψLaw.product ((uniform (Fin T)).sigma (fun t => slotLaw.iid t.val))
def bigLaw : FiniteDistribution (BigSeed X M T N) := (commonLaw ψLaw).product Pivotal.labelOrderLaw
def smallLaw : FiniteDistribution (SmallSeed X Y M T N) := (commonLaw ψLaw).product Pivotal.labelOrderLaw

def localCompareLaw (t : Nat) : FiniteDistribution (Σ _ : Fin M, Fin (Prefix.cellCount t) × (Y → Coupling.Block)) :=
  (uniform (Fin M)).sigma (fun i => (uniform (Fin (Prefix.cellCount t))).product
    (Coupling.law (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])))
def compareLaw : FiniteDistribution (CompareSeed X Y M T N) :=
  (commonLaw ψLaw).sigma (fun d => localCompareLaw d.2.1.val)

variable (G : Game U V E X Y)

def fillPrefix {t : Nat} (ht : t≤T+1) (a : PrefixSeed X M t) (e : Fin (T+1) → E) :
    PrefixData U X M t := fun j => (G.left (e (Fin.castLE ht j)),a j)
def fillFull (a : FullSeed X M T N) (e : Fin (T+1) → E) : Full U X M T N :=
  (a.1,fillPrefix G (Nat.le_succ T) a.2 e)
def fillCommon (a : CommonSeed X M T N) (e : Fin (T+1) → E) : Common U X M T N :=
  (a.1,⟨a.2.1,fillPrefix G (by have := a.2.1.isLt; omega) a.2.2 e⟩)
def fresh (a : CommonSeed X M T N) (e : Fin (T+1) → E) : E :=
  e ⟨a.2.1.val,by have := a.2.1.isLt; omega⟩
def fillBig (a : BigSeed X M T N) (e : Fin (T+1) → E) : Big U X M T N :=
  (fillCommon G a.1 e,(G.left (fresh a.1 e),a.2))
def fillSmall (a : SmallSeed X Y M T N) (e : Fin (T+1) → E) : Small U V X Y M T N :=
  (fillCommon G a.1 e,(G.right (fresh a.1 e),a.2))
def fillCompare (a : CompareSeed X Y M T N) (e : Fin (T+1) → E) : Compare U E X Y M T N :=
  ⟨fillCommon G a.1 e,fresh a.1 e,a.2⟩

def fill : Seed X Y M T N → (Fin (T+1) → E) → AllVertex U V E X Y M T N
  | .inl a,e => .inr (.inl (.inl (fillFull G a e)))
  | .inr (.inl a),e => .inr (.inl (.inr (.inl (fillBig G a e))))
  | .inr (.inr (.inl a)),e => .inr (.inl (.inr (.inr (fillSmall G a e))))
  | .inr (.inr (.inr a)),e => .inr (.inr (fillCompare G a e))

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] [NeZero T] in
theorem sample_full (f : Full U X M T N → ℝ) :
    (fullLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillFull G a e))) =
      (Construction.fullLaw G ψLaw).expectation f := by
  simp only [fullLaw,Construction.fullLaw,expectation_product]
  apply expectation_congr
  intro ψ
  exact sample_prefix G.edgeLaw G.left slotLaw (Nat.le_succ T) (fun a => f (ψ,a))

omit [Fintype V] [Fintype Y] [Nonempty Y] in
theorem sample_big (f : Big U X M T N → ℝ) :
    (bigLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillBig G a e))) =
      (Construction.bigLaw G ψLaw).expectation f := by
  simp only [bigLaw,commonLaw,Construction.bigLaw,Construction.common,PrefixExperiment.commonLaw,
    expectation_product,expectation_sigma]
  apply expectation_congr
  intro ψ
  apply expectation_congr
  intro t
  simp_rw [expectation_comm Pivotal.labelOrderLaw (G.edgeLaw.iid (T+1))]
  simp only [Construction.bigMarginal,expectation_pushforward]
  exact sample_prefix_fresh G.edgeLaw G.left slotLaw (by have := t.isLt; omega : t.val<T+1)
    (fun a e => Pivotal.labelOrderLaw.expectation (fun o => f ((ψ,⟨t,a⟩),(G.left e,o))))

omit [Nonempty X] in
theorem sample_small (f : Small U V X Y M T N → ℝ) :
    (smallLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillSmall G a e))) =
      (Construction.smallLaw G ψLaw).expectation f := by
  simp only [smallLaw,commonLaw,Construction.smallLaw,Construction.common,PrefixExperiment.commonLaw,
    expectation_product,expectation_sigma]
  apply expectation_congr
  intro ψ
  apply expectation_congr
  intro t
  simp_rw [expectation_comm Pivotal.labelOrderLaw (G.edgeLaw.iid (T+1))]
  simp only [Construction.smallMarginal,expectation_pushforward]
  exact sample_prefix_fresh G.edgeLaw G.left slotLaw (by have := t.isLt; omega : t.val<T+1)
    (fun a e => Pivotal.labelOrderLaw.expectation (fun o => f ((ψ,⟨t,a⟩),(G.right e,o))))

omit [Fintype V] [Nonempty X] [Nonempty Y] in
theorem sample_compare (f : Compare U E X Y M T N → ℝ) :
    (compareLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillCompare G a e))) =
      (Construction.comparisonLaw G ψLaw).expectation f := by
  simp only [compareLaw,Construction.comparisonLaw,expectation_sigma]
  simp only [commonLaw,Construction.common,PrefixExperiment.commonLaw,expectation_product,expectation_sigma]
  apply expectation_congr
  intro ψ
  apply expectation_congr
  intro t
  change (slotLaw.iid t.val).expectation (fun a =>
    (localCompareLaw t.val).expectation (fun z => (G.edgeLaw.iid (T+1)).expectation
      (fun e => f (fillCompare G ⟨(ψ,⟨t,a⟩),z⟩ e)))) = _
  simp_rw [expectation_comm (localCompareLaw t.val) (G.edgeLaw.iid (T+1))]
  dsimp +unfoldPartialApp only [fillCompare,fillCommon,fillPrefix,fresh]
  simpa +unfoldPartialApp only [localCompareLaw,expectation_sigma,expectation_product,fillCompare,fillCommon,fillPrefix,fresh,
    PrefixExperiment.atomLaw,Construction.bigMarginal,slotLaw] using
    sample_prefix_fresh G.edgeLaw G.left slotLaw (by have := t.isLt; omega : t.val<T+1)
      (fun a e => (localCompareLaw t.val).expectation (fun z => f ⟨(ψ,⟨t,a⟩),e,z⟩))

end DirectedFeedback.PacketSeeds

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RankPackets
open RankGraph

abbrev Shape (X Y : Type) (T N : Nat) :=
  (Σ t : Fin (T+1), (Fin t.val → X) → Fin N) ⊕
  (Σ t : Fin T, ((Fin t.val → X) × Y) → Fin N)

instance shapeFintype {X Y : Type} [Fintype X] [Fintype Y] {T N : Nat} :
    Fintype (Shape X Y T N) := by unfold Shape; infer_instance

variable {W X Y : Type} {T N : Nat}

def fill (s : Shape X Y T N) (a : Fin (T+1) → W) : Rank W W X Y T N :=
  match s with
  | .inl ⟨t,f⟩ => vertex (.inl ⟨t,fun i => a (Fin.castLE (Nat.le_of_lt t.isLt) i)⟩) f
  | .inr ⟨t,f⟩ => vertex (.inr ⟨t,(fun i => a (Fin.castLE (by have := t.isLt; omega) i)),
      a ⟨t.val,by have := t.isLt; omega⟩⟩) f

theorem fill_surjective [Nonempty W] : Function.Surjective
    (fun z : Shape X Y T N × (Fin (T+1) → W) => fill z.1 z.2) := by
  intro r
  induction r using Quot.inductionOn with
  | h d =>
    rcases d with ⟨⟨t,s⟩ | ⟨t,s,v⟩,f⟩
    · let a : Fin (T+1) → W := fun i => if h : i.val<t.val then s ⟨i.val,h⟩
          else Classical.choice inferInstance
      refine ⟨(.inl ⟨t,f⟩,a),?_⟩
      have he : (fun i : Fin t.val => a (Fin.castLE (Nat.le_of_lt t.isLt) i))=s := by
        funext i
        simp only [a,Fin.castLE,dite_eq_left i.isLt]
      exact congrArg (fun s' : Fin t.val → W => vertex (.inl ⟨t,s'⟩) f) he
    · let a : Fin (T+1) → W := fun i => if h : i.val<t.val then s ⟨i.val,h⟩ else v
      refine ⟨(.inr ⟨t,f⟩,a),?_⟩
      have he : (fun i : Fin t.val => a (Fin.castLE (by have := t.isLt; omega) i))=s := by
        funext i
        simp only [a,Fin.castLE,dite_eq_left i.isLt]
      have hv : a ⟨t.val,by have := t.isLt; omega⟩=v := by simp [a]
      have hp : ((fun i : Fin t.val => a (Fin.castLE (by have := t.isLt; omega) i)),
          a ⟨t.val,by have := t.isLt; omega⟩)=(s,v) := Prod.ext he hv
      exact congrArg (fun p : (Fin t.val → W) × W => vertex (.inr ⟨t,p⟩) f) hp

theorem eval_fill (s : Shape X Y T N) (a : Fin (T+1) → W)
    (lu : W → X) (lv : W → Y) :
    eval lu lv (fill s a) = eval (lu ∘ a) (lv ∘ a) (fill s id) := by
  rcases s with ⟨t,f⟩ | ⟨t,f⟩ <;> rfl

end DirectedFeedback.RankPackets

end
end

end OAI
