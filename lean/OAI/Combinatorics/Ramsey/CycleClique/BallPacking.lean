import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Exceptional
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems
import OAI.Combinatorics.Ramsey.CycleClique.SystemInsertion

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def pathEdges : List ℕ → List (ℕ × ℕ)
  | a :: b :: l => (a,b) :: pathEdges (b :: l)
  | _ => []

def pathLabels (n i j d : ℕ) : List ℕ := i :: (List.range' n d ++ [j])

def augmentedEdges (n : ℕ) (E : List (ℕ × ℕ)) (i j d : ℕ) : List (ℕ × ℕ) :=
  E ++ pathEdges (pathLabels n i j d)

theorem pathEdges_mem {L : List ℕ} {a b : ℕ} (hab : (a,b) ∈ pathEdges L) :
    a ∈ L ∧ b ∈ L := by
  induction L using List.twoStepInduction with
  | nil => simp [pathEdges] at hab
  | singleton x => simp [pathEdges] at hab
  | cons_cons x y L ih₀ ih =>
    simp only [pathEdges, List.mem_cons] at hab
    rcases hab with he | hab
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      simp
    · have hh := ih y hab
      exact ⟨List.mem_cons_of_mem _ hh.1, List.mem_cons_of_mem _ hh.2⟩

theorem pathLabels_bound {n i j d a : ℕ} (hi : i < n) (hj : j < n)
    (ha : a ∈ pathLabels n i j d) : a < n + d := by
  simp only [pathLabels, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | ha | rfl
  · omega
  · have hh := List.mem_range'.mp ha
    obtain ⟨l, hl, he⟩ := hh
    simp only [Nat.one_mul] at he
    omega
  · omega

theorem pathEdges_sound {V : Type*} {G : SimpleGraph V} (f : ℕ → V)
    {L : List ℕ} (h : (L.map f).IsChain G.Adj) {a b : ℕ}
    (hab : (a,b) ∈ pathEdges L) : G.Adj (f a) (f b) := by
  induction L using List.twoStepInduction with
  | nil => simp [pathEdges] at hab
  | singleton x => simp [pathEdges] at hab
  | cons_cons x y L ih₀ ih =>
    simp only [pathEdges, List.mem_cons] at hab
    rcases hab with he | hab
    · have he' := Prod.mk.inj he
      obtain ⟨rfl, rfl⟩ := he'
      exact List.isChain_cons_cons.mp h |>.1
    · exact ih y (List.IsChain.tail h) hab

namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

def extendedFunction (I : List V) (i : ℕ) : V :=
  if i < n then S.f i else I[i-n]?.getD (S.f 0)

theorem extendedFunction_old (I : List V) {i : ℕ} (hi : i < n) :
    S.extendedFunction I i = S.f i := by simp [extendedFunction, hi]

theorem extendedFunction_new (I : List V) {i : ℕ} (hi : i < I.length) :
    S.extendedFunction I (n + i) = I[i] := by
  simp only [extendedFunction, Nat.not_lt.mpr (Nat.le_add_right n i), ite_false,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi, Option.getD_some]

theorem extendedFunction_inj {I : List V} (hI : I.Nodup)
    (hout : ∀ v ∈ I, v ∉ S.vertices) :
    Set.InjOn (S.extendedFunction I) (Set.Iio (n + I.length)) := by
  intro i hi j hj he
  change i < n + I.length at hi
  change j < n + I.length at hj
  by_cases hin : i < n <;> by_cases hjn : j < n
  · rw [S.extendedFunction_old I hin, S.extendedFunction_old I hjn] at he
    exact S.inj hin hjn he
  · have hji : j - n < I.length := by omega
    have hjj : j = n + (j - n) := by omega
    rw [S.extendedFunction_old I hin, hjj, S.extendedFunction_new I hji] at he
    exact (hout _ (List.getElem_mem hji) (he ▸ S.mem_vertices hin)).elim
  · have hii : i - n < I.length := by omega
    have hii' : i = n + (i - n) := by omega
    rw [S.extendedFunction_old I hjn, hii', S.extendedFunction_new I hii] at he
    exact (hout _ (List.getElem_mem hii) (he.symm ▸ S.mem_vertices hjn)).elim
  · have hii : i - n < I.length := by omega
    have hji : j - n < I.length := by omega
    have hii' : i = n + (i - n) := by omega
    have hjj : j = n + (j - n) := by omega
    have hie : S.extendedFunction I i = I[i-n] := by
      calc
        _ = S.extendedFunction I (n + (i-n)) := congrArg _ hii'
        _ = _ := S.extendedFunction_new I hii
    have hje : S.extendedFunction I j = I[j-n] := by
      calc
        _ = S.extendedFunction I (n + (j-n)) := congrArg _ hjj
        _ = _ := S.extendedFunction_new I hji
    have he' : I[i-n] = I[j-n] := hie.symm.trans (he.trans hje)
    have hh := hI.getElem_inj_iff.mp he'
    omega

theorem extendedFunction_range' (I : List V) :
    (List.range' n I.length).map (S.extendedFunction I) = I := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range', Nat.one_mul, S.extendedFunction_new I hi']

theorem exists_extension {i j d : ℕ} (hi : i < n) (hj : j < n)
    (hp : OutsidePath G S.vertices (S.f i) (S.f j) d) :
    ∃ T : LabelState G Q (n + d) q (augmentedEdges n E i j d),
      ∀ a, a < n → T.f a = S.f a := by
  obtain ⟨I, hIl, hchain, hIn, hout⟩ := hp.to_list
  let g := S.extendedFunction I
  have hold : ∀ a, a < n → g a = S.f a := fun a ha => S.extendedFunction_old I ha
  have hmap : (pathLabels n i j d).map g = S.f i :: I ++ [S.f j] := by
    simp only [pathLabels, List.map_cons, List.map_append, List.map_nil, hold i hi, hold j hj,
      ← hIl, g, S.extendedFunction_range', List.cons_append]
  refine ⟨{
    f := g
    inj := by simpa only [← hIl] using S.extendedFunction_inj hIn hout
    qb := fun a ha => by have := S.qb a ha; omega
    qimage := ?_
    eb := ?_
    edges := ?_ }, hold⟩
  · calc
      Q = S.f '' (↑q : Set ℕ) := S.qimage
      _ = g '' (↑q : Set ℕ) := by
        apply Set.image_congr
        intro a ha
        exact (hold a (S.qb a ha)).symm
  · intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · have hh := S.eb a b hab
      constructor <;> omega
    · have hh := pathEdges_mem hab
      exact ⟨pathLabels_bound hi hj hh.1, pathLabels_bound hi hj hh.2⟩
  · intro a b hab
    rcases hab with hab | hab
    · rcases List.mem_append.mp hab with hab | hab
      · obtain ⟨ha, hb⟩ := S.eb a b hab
        rw [hold a ha, hold b hb]
        exact S.edges a b (Or.inl hab)
      · exact pathEdges_sound g (hmap ▸ hchain) hab
    · rcases List.mem_append.mp hab with hab | hab
      · obtain ⟨hb, ha⟩ := S.eb b a hab
        rw [hold a ha, hold b hb]
        exact S.edges a b (Or.inr hab)
      · exact (pathEdges_sound g (hmap ▸ hchain) hab).symm

end LabelState

 
def LabelCycleValid (n k : ℕ) (E : List (ℕ × ℕ)) (L : List ℕ) : Prop :=
  L.Nodup ∧ L.length = k + 1 ∧ (∀ i ∈ L, i < n) ∧
  L.IsChain (labelAdj E) ∧ ∀ x ∈ L.head?, ∀ y ∈ L.getLast?, labelAdj E y x
instance (n k : ℕ) (E : List (ℕ × ℕ)) (L : List ℕ) :
    Decidable (LabelCycleValid n k E L) := by
  unfold LabelCycleValid
  infer_instance

theorem cycle_of_list {V : Type*} {G : SimpleGraph V} (L : List V)
    (hl : 3 ≤ L.length) (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (he : ∀ x ∈ L.head?, ∀ y ∈ L.getLast?, G.Adj y x) :
    SimpleGraph.cycleGraph L.length ⊑ G := by
  have hne : L ≠ [] := by intro hh; simp [hh] at hl
  let p := SimpleGraph.Walk.ofSupport L hne hc
  have hp : p.IsPath := p.isPath_def.mpr (by simpa [p] using hn)
  have hplen : p.length = L.length - 1 := SimpleGraph.Walk.length_ofSupport _ _
  have hadj := he (L.head hne) (List.head?_eq_some_head hne)
    (L.getLast hne) (List.getLast?_eq_some_getLast hne)
  have hcycle : (SimpleGraph.Walk.cons hadj p).IsCycle := by
    apply (p.cons_isCycle_iff hadj).mpr
    refine ⟨hp, ?_⟩
    intro hh
    have hh' := hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using hh)
    omega
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨_, SimpleGraph.Walk.cons hadj p, hcycle, ?_⟩
  rw [SimpleGraph.Walk.length_cons, hplen]
  omega

theorem LabelState.cycle {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {n k : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)
    (hk : 2 ≤ k) {L : List ℕ} (h : LabelCycleValid n k E L) :
    SimpleGraph.cycleGraph (k + 1) ⊑ G := by
  have hc := cycle_of_list (L.map S.f) (by simp only [List.length_map, h.2.1]; omega)
    (h.1.map_on (fun a ha b hb hab => S.inj (h.2.2.1 a ha) (h.2.2.1 b hb) hab))
    ((List.isChain_map S.f).mpr (h.2.2.2.1.imp (fun {a b} hab => S.edges a b hab))) (by
      intro x hx y hy
      simp only [List.head?_map, List.getLast?_map, Option.mem_map] at hx hy
      obtain ⟨a,ha,rfl⟩ := hx
      obtain ⟨b,hb,rfl⟩ := hy
      exact S.edges b a (h.2.2.2.2 a ha b hb))
  have hlen : (L.map S.f).length = k + 1 := by simp only [List.length_map, h.2.1]
  rw [← hlen]
  exact hc

 

structure OriginalSystem {V : Type*} [Fintype V] (G : SimpleGraph V) (Q : Set V)
    (k t L e : ℕ) where
  P : PathSystem G Q
  optimal : P.Optimal k
  clique : G.IsClique Q
  card : Q.ncard = t
  amount : P.amount = L
  edges : P.edgeCount = e

 

def Improvement (k t L e : ℕ) (C : List (List ℕ)) : Prop :=
  let A := C.flatten.length - t
  let N := t - C.length
  let v := t - (C.filter (fun c => c.length = 1)).length
  (A < k + 1 - t ∧ (L < A ∨ (L = A ∧ N < e))) ∨
  (k + 1 - t ≤ A ∧ A ≤ k + 1 - v)
instance (k t L e : ℕ) (C : List (List ℕ)) : Decidable (Improvement k t L e C) := by
  unfold Improvement
  infer_instance

theorem OriginalSystem.impossible {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k t L e n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)}
    (H : FiniteHyp G k t) (O : OriginalSystem G Q k t L e)
    (S : LabelState G Q n q E) {C : List (List ℕ)}
    (hC : LabelValid n q E C) (hc : Improvement k t L e C) : False := by
  let R := S.system hC
  have hqt : q.card = t := S.card_clique.symm.trans O.card
  have hA : R.amount = C.flatten.length - t := by rw [S.system_amount hC, hqt]
  have he : R.edgeCount = t - C.length := by rw [S.system_edges hC, hqt]
  have hv : R.incident = t - (C.filter (fun c => c.length = 1)).length := by
    rw [S.system_incident hC, hqt]
  change (_ ∧ (_ ∨ (_ ∧ _))) ∨ (_ ∧ _) at hc
  rcases hc with ⟨hsmall, hbetter | ⟨heq,hfewer⟩⟩ | ⟨hl,hu⟩
  · have hh := O.optimal.2.1 R (by rw [O.card, hA]; exact hsmall)
    rw [hA, O.amount] at hh
    omega
  · have hh := O.optimal.2.2 R (by rw [hA, O.amount]; exact heq.symm)
    rw [he, O.edges] at hh
    omega
  · exact R.closing_interval (by have := H.hk; omega) O.clique H.hcycle
      (by rw [O.card]; exact H.htk) (by rw [hA, O.card]; exact hl) (by rw [hA, hv]; exact hu)

 
theorem OutsidePath.restrict {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    {x y : V} {d : ℕ} (h : OutsidePath G Y x y d) (hXY : X ⊆ Y)
    (hx : x ∈ X) (hy : y ∈ X) : OutsidePath G X x y d := by
  obtain ⟨_,_,hne,p,hp,hl,hs⟩ := h
  exact ⟨hx,hy,hne,p,hp,hl,fun v hv hvX => hs v hv (hXY hvX)⟩

theorem LabelState.forbidden_extension {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {n m : ℕ} {q : Finset ℕ} {E F : List (ℕ × ℕ)}
    (S : LabelState G Q n q E) (T : LabelState G Q m q F)
    (hnm : n ≤ m) (he : ∀ i, i < n → T.f i = S.f i)
    {i j d : ℕ} (hi : i < n) (hj : j < n)
    (hno : ¬ OutsidePath G S.vertices (S.f i) (S.f j) d) :
    ¬ OutsidePath G T.vertices (T.f i) (T.f j) d := by
  intro hp
  have hsub : S.vertices ⊆ T.vertices := by
    rintro v ⟨a,ha,rfl⟩
    exact ⟨a, lt_of_lt_of_le ha hnm, he a ha⟩
  rw [he i hi, he j hj] at hp
  exact hno (hp.restrict hsub (S.mem_vertices hi) (S.mem_vertices hj))

abbrev ForbiddenMatrix := List (ℕ × ℕ × ℕ)

def matrixEntry (M : ForbiddenMatrix) (i j d : ℕ) : Prop :=
  (i,j,d) ∈ M ∨ (j,i,d) ∈ M
instance (M : ForbiddenMatrix) (i j d : ℕ) : Decidable (matrixEntry M i j d) := by
  unfold matrixEntry
  infer_instance

structure ValidMatrix {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)
    (M : ForbiddenMatrix) : Prop where
  bounds : ∀ c ∈ M, c.1 < n ∧ c.2.1 < n
  forbidden : ∀ c ∈ M, ¬ OutsidePath G S.vertices (S.f c.1) (S.f c.2.1) c.2.2

namespace ValidMatrix
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} {S : LabelState G Q n q E}
  {M : ForbiddenMatrix} (hM : ValidMatrix S M)
include hM

theorem lookup {i j d : ℕ} (hm : matrixEntry M i j d) :
    ¬ OutsidePath G S.vertices (S.f i) (S.f j) d := by
  rcases hm with hm | hm
  · exact hM.forbidden _ hm
  · intro hp
    exact hM.forbidden _ hm hp.symm

theorem extend {m : ℕ} {F : List (ℕ × ℕ)} (T : LabelState G Q m q F)
    (hnm : n ≤ m) (he : ∀ i, i < n → T.f i = S.f i) : ValidMatrix T M := by
  constructor
  · intro c hc
    exact ⟨lt_of_lt_of_le (hM.bounds c hc).1 hnm, lt_of_lt_of_le (hM.bounds c hc).2 hnm⟩
  · intro c hc
    exact S.forbidden_extension T hnm he (hM.bounds c hc).1 (hM.bounds c hc).2
      (hM.forbidden c hc)

theorem insert {i j d : ℕ} (hi : i < n) (hj : j < n)
    (hno : ¬ OutsidePath G S.vertices (S.f i) (S.f j) d) :
    ValidMatrix S ((i,j,d) :: M) := by
  constructor
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hi,hj⟩
    · exact hM.bounds c hc
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hno
    · exact hM.forbidden c hc

end ValidMatrix

theorem OutsidePath.of_adj {V : Type*} {G : SimpleGraph V} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : G.Adj x y) : OutsidePath G X x y 0 := by
  refine ⟨hx, hy, hxy.ne, SimpleGraph.Walk.cons hxy .nil, ?_, rfl, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simpa using hxy.ne
  · intro v hv _
    simpa only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hv

 
def Excluded (n : ℕ) (M : ForbiddenMatrix) (i lo hi : ℕ) (Z : Finset ℕ) : Prop :=
  (∀ j ∈ Z, j < n ∧ j ≠ i) ∧
  ∀ j ∈ Z, ∀ d ∈ Finset.Icc lo hi, matrixEntry M i j d
instance (n : ℕ) (M : ForbiddenMatrix) (i lo hi : ℕ) (Z : Finset ℕ) :
    Decidable (Excluded n M i lo hi Z) := by
  unfold Excluded
  infer_instance

namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

def imageLabels (Z : Finset ℕ) : Set V := S.f '' (↑Z : Set ℕ)

theorem imageLabels_card (Z : Finset ℕ) (hZ : ∀ j ∈ Z, j < n) :
    (S.imageLabels Z).ncard = Z.card := by
  rw [imageLabels, Set.InjOn.ncard_image (S.inj.mono hZ), Set.ncard_coe_finset]

theorem imageLabels_subset (Z : Finset ℕ) (hZ : ∀ j ∈ Z, j < n) :
    S.imageLabels Z ⊆ S.vertices := by
  rintro v ⟨j,hj,rfl⟩
  exact S.mem_vertices (hZ j hj)

theorem excluded_notMem {M : ForbiddenMatrix} {i lo hi : ℕ} {Z : Finset ℕ}
    (hib : i < n) (hZ : Excluded n M i lo hi Z) : S.f i ∉ S.imageLabels Z := by
  rintro ⟨j,hj,he⟩
  exact (hZ.1 j hj).2 (S.inj (hZ.1 j hj).1 hib he)

theorem excluded_zero {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    {i : ℕ} {Z : Finset ℕ} (hi : i < n) (hZ : Excluded n M i 0 0 Z) :
    ∀ z ∈ S.imageLabels Z, ¬ G.Adj (S.f i) z := by
  rintro z ⟨j,hj,rfl⟩ hij
  exact hM.lookup (hZ.2 j hj 0 (by simp))
    (OutsidePath.of_adj (S.mem_vertices hi) (S.mem_vertices (hZ.1 j hj).1) hij)

theorem excluded_ball {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    {i r : ℕ} {Z : Finset ℕ} (hi : i < n) (hZ : Excluded n M i 1 (r+1) Z) :
    ∀ v ∈ outsideBall G S.vertices (S.f i) r, ∀ z ∈ S.imageLabels Z, ¬ G.Adj v z := by
  intro v hv z hz
  obtain ⟨j,hj,rfl⟩ := hz
  apply outside_ball_misses (S.mem_vertices hi) (S.mem_vertices (hZ.1 j hj).1)
    (fun he => (hZ.1 j hj).2 (S.inj (hZ.1 j hj).1 hi he.symm)) _ v hv
  intro d hd hd'
  exact hM.lookup (hZ.2 j hj d (Finset.mem_Icc.mpr ⟨hd,hd'⟩))

end LabelState

 

inductive BallCertificate where
  | zero (Z : Finset ℕ) (b u : ℕ)
  | succ (previous : BallCertificate) (Z : Finset ℕ) (b u : ℕ)
  deriving DecidableEq
namespace BallCertificate

def radius : BallCertificate → ℕ
  | .zero _ _ _ => 0
  | .succ p _ _ _ => p.radius + 1

def size : BallCertificate → ℕ
  | .zero _ b _ => b
  | .succ _ _ b _ => b

def weight : BallCertificate → ℕ
  | .zero _ _ u => u
  | .succ _ _ _ u => u

def Valid (k t n : ℕ) (M : ForbiddenMatrix) (i : ℕ) : BallCertificate → Prop
  | .zero Z b u => Excluded n M i 0 0 Z ∧ 0 < b ∧ n + b ≤ k + 1 + Z.card ∧
      1 ≤ u ∧ (u ≤ 1 ∨ (u ≤ 2 ∧ t ≤ b))
  | .succ p Z b u => p.Valid k t n M i ∧ Excluded n M i 1 (p.radius+1) Z ∧
      (b ≤ p.size ∨ n + b ≤ k * p.weight + 1 + Z.card) ∧ 1 ≤ u ∧
      (u ≤ p.weight ∨ (u ≤ 2 ∧ t < b) ∨ (u ≤ 3 ∧ max k (2*t) < b) ∨
        (u ≤ 2 ∧ t ≤ p.size ∧ n + t ≤ k + 1 + Z.card))

instance instDecidableValid (k t n : ℕ) (M : ForbiddenMatrix) (i : ℕ) (B : BallCertificate) :
    Decidable (B.Valid k t n M i) :=
  match B with
  | .zero Z b u => by unfold Valid; infer_instance
  | .succ p Z b u => by
    unfold Valid
    exact @instDecidableAnd _ _ (instDecidableValid k t n M i p) inferInstance

theorem sound {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (H : FiniteHyp G k t)
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    {i : ℕ} (hi : i < n) (B : BallCertificate) (h : B.Valid k t n M i) :
    B.size ≤ (outsideBall G S.vertices (S.f i) B.radius).ncard ∧
    1 ≤ B.weight ∧ B.weight ≤ independence G (outsideBall G S.vertices (S.f i) B.radius) := by
  induction B with
  | zero Z b u =>
    rcases h with ⟨hZ,hb,hn,hu,hw⟩
    have hs := H.ball_zero_size (S.mem_vertices hi) (S.imageLabels_subset Z (fun j hj => (hZ.1 j hj).1))
      (S.excluded_notMem hi hZ) (S.excluded_zero hM hi hZ)
    rw [S.card_vertices, S.imageLabels_card Z (fun j hj => (hZ.1 j hj).1)] at hs
    have hbound : b ≤ (outsideBall G S.vertices (S.f i) 0).ncard := by omega
    refine ⟨hbound,hu,?_⟩
    rcases hw with hw | ⟨hw,ht⟩
    · exact hw.trans (independence_pos ((Set.ncard_pos).mp (show 0 < (outsideBall G S.vertices (S.f i) 0).ncard by omega)))
    · exact hw.trans (H.ball_zero_pair (S.mem_vertices hi) (ht.trans hbound))
  | succ p Z b u ih =>
    rcases h with ⟨hp,hZ,hb,hu,hw⟩
    obtain ⟨hsize,hpos,hweight⟩ := ih hp
    have hs := H.ball_step_size hpos hweight
      (S.imageLabels_subset Z (fun j hj => (hZ.1 j hj).1)) (S.excluded_ball hM hi hZ)
    rw [S.card_vertices, S.imageLabels_card Z (fun j hj => (hZ.1 j hj).1)] at hs
    have hsub := outsideBall_subset_succ G S.vertices (S.f i) p.radius
    have hcard := Set.ncard_le_ncard hsub
    have hbound : b ≤ (outsideBall G S.vertices (S.f i) (p.radius+1)).ncard := by
      rcases hb with hb | hb <;> omega
    refine ⟨hbound,hu,?_⟩
    change u ≤ independence G (outsideBall G S.vertices (S.f i) (p.radius+1))
    rcases hw with hw | ⟨hu2,ht⟩ | ⟨hu3,ht⟩ | ⟨hu2,ht,hn⟩
    · exact hw.trans (hweight.trans (independence_mono hsub))
    · exact hu2.trans (H.ball_pair (ht.trans_le hbound))
    · exact hu3.trans (H.ball_triple (ht.trans_le hbound))
    · apply hu2.trans
      apply H.ball_stagnation (S.mem_vertices hi)
        (S.imageLabels_subset Z (fun j hj => (hZ.1 j hj).1)) (S.excluded_notMem hi hZ)
        (ht.trans hsize) _ (S.excluded_ball hM hi hZ)
      simpa only [S.card_vertices, S.imageLabels_card Z (fun j hj => (hZ.1 j hj).1)] using hn

end BallCertificate

inductive PackingOption where
  | singleton (i : ℕ)
  | ball (i : ℕ) (B : BallCertificate)
  deriving DecidableEq

namespace PackingOption

def base : PackingOption → ℕ
  | .singleton i | .ball i _ => i

def radiusCode : PackingOption → ℕ
  | .singleton _ => 0
  | .ball _ B => B.radius + 1

def weight : PackingOption → ℕ
  | .singleton _ => 1
  | .ball _ B => B.weight

def Valid (k t n : ℕ) (M : ForbiddenMatrix) : PackingOption → Prop
  | .singleton i => i < n
  | .ball i B => i < n ∧ B.radius ≤ 2 ∧ B.Valid k t n M i
instance (k t n : ℕ) (M : ForbiddenMatrix) (o : PackingOption) :
    Decidable (o.Valid k t n M) := by
  cases o <;> unfold Valid <;> infer_instance

def Compatible (M : ForbiddenMatrix) (a b : PackingOption) : Prop :=
  a.base ≠ b.base ∧
  if a.radiusCode + b.radiusCode = 0 then matrixEntry M a.base b.base 0
  else ∀ d ∈ Finset.Icc 1 (a.radiusCode+b.radiusCode), matrixEntry M a.base b.base d
instance (M : ForbiddenMatrix) (a b : PackingOption) : Decidable (Compatible M a b) := by
  unfold Compatible
  infer_instance

def vertices {V : Type*} (G : SimpleGraph V) (X : Set V) (f : ℕ → V) : PackingOption → Set V
  | .singleton i => {f i}
  | .ball i B => outsideBall G X (f i) B.radius

theorem weight_le {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (H : FiniteHyp G k t)
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (o : PackingOption) (ho : o.Valid k t n M) :
    o.weight ≤ independence G (o.vertices G S.vertices S.f) := by
  cases o with
  | singleton i => exact independence_pos (Set.singleton_nonempty _)
  | ball i B => exact (B.sound H S hM ho.1 ho.2.2).2.2

theorem separated {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)}
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (a b : PackingOption) (ha : a.Valid k t n M) (hb : b.Valid k t n M)
    (hab : a.Compatible M b) :
    Disjoint (a.vertices G S.vertices S.f) (b.vertices G S.vertices S.f) ∧
    ∀ x ∈ a.vertices G S.vertices S.f, ∀ y ∈ b.vertices G S.vertices S.f, ¬ G.Adj x y := by
  have ha' : a.base < n := by cases a with
    | singleton i => exact ha
    | ball i B => exact ha.1
  have hb' : b.base < n := by cases b with
    | singleton i => exact hb
    | ball i B => exact hb.1
  have hne : S.f a.base ≠ S.f b.base := fun he => hab.1 (S.inj ha' hb' he)
  have hm := hab.2
  cases a with
  | singleton i =>
    cases b with
    | singleton j =>
      simp only [radiusCode, Nat.zero_add, base] at hm
      refine ⟨Set.disjoint_singleton.mpr hne, ?_⟩
      rintro x rfl y rfl hij
      exact hM.lookup hm (OutsidePath.of_adj (S.mem_vertices ha') (S.mem_vertices hb') hij)
    | ball j B =>
      simp only [radiusCode, Nat.zero_add, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte, base] at hm
      constructor
      · apply Set.disjoint_left.mpr
        rintro x rfl hx
        exact outsideBall_subset_compl G S.vertices (S.f j) B.radius hx (S.mem_vertices ha')
      · rintro x rfl y hy hxy
        apply outside_ball_misses (S.mem_vertices hb') (S.mem_vertices ha') hne.symm _ y hy hxy.symm
        intro d hd hd' hp
        exact hM.lookup (hm d (Finset.mem_Icc.mpr ⟨hd,hd'⟩)) hp.symm
  | ball i A =>
    cases b with
    | singleton j =>
      simp only [radiusCode, Nat.add_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte, base] at hm
      constructor
      · apply Set.disjoint_left.mpr
        rintro x hx rfl
        exact outsideBall_subset_compl G S.vertices (S.f i) A.radius hx (S.mem_vertices hb')
      · rintro x hx y rfl hxy
        apply outside_ball_misses (S.mem_vertices ha') (S.mem_vertices hb') hne _ x hx hxy
        intro d hd hd'
        exact hM.lookup (hm d (Finset.mem_Icc.mpr ⟨hd,hd'⟩))
    | ball j B =>
      change (if A.radius+1+(B.radius+1) = 0 then _ else _) at hm
      rw [ite_eq_right (by omega)] at hm
      apply outside_balls_separated (S.mem_vertices ha') (S.mem_vertices hb') hne
      intro d hd hd'
      exact hM.lookup (hm d (Finset.mem_Icc.mpr ⟨hd,by dsimp [radiusCode]; omega⟩))
end PackingOption

end CycleClique

end OAI
