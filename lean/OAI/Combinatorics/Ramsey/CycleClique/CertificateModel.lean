import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.ChainProfiles
import OAI.Combinatorics.Ramsey.CycleClique.ChainRearrangement
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.LargeSystems
import OAI.Combinatorics.Ramsey.CycleClique.MarkedChains
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def PackingValid (k t n : ℕ) (M : ForbiddenMatrix) (P : Finset PackingOption) : Prop :=
  (∀ o ∈ P, o.Valid k t n M) ∧
  (∀ a ∈ P, ∀ b ∈ P, a ≠ b → a.Compatible M b) ∧ k < ∑ o ∈ P, o.weight
instance (k t n : ℕ) (M : ForbiddenMatrix) (P : Finset PackingOption) :
    Decidable (PackingValid k t n M P) := by
  unfold PackingValid
  infer_instance

theorem packing_impossible {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (H : FiniteHyp G k t)
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (P : Finset PackingOption) (hP : PackingValid k t n M P) : False := by
  have hs := sum_independence_local G (fun o => o.vertices G S.vertices S.f) P
    (fun a ha b hb hab => (a.separated S hM b (hP.1 a ha) (hP.1 b hb) (hP.2.1 a ha b hb hab)).1)
    (fun a ha b hb hab => (a.separated S hM b (hP.1 a ha) (hP.1 b hb) (hP.2.1 a ha b hb hab)).2)
  have hw : ∑ o ∈ P, o.weight ≤ ∑ o ∈ P, independence G (o.vertices G S.vertices S.f) :=
    Finset.sum_le_sum (fun o ho => o.weight_le H S hM (hP.1 o ho))
  exact (Nat.not_lt_of_ge (hw.trans (hs.trans H.hα))) hP.2.2

 

inductive FiniteCertificate where
  | system (C : List (List ℕ))
  | cycle (C : List ℕ)
  | packing (P : Finset PackingOption)
  | edge (i j : ℕ)
  | forbid (i j d : ℕ) (reason next : FiniteCertificate)
  deriving DecidableEq
namespace FiniteCertificate

def Valid (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) (L e : ℕ)
    (M : ForbiddenMatrix) : FiniteCertificate → Prop
  | .system C => LabelValid n q E C ∧ Improvement k t L e C
  | .cycle C => LabelCycleValid n k E C
  | .packing P => PackingValid k t n M P
  | .edge i j => i < n ∧ j < n ∧ labelAdj E i j ∧ matrixEntry M i j 0
  | .forbid i j d R N => i < n ∧ j < n ∧
      R.Valid k t (n+d) q (augmentedEdges n E i j d) L e M ∧
      N.Valid k t n q E L e ((i,j,d)::M)

instance instDecidableValid (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold Valid; infer_instance
  | .forbid i j d R N => by
    unfold Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (instDecidableValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (instDecidableValid k t n q E L e ((i,j,d)::M) N)))

theorem sound {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t L e : ℕ} (H : FiniteHyp G k t) (O : OriginalSystem G Q k t L e)
    (C : FiniteCertificate) {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)}
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (h : C.Valid k t n q E L e M) : False := by
  induction C generalizing n E M with
  | system C => exact O.impossible H S h.1 h.2
  | cycle C => exact H.hcycle (S.cycle (by have := H.hk; omega) h)
  | packing P => exact packing_impossible H S hM P h
  | edge i j =>
    exact hM.lookup h.2.2.2 (OutsidePath.of_adj (S.mem_vertices h.1)
      (S.mem_vertices h.2.1) (S.edges i j h.2.2.1))
  | forbid i j d R N ihR ihN =>
    obtain ⟨hi,hj,hR,hN⟩ := h
    have hno : ¬ OutsidePath G S.vertices (S.f i) (S.f j) d := by
      intro hp
      obtain ⟨T,hT⟩ := S.exists_extension hi hj hp
      exact ihR T (hM.extend T (by omega) hT) hR
    exact ihN S (hM.insert hi hj hno) hN
end FiniteCertificate
open scoped SimpleGraph

 
def normalizedChain (A : List ℕ) : List ℕ := min A A.reverse

theorem normalizedChain_cases (A : List ℕ) : normalizedChain A = A ∨ normalizedChain A = A.reverse :=
  min_choice A A.reverse

theorem normalizedChain_normal (A : List ℕ) : normalizedChain A ≤ (normalizedChain A).reverse := by
  rcases normalizedChain_cases A with h | h
  · rw [h]
    exact h.symm.trans_le (min_le_right A A.reverse)
  · rw [h, List.reverse_reverse]
    exact h.symm.trans_le (min_le_left A A.reverse)

def canonicalPattern (D : List (List ℕ)) : List (List ℕ) :=
  (D.map normalizedChain).mergeSort (fun a b => decide (a ≤ b))

theorem canonicalPattern_sorted (D : List (List ℕ)) : (canonicalPattern D).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : List ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total a b)
    (D.map normalizedChain)
  simpa only [canonicalPattern, decide_eq_true_eq] using h

theorem canonicalPattern_normal (D : List (List ℕ)) :
    ∀ A ∈ canonicalPattern D, A ≤ A.reverse := by
  intro A hA
  obtain ⟨B,hB,rfl⟩ := List.mem_map.mp ((List.mergeSort_perm _ _).mem_iff.mp hA)
  exact normalizedChain_normal B

theorem ClosedChain.reverse {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (hc : ClosedChain G Q c) : ClosedChain G Q c.reverse := by
  refine ⟨by simpa using hc.nonempty, ?_, ?_, ?_⟩
  · exact List.isChain_reverse.mpr (hc.edges.imp (fun _ _ h => h.symm))
  · exact List.isChain_reverse.mpr (hc.positive.imp (fun _ _ h => h.symm))
  · simpa using And.intro hc.ends.2 hc.ends.1

 

theorem normalize_amounts {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {C : List (List V)} {D : List (List ℕ)} (hD : List.Forall₂ (ChainAmounts Q) C D)
    (hC : ∀ c ∈ C, ClosedChain G Q c) :
    ∃ C', C'.flatten.Perm C.flatten ∧ C'.length = C.length ∧
      List.Forall₂ (ChainAmounts Q) C' (D.map normalizedChain) ∧
      ∀ c ∈ C', ClosedChain G Q c := by
  induction hD with
  | nil => exact ⟨[], List.Perm.refl _, rfl, .nil, by simp⟩
  | @cons c A C D hc hD ih =>
    obtain ⟨C',hp,hl,hD',hC'⟩ := ih (fun d hd => hC d (by simp [hd]))
    rcases normalizedChain_cases A with ha | ha
    · refine ⟨c::C', ?_, by simp [hl], ?_, ?_⟩
      · exact (List.Perm.refl c).append hp
      · simpa only [List.map_cons, ha] using List.Forall₂.cons hc hD'
      · intro d hd
        exact (List.mem_cons.mp hd).elim (fun he => he ▸ hC c (by simp)) (hC' d)
    · refine ⟨c.reverse::C', ?_, by simp [hl], ?_, ?_⟩
      · exact (List.reverse_perm c).append hp
      · simpa only [List.map_cons, ha] using List.Forall₂.cons hc.reverse hD'
      · intro d hd
        exact (List.mem_cons.mp hd).elim (fun he => he ▸ (hC c (by simp)).reverse) (hC' d)

theorem PathSystem.canonical_realization {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    ∃ (R : PathSystem G Q) (D : List (List ℕ)),
      List.Forall₂ (ChainAmounts Q) R.chains D ∧
      D.Pairwise (· ≤ ·) ∧ (∀ A ∈ D, A ≤ A.reverse) ∧
      R.amount = P.amount ∧ R.edgeCount = P.edgeCount := by
  obtain ⟨A,D,hD,hperm⟩ := P.exists_profile
  obtain ⟨C,hCperm,hClen,hCD,hC⟩ := normalize_amounts hD (fun c hc => P.closed_chain hc)
  have hdperm := List.mergeSort_perm (D.map normalizedChain) (fun a b => decide (a ≤ b))
  obtain ⟨C',hDC',hCperm'⟩ := List.perm_comp_forall₂ hdperm hCD.flip
  have hf : C'.flatten.Perm P.chains.flatten := hCperm'.flatten.trans hCperm
  have hc : ∀ c ∈ C', ClosedChain G Q c := fun c hc => hC c (hCperm'.mem_iff.mp hc)
  let R : PathSystem G Q := {
    chains := C'
    nonempty := fun c hc' => (hc c hc').nonempty
    nodup := hf.nodup_iff.mpr P.nodup
    edges := fun c hc' => (hc c hc').edges
    positive := fun c hc' => (hc c hc').positive
    ends := fun c hc' => (hc c hc').ends
    cover := fun v hv => hf.mem_iff.mpr (P.cover v hv) }
  refine ⟨R, canonicalPattern D, hDC'.flip, canonicalPattern_sorted D,
    canonicalPattern_normal D, ?_, ?_⟩
  · exact congrArg (fun z => z - Q.ncard) hf.length_eq
  · have hl := hCperm'.length_eq.trans hClen
    exact congrArg (fun z => Q.ncard - z) hl

namespace PathSystem

theorem optimal_of_same {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k : ℕ} {P R : PathSystem G Q} (hP : P.Optimal k)
    (ha : R.amount = P.amount) (he : R.edgeCount = P.edgeCount) : R.Optimal k := by
  unfold Optimal at hP ⊢
  simpa only [ha,he] using hP

end PathSystem

 
def chainOrder (A : List ℕ) : ℕ := A.sum + A.length + 1

def chainClique (b : ℕ) : List ℕ → List ℕ
  | [] => [b]
  | a::A => b :: chainClique (b+a+1) A

def patternChainsFrom (b : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => []
  | A::D => List.range' b (chainOrder A) :: patternChainsFrom (b+chainOrder A) D

def patternCliqueFrom (b : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | A::D => chainClique b A ++ patternCliqueFrom (b+chainOrder A) D

def patternOrder (D : List (List ℕ)) : ℕ := (D.map chainOrder).sum

def patternClique (D : List (List ℕ)) : Finset ℕ := (patternCliqueFrom 0 D).toFinset

def patternEdges (D : List (List ℕ)) : List (ℕ × ℕ) :=
  (patternChainsFrom 0 D).flatMap pathEdges ++
    ((patternCliqueFrom 0 D).product (patternCliqueFrom 0 D)).filter (fun p => p.1 < p.2)

def patternAmount (D : List (List ℕ)) : ℕ := D.flatten.sum

def patternSize (D : List (List ℕ)) : ℕ := D.flatten.length + D.length

def patternEdgeCount (D : List (List ℕ)) : ℕ := D.flatten.length

@[simp] theorem patternOrder_nil : patternOrder [] = 0 := rfl
@[simp] theorem patternOrder_cons (A : List ℕ) (D : List (List ℕ)) :
    patternOrder (A::D) = chainOrder A + patternOrder D := rfl

@[simp] theorem patternChainsFrom_length (b : ℕ) (D : List (List ℕ)) :
    (patternChainsFrom b D).length = D.length := by
  induction D generalizing b with
  | nil => rfl
  | cons A D ih => simp [patternChainsFrom, ih]

theorem patternChainsFrom_flatten (b : ℕ) (D : List (List ℕ)) :
    (patternChainsFrom b D).flatten = List.range' b (patternOrder D) := by
  induction D generalizing b with
  | nil => simp [patternChainsFrom]
  | cons A D ih =>
    simp only [patternChainsFrom, List.flatten_cons, ih, patternOrder_cons]
    simpa only [Nat.one_mul] using (List.range'_append (step := 1) (s := b) (m := chainOrder A) (n := patternOrder D))

theorem patternOrder_eq (D : List (List ℕ)) : patternOrder D = patternAmount D + patternSize D := by
  induction D with
  | nil => rfl
  | cons A D ih =>
    simp only [patternOrder_cons, chainOrder, patternAmount, patternSize, List.flatten_cons,
      List.sum_append, List.length_append, List.length_cons] at ih ⊢
    omega

theorem chainClique_bounds {b i : ℕ} {A : List ℕ} (hi : i ∈ chainClique b A) :
    b ≤ i ∧ i < b + chainOrder A := by
  induction A generalizing b with
  | nil => simp only [chainClique, List.mem_singleton] at hi; subst i; simp [chainOrder]
  | cons a A ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp [chainOrder]
    · obtain ⟨hl,hu⟩ := ih hi
      simp only [chainOrder, List.sum_cons, List.length_cons] at *
      omega

theorem patternCliqueFrom_bounds {b i : ℕ} {D : List (List ℕ)}
    (hi : i ∈ patternCliqueFrom b D) : b ≤ i ∧ i < b + patternOrder D := by
  induction D generalizing b with
  | nil => simp [patternCliqueFrom] at hi
  | cons A D ih =>
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨hl,hu⟩ := chainClique_bounds hi
      exact ⟨hl,by simp only [patternOrder_cons]; omega⟩
    · obtain ⟨hl,hu⟩ := ih hi
      exact ⟨by omega,by simp only [patternOrder_cons]; omega⟩

theorem map_range_getD {V : Type*} (c : List V) (v : V) :
    (List.range' 0 c.length).map (fun i => c.getD i v) = c := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Nat.zero_add]
  exact c.getD_eq_getElem v hi'

theorem ChainAmounts.clique_map {V : Type*} {Q : Set V} [DecidablePred (· ∈ Q)] {c : List V} {A : List ℕ}
    (hA : ChainAmounts Q c A) (f : ℕ → V) {b : ℕ}
    (hmap : (List.range' b (chainOrder A)).map f = c) :
    (chainClique b A).map f = c.filter (fun v => decide (v ∈ Q)) := by
  induction hA generalizing b with
  | singleton x hx =>
    simpa [chainOrder, chainClique, hx] using hmap
  | step x y I B A hx hI hout htail ih =>
    have hh := congrArg List.head? hmap
    have hhead : f b = x := by
      simpa only [chainOrder, List.sum_cons, List.length_cons, List.range'_succ,
        List.map_cons, List.head?_cons, Option.some.injEq] using hh
    have hd := congrArg (List.drop (I.length+1)) hmap
    rw [← List.map_drop, List.drop_range'] at hd
    have hlen : chainOrder (I.length::A) - (I.length+1) = chainOrder A := by
      simp only [chainOrder, List.sum_cons, List.length_cons]
      omega
    simp only [Nat.mul_one, hlen, List.drop_succ_cons, List.drop_left] at hd
    have htailmap : (List.range' (b+I.length+1) (chainOrder A)).map f = y::B := by
      simpa only [Nat.add_assoc] using hd
    have hIfilter : I.filter (fun v => decide (v ∈ Q)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      simpa using hout
    rw [chainClique, List.map_cons, hhead, ih htailmap]
    conv_rhs => rw [List.filter_cons]
    simp only [hx, decide_true, ↓reduceIte, List.filter_append, hIfilter, List.nil_append]

theorem amounts_order {V : Type*} {Q : Set V} {C : List (List V)} {D : List (List ℕ)}
    (h : List.Forall₂ (ChainAmounts Q) C D) : C.flatten.length = patternOrder D := by
  induction h with
  | nil => rfl
  | @cons c A C D hc h ih =>
    simp only [List.flatten_cons, List.length_append, patternOrder_cons, ←ih]
    exact congrArg (· + C.flatten.length) hc.count.2.1

theorem amounts_shape {V : Type*} {Q : Set V} [DecidablePred (· ∈ Q)] {C : List (List V)} {D : List (List ℕ)}
    (h : List.Forall₂ (ChainAmounts Q) C D) (f : ℕ → V) {b : ℕ}
    (hmap : (List.range' b (patternOrder D)).map f = C.flatten) :
    (patternChainsFrom b D).map (List.map f) = C ∧
    (patternCliqueFrom b D).map f = C.flatten.filter (fun v => decide (v ∈ Q)) := by
  induction h generalizing b with
  | nil => simp [patternChainsFrom,patternCliqueFrom]
  | @cons c A C D hc h ih =>
    have hsplit : (List.range' b (chainOrder A)).map f ++
        (List.range' (b+chainOrder A) (patternOrder D)).map f = c ++ C.flatten := by
      rw [←List.map_append]
      rw [show List.range' b (chainOrder A) ++ List.range' (b+chainOrder A) (patternOrder D) =
        List.range' b ((chainOrder A)+(patternOrder D)) by simp]
      exact hmap
    obtain ⟨hfirst,hrest⟩ := List.append_inj hsplit (by simpa [chainOrder] using hc.count.2.1.symm)
    obtain ⟨hshape,hclique⟩ := ih hrest
    constructor
    · simp only [patternChainsFrom, List.map_cons, hfirst, hshape]
    · simp only [patternCliqueFrom, List.map_append, hc.clique_map f hfirst, hclique,
        List.flatten_cons, List.filter_append]

 

noncomputable def PathSystem.labelState {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (hQ : G.IsClique Q)
    {D : List (List ℕ)} (hD : List.Forall₂ (ChainAmounts Q) P.chains D) (v : V) :
    LabelState G Q (patternOrder D) (patternClique D) (patternEdges D) := by
  classical
  let f : ℕ → V := fun i => P.chains.flatten.getD i v
  have hlen := amounts_order hD
  have hmap : (List.range' 0 (patternOrder D)).map f = P.chains.flatten := by
    rw [←hlen]
    exact map_range_getD _ _
  obtain ⟨hshape,hclique⟩ := amounts_shape hD f hmap
  have hq : Q = f '' (↑(patternClique D) : Set ℕ) := by
    ext x
    constructor
    · intro hx
      have hm : x ∈ (patternCliqueFrom 0 D).map f := by
        rw [hclique]
        exact List.mem_filter.mpr ⟨P.cover x hx, by simpa using hx⟩
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
      exact ⟨i, List.mem_toFinset.mpr hi, rfl⟩
    · rintro ⟨i,hi,rfl⟩
      have hm : f i ∈ (patternCliqueFrom 0 D).map f :=
        List.mem_map.mpr ⟨i,List.mem_toFinset.mp hi,rfl⟩
      rw [hclique] at hm
      simpa using (List.mem_filter.mp hm).2
  have hinj : Set.InjOn f (Set.Iio (patternOrder D)) := by
    intro i hi j hj he
    exact (List.Nodup.getD_inj (hlen ▸ hi) (hlen ▸ hj) P.nodup).mp he
  have hqb : ∀ i ∈ patternClique D, i < patternOrder D := by
    intro i hi
    simpa using (patternCliqueFrom_bounds (List.mem_toFinset.mp hi)).2
  have heb : ∀ a b, (a,b) ∈ patternEdges D → a < patternOrder D ∧ b < patternOrder D := by
    intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · obtain ⟨c,hc,hab⟩ := List.mem_flatMap.mp hab
      obtain ⟨ha,hb⟩ := pathEdges_mem hab
      have hal : a ∈ (patternChainsFrom 0 D).flatten := List.mem_flatten.mpr ⟨c,hc,ha⟩
      have hbl : b ∈ (patternChainsFrom 0 D).flatten := List.mem_flatten.mpr ⟨c,hc,hb⟩
      rw [patternChainsFrom_flatten] at hal hbl
      simp only [List.mem_range'] at hal hbl
      exact ⟨by omega, by omega⟩
    · obtain ⟨hab,_⟩ := List.mem_filter.mp hab
      obtain ⟨ha,hb⟩ := List.mem_product.mp hab
      exact ⟨hqb a (List.mem_toFinset.mpr ha), hqb b (List.mem_toFinset.mpr hb)⟩
  have hadj : ∀ a b, (a,b) ∈ patternEdges D → G.Adj (f a) (f b) := by
    intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · obtain ⟨c,hc,hab⟩ := List.mem_flatMap.mp hab
      have hcm : c.map f ∈ P.chains := by
        rw [←hshape]
        exact List.mem_map.mpr ⟨c,hc,rfl⟩
      exact pathEdges_sound f (P.edges _ hcm) hab
    · obtain ⟨hab,hlt⟩ := List.mem_filter.mp hab
      obtain ⟨ha,hb⟩ := List.mem_product.mp hab
      have hai := hqb a (List.mem_toFinset.mpr ha)
      have hbi := hqb b (List.mem_toFinset.mpr hb)
      apply hQ
      · rw [hq]; exact ⟨a,List.mem_toFinset.mpr ha,rfl⟩
      · rw [hq]; exact ⟨b,List.mem_toFinset.mpr hb,rfl⟩
      · intro he
        have hh := hinj hai hbi he
        have hh' : a < b := of_decide_eq_true hlt
        omega
  exact {
    f := f
    inj := hinj
    qb := hqb
    qimage := hq
    eb := heb
    edges := fun a b hab => hab.elim (hadj a b) (fun h => (hadj b a h).symm) }

theorem PathSystem.profile_parameters {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {D : List (List ℕ)} (hD : List.Forall₂ (ChainAmounts Q) P.chains D) :
    patternSize D = Q.ncard ∧ patternAmount D = P.amount ∧
    patternEdgeCount D = P.edgeCount ∧ ∀ a ∈ D.flatten, 0 < a := by
  obtain ⟨ha,he,hpos⟩ := AmountProfile.count (show AmountProfile P D.flatten from ⟨D,hD,List.Perm.refl _⟩)
  have hl := hD.length_eq
  have hle := P.chains_length_le
  refine ⟨?_,ha,he,hpos⟩
  change D.flatten.length+D.length = Q.ncard
  change D.flatten.length = Q.ncard - P.chains.length at he
  omega

 
def chainChoices : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | l+1, B => [] :: (List.range B).flatMap (fun a =>
      (chainChoices l (B-(a+1))).map (fun A => (a+1)::A))

theorem mem_chainChoices {A : List ℕ} {l B : ℕ}
    (hl : A.length ≤ l) (hB : A.sum ≤ B) (hpos : ∀ a ∈ A, 0 < a) :
    A ∈ chainChoices l B := by
  induction l generalizing A B with
  | zero =>
    have ha : A = [] := List.length_eq_zero_iff.mp (by omega)
    simp [ha,chainChoices]
  | succ l ih =>
    cases A with
    | nil => simp [chainChoices]
    | cons a A =>
      have ha : 0 < a := hpos a (by simp)
      have hs : a + A.sum ≤ B := by simpa using hB
      simp only [chainChoices, List.mem_cons, List.cons_ne_nil, false_or,
        List.mem_flatMap, List.mem_map]
      refine ⟨a-1, List.mem_range.mpr (by omega), A, ?_, ?_⟩
      · apply ih
        · simpa using hl
        · omega
        · intro b hb; exact hpos b (by simp [hb])
      · congr 1; omega

 

def patternChoices (t B : ℕ) (lower : List ℕ) : List (List (List ℕ)) :=
  if _ht : t = 0 then [[]] else
    (chainChoices (t-1) B).flatMap (fun A =>
      if A ≤ A.reverse ∧ lower ≤ A then
        (patternChoices (t-(A.length+1)) (B-A.sum) A).map (A::·)
      else [])
termination_by t
decreasing_by omega

@[simp] theorem patternSize_cons (A : List ℕ) (D : List (List ℕ)) :
    patternSize (A::D) = A.length + 1 + patternSize D := by
  simp [patternSize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem patternAmount_cons (A : List ℕ) (D : List (List ℕ)) :
    patternAmount (A::D) = A.sum + patternAmount D := by
  simp [patternAmount]

theorem mem_patternChoices {D : List (List ℕ)} {t B : ℕ} {lower : List ℕ}
    (ht : patternSize D = t) (hB : patternAmount D ≤ B)
    (hpos : ∀ a ∈ D.flatten, 0 < a) (hs : D.Pairwise (· ≤ ·))
    (hn : ∀ A ∈ D, A ≤ A.reverse) (hl : ∀ A ∈ D, lower ≤ A) :
    D ∈ patternChoices t B lower := by
  induction D generalizing t B lower with
  | nil =>
    have ht' : t = 0 := ht.symm
    simp [ht',patternChoices]
  | cons A D ih =>
    have ht' : A.length+1+patternSize D = t := by simpa using ht
    have ht0 : t ≠ 0 := by omega
    have haB : A.sum+patternAmount D ≤ B := by simpa using hB
    have hA : A ∈ chainChoices (t-1) B := mem_chainChoices (by omega) (by omega)
      (fun a ha => hpos a (by simp [ha]))
    rw [patternChoices, dite_eq_right ht0]
    apply List.mem_flatMap.mpr
    refine ⟨A,hA,?_⟩
    rw [ite_eq_left ⟨hn A (by simp),hl A (by simp)⟩]
    apply List.mem_map.mpr
    refine ⟨D,ih ?_ (by omega) (fun a ha => hpos a (by simp [ha]))
      (List.pairwise_cons.mp hs).2 (fun C hC => hn C (by simp [hC]))
      (List.pairwise_cons.mp hs).1, rfl⟩
    omega

end CycleClique

end OAI
