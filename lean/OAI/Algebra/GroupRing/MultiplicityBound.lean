import Mathlib
import OAI.Algebra.GroupRing.EntropyStages
import OAI.Algebra.GroupRing.ChainCoverage
import OAI.Algebra.GroupRing.IntervalSelfLinks

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MultiplicityBound
open SimpleGraph WeightedCycles
variable {V : Type*} {G : SimpleGraph V}

/-- Every nonempty reduced closed walk pays at least the cycle girth, even
when subdivision spokes have zero weight. -/
theorem closed_weight (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (L : ℝ) (hg : ∀ a (c : G.Walk a a), c.IsCycle → L ≤ weight w c)
    {a : V} (p : G.Walk a a) (hp : p.edges.IsChain (· ≠ ·)) (hne : ¬ p.Nil) :
    L ≤ weight w p := by
  have hn : ¬p.IsPath := fun h => hne (Walk.isPath_iff_nil.mp h)
  obtain ⟨b,c,hc,hcp⟩ := reduced_not_path_cycle w hw p hp hn
  exact (hg b c hc).trans hcp

/-- Vertex visits in any reduced walk are uniformly bounded in terms of
expanded length divided by girth. This counts occurrences, not just edges. -/
theorem visit_bound [DecidableEq V] (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ a (c : G.Walk a a), c.IsCycle → L ≤ weight w c)
    {a b : V} (p : G.Walk a b) (hp : p.edges.IsChain (· ≠ ·)) (x : V) :
    (p.support.count x : ℝ)*L ≤ weight w p + L := by
  induction hn : p.length using Nat.strong_induction_on generalizing a b p with
  | h n ih =>
    cases p with
    | nil =>
      by_cases hx : a=x
      · subst x; simp
      · simpa [hx] using hL
    | @cons a b c hab r =>
      have hr : r.edges.IsChain (· ≠ ·) := (List.isChain_cons.mp hp).2
      have il := ih r.length (by simp only [Walk.length_cons] at hn; omega)
        r hr rfl
      by_cases hax : a=x
      · subst x
        by_cases hmem : a ∈ r.support
        · let pref : G.Walk a a := Walk.cons hab (r.takeUntil a hmem)
          let suff := r.dropUntil a hmem
          have hsplit : pref.append suff = Walk.cons hab r := by
            simp only [pref,suff,Walk.cons_append,Walk.take_spec]
          have hpref : pref.edges.IsChain (· ≠ ·) := hp.prefix (by
            rw [← hsplit,Walk.edges_append]
            exact List.prefix_append _ _)
          have hsuff : suff.edges.IsChain (· ≠ ·) := hr.suffix (r.edges_dropUntil_suffix_edges hmem)
          have hpw : L ≤ weight w pref := closed_weight w hw L hg pref hpref (by simp [pref])
          have hsw := ih suff.length (by
            have hlen := r.length_dropUntil_le_length hmem
            simp only [Walk.length_cons] at hn
            dsimp [suff]
            omega) suff hsuff rfl
          have hcount : (Walk.cons hab r).support.count a = suff.support.count a + 1 := by
            have ht := r.count_support_takeUntil_eq_one hmem
            have hstart : suff.support = a :: suff.support.tail := by
              exact (List.cons_head_tail (by simp : suff.support ≠ [])).symm.trans (by simp)
            have hrc : r.support.count a = suff.support.count a := by
              conv_lhs => rw [← r.take_spec hmem]
              simp only [Walk.support_append,List.count_append,ht]
              change 1+suff.support.tail.count a=suff.support.count a
              have hh := congrArg (fun xs : List V => xs.count a) hstart
              simp only [List.count_cons_self] at hh
              omega
            simp [hrc,Nat.add_comm]
          have hweight : weight w (Walk.cons hab r)=weight w pref+weight w suff := by
            rw [← hsplit,weight_append]
          rw [hcount,hweight]
          push_cast
          nlinarith
        · have hz : r.support.count a=0 := List.count_eq_zero.mpr hmem
          simp only [Walk.support_cons,List.count_cons_self,hz,Nat.zero_add,Nat.cast_one,one_mul]
          linarith [weight_nonneg w hw (Walk.cons hab r)]
      · have hc : (Walk.cons hab r).support.count x=r.support.count x := by
          simp [hax]
        rw [hc,weight_cons]
        linarith [hw s(a,b)]

end TorsionFreeZeroDivisors.MultiplicityBound

namespace TorsionFreeZeroDivisors.PathMultiplicity
open SimpleGraph WeightedCycles WeightedMoore WeightedPortMoore
open PortSubdivision SuppressedMoore
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)
local instance : BEq (V ⊕ D) := instBEqOfDecidableEq

/-- Convert a literal nonempty dart path to the dependent chain encoding. -/
def pathChain (x : D) : (xs : List D) → Chain D xs.length
  | [] => x
  | y::ys => (x,pathChain y ys)

@[simp] lemma pathChain_head (x : D) (xs : List D) : head (pathChain x xs)=x := by
  cases xs <;> rfl

@[simp] lemma pathChain_word (x : D) (xs : List D) : outWord (pathChain x xs)=x::xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => exact congrArg (List.cons x) (ih y)

lemma pathChain_good (x : D) (xs : List D)
    (hr : (x::xs).IsChain (PortWalk.step Γ.origin Γ.reverse)) : Good Γ (pathChain x xs) := by
  induction xs generalizing x with
  | nil => trivial
  | cons y ys ih =>
    exact ⟨by simpa only [pathChain,pathChain_head] using (List.isChain_cons_cons.mp hr).1, ih y hr.tail⟩

/-- A port appears once per traversal of its undirected edge in the physical
subdivision walk, in either direction. Spoke vertices do not add occurrences. -/
lemma draw_count {k : ℕ} (p : Chain D k) (hp : Good Γ p) (x : D) :
    (draw Γ p hp).support.count (Sum.inr x) =
      (outWord p).count x + (outWord p).count (Γ.reverse x) := by
  classical
  induction k with
  | zero =>
    change ([Sum.inr p, Sum.inr (Γ.reverse p)] : List (V ⊕ D)).count (Sum.inr x) =
      [p].count x + [p].count (Γ.reverse x)
    have he : Γ.reverse p=x ↔ p=Γ.reverse x := by
      constructor
      · intro h; rw [←h,Γ.reverse_reverse]
      · intro h; rw [h,Γ.reverse_reverse]
    simp only [List.count_cons,List.count_nil,beq_iff_eq,Sum.inr.injEq,he]
    omega
  | succ k ih =>
    change (Sum.inr p.1 :: Sum.inr (Γ.reverse p.1) ::
      Sum.inl (Γ.origin (Γ.reverse p.1)) :: (draw Γ p.2 hp.2).support).count (Sum.inr x) =
      (p.1 :: outWord p.2).count x + (p.1 :: outWord p.2).count (Γ.reverse x)
    have he : Γ.reverse p.1=x ↔ p.1=Γ.reverse x := by
      constructor
      · intro h; rw [←h,Γ.reverse_reverse]
      · intro h; rw [h,Γ.reverse_reverse]
    simp only [List.count_cons,beq_iff_eq,Sum.inr.injEq,reduceCtorEq,he,ih]
    simp only [ite_false]
    omega

lemma pathChain_cost (x : D) (xs : List D) :
    cost (fun _ : D => (1:ℝ)) (pathChain x xs) = (x::xs).length := by
  induction xs generalizing x with
  | nil => simp [pathChain,cost]
  | cons y ys ih =>
    change 1+cost (fun _ : D => (1:ℝ)) (pathChain y ys) = ((x::y::ys).length:ℝ)
    rw [ih]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

/-- The undirected edge count for a literal port path bounds each orientation
in particular. -/
theorem path_edge_bound (L : ℝ) (hL : 0≤L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (p : List D) (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse)) (x : D) :
    ((p.count x + p.count (Γ.reverse x):ℕ):ℝ)*L ≤ p.length + L := by
  cases p with
  | nil => simpa using hL
  | cons y ys =>
    let q := pathChain y ys
    have hq : Good Γ q := pathChain_good Γ y ys hp
    have h := MultiplicityBound.visit_bound (edgeWeight (fun _ : D => 1))
      (edgeWeight_nonneg _ (by intro d; norm_num)) L hL hg
      (draw Γ q hq) (draw_reduced Γ q hq) (Sum.inr x)
    rw [draw_count Γ q hq x,draw_weight Γ _ (by intro d; rfl)] at h
    simpa only [q,pathChain_word,pathChain_cost] using h

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

lemma reverse_mem_word (d : B) (x : D) (hx : x∈word Γ mark h2 d) :
    Γ.reverse x∈word Γ mark h2 ((suppressed Γ mark h2).reverse d) := by
  obtain ⟨i,rfl⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  let e := (suppressed Γ mark h2).reverse d
  let k := len d
  have hj : k-i.val-1 < len e := by
    rw [chainLength_reverse]
    have hi := i.isLt
    change i.val < k at hi
    omega
  rw [mem_word_iff]
  refine ⟨⟨k-i.val-1,hj⟩,?_⟩
  have hf := endpoint_reverse Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (x:=d) (i:=k-i.val) (by change k-i.val ≤ k; omega)
  have he : k-(k-i.val)=i.val := by omega
  have hs : k-i.val=(k-i.val-1)+1 := by have hi := i.isLt; change i.val < k at hi; omega
  change F^[k-i.val] e.val = τ (F^[k-(k-i.val)] d.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (Γ.reverse (F^[k-i.val-1] e.val))) = τ (τ (F^[i.val] d.val)) at h
  rw [turn_involutive Γ.origin mark h2,turn_involutive Γ.origin mark h2] at h
  have hh := congrArg Γ.reverse h
  rwa [Γ.reverse_reverse] at hh

lemma undirected_multiplicity_constant (ds : List B) (d : B) (x : D)
    (hx : x∈word Γ mark h2 d) :
    (ds.flatMap (word Γ mark h2)).count x +
      (ds.flatMap (word Γ mark h2)).count (Γ.reverse x) =
      ds.count d + ds.count ((suppressed Γ mark h2).reverse d) := by
  rw [multiplicity_constant Γ mark h2 ds d x hx,
    multiplicity_constant Γ mark h2 ds _ _ (reverse_mem_word Γ mark h2 d x hx)]

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.PathMultiplicity
open PortSubdivision WeightedCycles WeightedPortMoore
open scoped BigOperators Classical
variable {V D I : Type*} (Γ : PortGraph V D) [Fintype I]

/-- Summing the literal edge-multiplicity estimate over the given path system. -/
theorem total_edge_bound (L : ℝ) (hL : 0≤L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (p : I → List D) (hp : ∀ i, (p i).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (x : D) :
    (∑ i, ((p i).count x + (p i).count (Γ.reverse x)):ℕ)*L ≤
      (∑ i, (p i).length : ℕ)+(Fintype.card I:ℝ)*L := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => path_edge_bound Γ L hL hg (p i) (hp i) x)
  rw [← Finset.sum_mul] at h
  simpa only [Nat.cast_sum,Nat.cast_add,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] using h

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains WeightedCycles
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}

lemma start_mem_word (d : B) : d.val∈word Γ mark h2 d := by
  rw [mem_word_iff]
  exact ⟨⟨0,chainLength_pos Γ mark h2 d⟩,rfl⟩

omit [Fintype D] in
lemma sum_count_eq_length {A : Type*} [Fintype A] [BEq A] [LawfulBEq A] (p : List A) :
    ∑ a, p.count a = p.length := by
  classical
  induction p with
  | nil => simp
  | cons b p ih =>
    simp only [List.count_cons,beq_iff_eq,Finset.sum_add_distrib,List.length_cons,ih]
    simp

/-- The number of chain traversals is bounded independently of their lengths. -/
theorem total_chain_bound {I : Type*} [Fintype I]
    (L : ℝ) (hL : 0≤L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (ds : I → List B)
    (hp : ∀ i, ((ds i).flatMap (word Γ mark h2)).IsChain (PortWalk.step Γ.origin Γ.reverse)) :
    (∑ i, (ds i).length : ℕ)*L ≤ (Fintype.card B:ℝ)*
      ((∑ i, ((ds i).flatMap (word Γ mark h2)).length : ℕ)+(Fintype.card I:ℝ)*L) := by
  let H : ℝ := (∑ i, ((ds i).flatMap (word Γ mark h2)).length : ℕ)
  have hd (d : B) : (∑ i, (ds i).count d : ℕ)*L ≤ H+(Fintype.card I:ℝ)*L := by
    have h := PathMultiplicity.total_edge_bound Γ L hL hg
      (fun i => (ds i).flatMap (word Γ mark h2)) hp d.val
    have he : (∑ i, (ds i).count d : ℕ) ≤
        ∑ i, (((ds i).flatMap (word Γ mark h2)).count d.val +
          ((ds i).flatMap (word Γ mark h2)).count (Γ.reverse d.val)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [multiplicity_constant Γ mark h2 _ d d.val (start_mem_word Γ mark h2 d)]
      exact Nat.le_add_right _ _
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast he) hL).trans h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun d _ => hd d)
  rw [← Finset.sum_mul] at hs
  have he : ∑ d : B, (∑ i, (ds i).count d : ℕ) = ∑ i, (ds i).length := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_count_eq_length (ds i)
  simpa only [← Nat.cast_sum,he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,H] using hs

/-- A uniform integer bound in terms of the length, path count, and chain count. -/
theorem bounded_chain_traversals {I : Type*} [Fintype I]
    (C : ℝ) (hC : 0≤C) (K R : ℕ) (hI : Fintype.card I≤K) (hB : Fintype.card B≤R)
    (L : ℝ) (hL : 0<L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (ds : I → List B)
    (hp : ∀ i, ((ds i).flatMap (word Γ mark h2)).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hH : (∑ i, ((ds i).flatMap (word Γ mark h2)).length : ℕ) ≤ C*L) :
    ∑ i, (ds i).length ≤ ⌈(R:ℝ)*(C+K)⌉₊ := by
  have h := total_chain_bound Γ mark h2 L hL.le hg ds hp
  have hib : (Fintype.card I:ℝ) ≤ K := by exact_mod_cast hI
  have hbb : (Fintype.card B:ℝ) ≤ R := by exact_mod_cast hB
  have hh : (∑ i, (ds i).length : ℕ)*L ≤ (R:ℝ)*(C+(K:ℝ))*L := by
    calc
      _ ≤ (Fintype.card B:ℝ)*((C:ℝ)*L+(K:ℝ)*L) :=
        h.trans (mul_le_mul_of_nonneg_left
          (add_le_add hH (mul_le_mul_of_nonneg_right hib hL.le)) (Nat.cast_nonneg _))
      _ = (Fintype.card B:ℝ)*(C+K)*L := by ring
      _ ≤ (R:ℝ)*(C+K)*L := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbb (by positivity)) hL.le
  have he := (mul_le_mul_iff_left₀ hL).mp hh
  exact_mod_cast he.trans (Nat.le_ceil _)

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.IncidenceStages
open scoped Classical BigOperators
open EntropyStages
variable {O D V : Type*} [Fintype O] [Fintype D] [Fintype V]

/-- An incidence remembers its occurrence and which (oriented) half-edge it
uses. Passages pair incidences at a vertex; path endpoints are fixed points. -/
structure Passages (origin : D → V) (port : O → D) extends Pairing O where
  location : ∀ o, origin (port (partner o)) = origin (port o)
  reduced : ∀ o, partner o ≠ o → port (partner o) ≠ port o

namespace Passages
variable {origin : D → V} {port : O → D} (P : Passages origin port)

abbrev AtVertex (v : V) := {o : O // origin (port o) = v}

def localPairing (v : V) : Pairing (AtVertex (origin := origin) (port := port) v) where
  partner o := ⟨P.partner o.val,(P.location o.val).trans o.property⟩
  involutive o := Subtype.ext (P.involutive o.val)

def multiplicity (d : D) : ℕ := Fintype.card {o : O // port o = d}
def maxMultiplicity (v : V) : ℕ :=
  (Finset.univ.filter (fun d => origin d = v)).sup (multiplicity (port := port))

omit [Fintype V] [Fintype D] in
theorem local_multiplicity (d : D) :
    Fintype.card {o : AtVertex (origin := origin) (port := port) (origin d) // port o.val = d} =
      multiplicity (port := port) d := by
  let e : {o : AtVertex (origin := origin) (port := port) (origin d) // port o.val = d} ≃
      {o : O // port o = d} :=
    { toFun := fun o => ⟨o.val.val,o.property⟩
      invFun := fun o => ⟨⟨o.val,congrArg origin o.property⟩,o.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.card_congr e

omit [Fintype V] in
theorem local_balance (v : V) :
    2 * maxMultiplicity (origin := origin) (port := port) v ≤
      Fintype.card (AtVertex (origin := origin) (port := port) v) +
        Fintype.card (P.localPairing v).Unmatched := by
  by_cases hem : (Finset.univ.filter (fun d => origin d = v)).Nonempty
  · obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup _ hem (multiplicity (port := port))
    have hdv : origin d = v := (Finset.mem_filter.mp hd).2
    have hb := (P.localPairing v).color_balance (fun o => port o.val) d (by
      intro o ho
      exact P.reduced o.val (by intro h; exact ho (Subtype.ext h)))
    have hc : Fintype.card {o : AtVertex (origin := origin) (port := port) v // port o.val = d} =
        multiplicity (port := port) d := by
      subst v
      exact local_multiplicity d
    rw [hc] at hb
    simpa only [maxMultiplicity,he] using hb
  · have he : Finset.univ.filter (fun d => origin d = v) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hem
    simp [maxMultiplicity,he]

omit [Fintype D] in
theorem sum_vertex_cards :
    (∑ v : V, Fintype.card (AtVertex (origin := origin) (port := port) v)) = Fintype.card O := by
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    Fintype.sum_fiberwise (fun o => origin (port o)) (fun _ => (1 : ℕ))

omit [Fintype D] in
theorem sum_endpoint_cards :
    (∑ v : V, Fintype.card (P.localPairing v).Unmatched) = Fintype.card P.toPairing.Unmatched := by
  have hc (v : V) : Fintype.card (P.localPairing v).Unmatched =
      Fintype.card {o : P.toPairing.Unmatched // origin (port o.val) = v} := by
    let e : (P.localPairing v).Unmatched ≃
        {o : P.toPairing.Unmatched // origin (port o.val) = v} :=
      { toFun := fun o => ⟨⟨o.val.val,congrArg Subtype.val o.property⟩,o.val.property⟩
        invFun := fun o => ⟨⟨o.val.val,o.property⟩,Subtype.ext o.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  simp_rw [hc]
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    Fintype.sum_fiberwise (fun o : P.toPairing.Unmatched => origin (port o.val)) (fun _ => (1 : ℕ))

/-- Exact incidence balance before any probabilities or asymptotic estimates.
It remains valid when a loop contributes two distinct half-edges at a vertex. -/
theorem total_balance :
    2 * (∑ v : V, maxMultiplicity (origin := origin) (port := port) v) ≤
      Fintype.card O + Fintype.card P.toPairing.Unmatched := by
  calc
    _ = ∑ v : V, 2 * maxMultiplicity (origin := origin) (port := port) v := by rw [Finset.mul_sum]
    _ ≤ ∑ v : V, (Fintype.card (AtVertex (origin := origin) (port := port) v) +
      Fintype.card (P.localPairing v).Unmatched) := Finset.sum_le_sum (fun v _ => P.local_balance v)
    _ = _ := by rw [Finset.sum_add_distrib,sum_vertex_cards,P.sum_endpoint_cards]

/-- Each edge occurrence has two incidences, and zero or one interval
contributes zero or two endpoints. -/
theorem image_vertex_bound (H iota : ℕ) (hH : Fintype.card O = 2*H)
    (hiota : Fintype.card P.toPairing.Unmatched = 2*iota) :
    (∑ v : V, maxMultiplicity (origin := origin) (port := port) v) ≤ H+iota := by
  have h := P.total_balance
  rw [hH,hiota] at h
  omega

end Passages
end TorsionFreeZeroDivisors.IncidenceStages

end

end OAI
