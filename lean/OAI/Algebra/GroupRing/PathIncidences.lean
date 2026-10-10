import Mathlib
import OAI.Algebra.GroupRing.MultiplicityBound

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PathIncidences

section
open scoped Classical BigOperators
open EntropyStages IncidenceStages

namespace Opened
variable {O : Type*} (P : EntropyStages.Pairing O)

/-- Open one cyclic passage into two interval endpoints. -/
def openAt (c : O) : EntropyStages.Pairing O where
  partner o := if o = c ∨ o = P.partner c then o else P.partner o
  involutive o := by
    by_cases h : o = c ∨ o = P.partner c
    · simp only [ite_eq_left h]
    · have h' : ¬ (P.partner o = c ∨ P.partner o = P.partner c) := by
        rintro (he|he)
        · exact h (Or.inr (by rw [← he,P.involutive]))
        · exact h (Or.inl (P.involutive.injective he))
      simp only [ite_eq_right h,ite_eq_right h']
      exact P.involutive o

theorem openAt_fixed_iff (hfree : ∀ o, P.partner o ≠ o) (c o : O) :
    (openAt P c).partner o = o ↔ o = c ∨ o = P.partner c := by
  dsimp [openAt]
  split_ifs with h
  · simp only [h]
  · exact iff_of_false (hfree o) h

theorem openAt_unmatched_card [Fintype O] [DecidableEq O] (hfree : ∀ o, P.partner o ≠ o) (c : O) :
    Fintype.card (openAt P c).Unmatched = 2 := by
  let e : (openAt P c).Unmatched ≃ Bool :=
    { toFun := fun o => if o.val = c then false else true
      invFun := fun b => if b then
        ⟨P.partner c,by rw [openAt_fixed_iff P hfree]; exact Or.inr rfl⟩ else
        ⟨c,by rw [openAt_fixed_iff P hfree]; exact Or.inl rfl⟩
      left_inv := by
        intro o
        apply Subtype.ext
        obtain h|h := (openAt_fixed_iff P hfree c o.val).mp o.property
        · simp [h]
        · simp [h,hfree c]
      right_inv := by
        intro b
        cases b <;> simp [hfree c] }
  exact (Fintype.card_congr e).trans Fintype.card_bool
end Opened

/-- Cyclic consecutive edge incidences. `succ` is the permutation of edge
positions; opening its passage at one position handles an interval path. -/
def cyclePairing {E : Type*} (succ : Equiv.Perm E) : EntropyStages.Pairing (E × Bool) where
  partner x := if x.2 then (succ x.1,false) else (succ.symm x.1,true)
  involutive x := by
    rcases x with ⟨i,b⟩
    cases b <;> simp

theorem cyclePairing_free {E : Type*} (succ : Equiv.Perm E) (x : E × Bool) :
    (cyclePairing succ).partner x ≠ x := by
  rcases x with ⟨i,b⟩
  cases b <;> simp [cyclePairing]

def pathPairing {E : Type*} (succ : Equiv.Perm E) (cut : Option E) : EntropyStages.Pairing (E × Bool) :=
  match cut with
  | none => cyclePairing succ
  | some c => Opened.openAt (cyclePairing succ) (c,false)

theorem pathPairing_card {E : Type*} [Fintype E] (succ : Equiv.Perm E) (cut : Option E) :
    Fintype.card (pathPairing succ cut).Unmatched = if cut.isSome then 2 else 0 := by
  cases cut with
  | none =>
    have : IsEmpty (pathPairing succ none).Unmatched :=
      ⟨fun o => cyclePairing_free succ o.val o.property⟩
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Fintype.card_of_isEmpty]
  | some c =>
    have h := Opened.openAt_unmatched_card _ (cyclePairing_free succ) (c,false)
    rw [← Nat.card_eq_fintype_card] at h ⊢
    exact h

variable {E D V : Type*} (origin : D → V) (reverse : D → D)
  (edge : E → D)
  (succ : Equiv.Perm E) (cut : Option E)

/-- Initial and terminal half-edge of an occurrence, respectively. -/
def port (x : E × Bool) : D := if x.2 then reverse (edge x.1) else edge x.1

theorem partner_turn {x : E × Bool}
    (hne : (pathPairing succ cut).partner x ≠ x) :
    (pathPairing succ cut).partner x = (cyclePairing succ).partner x ∧
    if x.2 then cut ≠ some (succ x.1) else cut ≠ some x.1 := by
  cases cut with
  | none => simp [pathPairing]
  | some c =>
    have hx : ¬ (x = (c,false) ∨ x = (cyclePairing succ).partner (c,false)) := by
      intro hh
      exact hne (by dsimp [pathPairing,Opened.openAt]; rw [ite_eq_left hh])
    refine ⟨by dsimp [pathPairing,Opened.openAt]; rw [ite_eq_right hx],?_⟩
    rcases x with ⟨i,b⟩
    cases b
    · simp only [Bool.false_eq_true,↓reduceIte,ne_eq,Option.some.injEq]
      intro he
      exact hx (Or.inl (Prod.ext he.symm rfl))
    · simp only [↓reduceIte,ne_eq,Option.some.injEq]
      intro he
      exact hx (Or.inr (by
        simp only [cyclePairing,Bool.false_eq_true,↓reduceIte]
        exact Prod.ext (by rw [he,Equiv.symm_apply_apply]) rfl))

/-- The incidence passage data is derived from the actual adjacency and
nonbacktracking conditions, not assumed as an extra vertex-count estimate. -/
def passages
    (hvertex : ∀ i, cut ≠ some (succ i) → origin (edge (succ i)) = origin (reverse (edge i)))
    (hreduced : ∀ i, cut ≠ some (succ i) → edge (succ i) ≠ reverse (edge i)) :
    IncidenceStages.Passages origin (port reverse edge) where
  toPairing := pathPairing succ cut
  location x := by
    by_cases he : (pathPairing succ cut).partner x = x
    · rw [he]
    obtain ⟨hp,hc⟩ := partner_turn succ cut he
    rw [hp]
    rcases x with ⟨i,b⟩
    cases b
    · have ht := hvertex (succ.symm i) (by simpa using hc)
      simpa [cyclePairing,port] using ht.symm
    · simpa [cyclePairing,port] using hvertex i hc
  reduced x he := by
    obtain ⟨hp,hc⟩ := partner_turn succ cut he
    rw [hp]
    rcases x with ⟨i,b⟩
    cases b
    · have ht := hreduced (succ.symm i) (by simpa using hc)
      simpa [cyclePairing,port] using ht.symm
    · simpa [cyclePairing,port] using hreduced i hc

end

open scoped Classical BigOperators
open EntropyStages IncidenceStages

theorem card_toNat {A : Type*} (inst : Fintype A) : @Fintype.card A inst = Nat.card A :=
  (@Nat.card_eq_fintype_card A inst).symm

/-- Disjoint union of the passages of the individual path components. -/
def familyPairing {I : Type*} {O : I → Type*} (P : ∀ i, EntropyStages.Pairing (O i)) :
    EntropyStages.Pairing (Sigma O) where
  partner x := ⟨x.1,(P x.1).partner x.2⟩
  involutive x := by
    rcases x with ⟨i,o⟩
    exact congrArg (Sigma.mk i) ((P i).involutive o)

def unmatchedEquiv {I : Type*} {O : I → Type*} (P : ∀ i, EntropyStages.Pairing (O i)) :
    (familyPairing P).Unmatched ≃ (Σ i, (P i).Unmatched) where
  toFun x := ⟨x.val.1,⟨x.val.2,by
    have h := x.property
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩⟩
  invFun x := ⟨⟨x.1,x.2.val⟩,congrArg (Sigma.mk x.1) x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem family_unmatched_card {I : Type*} [Fintype I] {O : I → Type*}
    [∀ i, Fintype (O i)] (P : ∀ i, EntropyStages.Pairing (O i)) :
    Fintype.card (familyPairing P).Unmatched = ∑ i, Fintype.card (P i).Unmatched := by
  rw [Fintype.card_congr (unmatchedEquiv P), Fintype.card_sigma]

variable {I D V : Type*} [Fintype I] [Fintype D] [Fintype V] {E : I → Type*}
  [∀ i, Fintype (E i)] (origin : D → V) (reverse : D → D)
  (edge : ∀ i, E i → D) (succ : ∀ i, Equiv.Perm (E i)) (cut : ∀ i, Option (E i))
  (hvertex : ∀ i e, cut i ≠ some (succ i e) →
    origin (edge i (succ i e)) = origin (reverse (edge i e)))
  (hreduced : ∀ i e, cut i ≠ some (succ i e) →
    edge i (succ i e) ≠ reverse (edge i e))

def familyPort (x : Σ i, E i × Bool) : D := port reverse (edge x.1) x.2

def familyPassages : IncidenceStages.Passages origin (familyPort reverse edge) where
  toPairing := familyPairing (fun i => pathPairing (succ i) (cut i))
  location x := (passages origin reverse (edge x.1) (succ x.1) (cut x.1)
    (hvertex x.1) (hreduced x.1)).location x.2
  reduced x he := (passages origin reverse (edge x.1) (succ x.1) (cut x.1)
    (hvertex x.1) (hreduced x.1)).reduced x.2 (fun h => he (congrArg (Sigma.mk x.1) h))

include succ hvertex hreduced in
/-- The exact occurrence balance for any union of immersed circles and
intervals. -/
theorem family_vertex_bound :
    (∑ v : V, IncidenceStages.Passages.maxMultiplicity
      (origin := origin) (port := familyPort reverse edge) v) ≤
      (∑ i, Fintype.card (E i)) + ∑ i, if (cut i).isSome then 1 else 0 := by
  apply (familyPassages origin reverse edge succ cut hvertex hreduced).image_vertex_bound
  · simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_bool,
      ← Finset.sum_mul,mul_comm]
  · have h := family_unmatched_card (fun i => pathPairing (succ i) (cut i))
    rw [card_toNat] at h ⊢
    change Nat.card (familyPairing (fun i => pathPairing (succ i) (cut i))).Unmatched = _
    rw [h]
    have hp (i : I) : Fintype.card (pathPairing (succ i) (cut i)).Unmatched =
        if (cut i).isSome then 2 else 0 := pathPairing_card (succ i) (cut i)
    simp_rw [card_toNat] at hp ⊢
    simp_rw [hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num

end TorsionFreeZeroDivisors.PathIncidences

namespace TorsionFreeZeroDivisors.StageSubgraphs
open scoped Classical BigOperators
open PortSubdivision
variable {V D : Type*} [Fintype V] [Fintype D] (Γ : PortGraph V D)

abbrev ActiveD (m : D → ℕ) (j : ℕ) := {d : D // j < m d}
abbrev ActiveV (m : D → ℕ) (j : ℕ) := {v : V // ∃ d, Γ.origin d = v ∧ j < m d}

/-- The actual multiplicity stage has precisely its incident vertices.
No inactive vertices are counted or forced to embed. -/
def stage (m : D → ℕ) (hm : ∀ d, m (Γ.reverse d) = m d) (j : ℕ) :
    PortGraph (ActiveV Γ m j) (ActiveD m j) where
  origin d := ⟨Γ.origin d.val, d.val,rfl,d.property⟩
  reverse d := ⟨Γ.reverse d.val, (hm d.val).symm ▸ d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d.val)
  reverse_ne d he := Γ.reverse_ne d.val (congrArg Subtype.val he)

def maxAt (m : D → ℕ) (v : V) : ℕ :=
  (Finset.univ.filter fun d => Γ.origin d = v).sup m

omit [Fintype V] in
theorem active_iff (m : D → ℕ) (j : ℕ) (v : V) :
    (∃ d, Γ.origin d = v ∧ j < m d) ↔ j < maxAt Γ m v := by
  simp [maxAt,Finset.lt_sup_iff]

theorem vertex_card (m : D → ℕ) (j : ℕ) :
    Fintype.card (ActiveV Γ m j) = ∑ v : V, if j < maxAt Γ m v then 1 else 0 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (active_iff Γ m j))]
  simp only [Fintype.card_subtype,Finset.card_filter]

theorem sum_vertex_card (m : D → ℕ) (M : ℕ) (hm : ∀ d, m d ≤ M) :
    (∑ j : Fin M, Fintype.card (ActiveV Γ m j.val)) = ∑ v : V, maxAt Γ m v := by
  simp_rw [vertex_card]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  have hv : maxAt Γ m v ≤ M := Finset.sup_le (fun d _ => hm d)
  rw [← Finset.card_filter]
  have he : (Finset.univ.filter fun j : Fin M => j.val < maxAt Γ m v) =
      Finset.univ.filter fun j => j.val ∈ Finset.range (maxAt Γ m v) := by simp
  rw [he]
  rw [← Fintype.card_subtype]
  let e : {j : Fin M // j.val ∈ Finset.range (maxAt Γ m v)} ≃ Fin (maxAt Γ m v) :=
    { toFun := fun j => ⟨j.val.val,Finset.mem_range.mp j.property⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt hv⟩,Finset.mem_range.mpr j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- Literal undirected stage edges; both orientations name a single edge. -/
def edges : Finset (Sym2 D) := Finset.univ.image (fun d => s(d,Γ.reverse d))
def edgeName (d : D) : edges Γ := ⟨s(d,Γ.reverse d),Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩⟩

omit [Fintype V] in
theorem fiber_card (e : edges Γ) : Fintype.card {d : D // edgeName Γ d = e} = 2 := by
  obtain ⟨d,_,hd⟩ := Finset.mem_image.mp e.property
  have he : e = edgeName Γ d := Subtype.ext hd.symm
  subst e
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter fun x => edgeName Γ x = edgeName Γ d) = {d,Γ.reverse d} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [Subtype.ext_iff]
    change s(x,Γ.reverse x) = s(d,Γ.reverse d) ↔ x = d ∨ x = Γ.reverse d
    rw [Sym2.eq_iff]
    constructor
    · rintro (⟨h,_⟩|⟨h,_⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl|rfl)
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,Γ.reverse_reverse d⟩
  rw [hf,Finset.card_pair (Ne.symm (Γ.reverse_ne d))]

omit [Fintype V] in
/-- A fixed-point-free port involution has exactly two darts per edge. -/
theorem two_edges : 2*(edges Γ).card = Fintype.card D := by
  have h := Fintype.card_sigma (α := fun e : edges Γ => {d : D // edgeName Γ d = e})
  simp_rw [fiber_card] at h
  have he : (Σ e : edges Γ, {d : D // edgeName Γ d = e}) ≃ D :=
    Equiv.sigmaFiberEquiv (edgeName Γ)
  rw [Fintype.card_congr he] at h
  simpa [mul_comm] using h.symm

omit [Fintype V] in
theorem sum_dart_card (m : D → ℕ) (M : ℕ) (hm : ∀ d, m d ≤ M) :
    (∑ j : Fin M, Fintype.card (ActiveD m j.val)) = ∑ d : D, m d := by
  simp only [ActiveD,Fintype.card_subtype,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.card_filter,← Fintype.card_subtype]
  let e : {j : Fin M // j.val < m d} ≃ Fin (m d) :=
    { toFun := fun j => ⟨j.val.val,j.property⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt (hm d)⟩,j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

omit [Fintype V] in
/-- Counting actual stage edges with multiplicity, not expected edges. -/
theorem sum_edge_card (m : D → ℕ) (hr : ∀ d, m (Γ.reverse d) = m d)
    (M H : ℕ) (hm : ∀ d, m d ≤ M) (hH : ∑ d, m d = 2*H) :
    (∑ j : Fin M, (edges (stage Γ m hr j.val)).card) = H := by
  have h2 : 2*(∑ j : Fin M, (edges (stage Γ m hr j.val)).card) = 2*H := by
    rw [Finset.mul_sum]
    simp_rw [two_edges]
    rw [sum_dart_card m M hm,hH]
  omega

variable {I : Type*} [Fintype I] {E : I → Type*} [∀ i, Fintype (E i)]
  (edge : ∀ i, E i → D)

def multiplicity (d : D) : ℕ := IncidenceStages.Passages.multiplicity
  (port := PathIncidences.familyPort Γ.reverse edge) d

omit [Fintype V] [Fintype D] in
/-- Source traversal multiplicity agrees on the two orientations. -/
theorem multiplicity_reverse (d : D) :
    multiplicity Γ edge (Γ.reverse d) = multiplicity Γ edge d := by
  let flip : (Σ i, E i × Bool) ≃ (Σ i, E i × Bool) :=
    { toFun := fun x => ⟨x.1,x.2.1,!x.2.2⟩
      invFun := fun x => ⟨x.1,x.2.1,!x.2.2⟩
      left_inv := by rintro ⟨i,e,b⟩; cases b <;> rfl
      right_inv := by rintro ⟨i,e,b⟩; cases b <;> rfl }
  have hf (x : Σ i, E i × Bool) :
      PathIncidences.familyPort Γ.reverse edge (flip x) =
        Γ.reverse (PathIncidences.familyPort Γ.reverse edge x) := by
    rcases x with ⟨i,e,b⟩
    cases b
    · rfl
    · exact (Γ.reverse_reverse (edge i e)).symm
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv flip (fun o => by
    rw [hf]
    constructor
    · intro h
      rw [h,Γ.reverse_reverse]
    · intro h
      exact Γ.reverse_reverse.injective ((Γ.reverse_reverse d).symm ▸ h))

omit [Fintype V] in
/-- Each edge occurrence contributes one incidence in each orientation. -/
theorem sum_multiplicity : (∑ d : D, multiplicity Γ edge d) =
    2*(∑ i, Fintype.card (E i)) := by
  have h := Fintype.card_sigma (α := fun d : D =>
    {o : Σ i, E i × Bool // PathIncidences.familyPort Γ.reverse edge o = d})
  have e := Equiv.sigmaFiberEquiv (PathIncidences.familyPort Γ.reverse edge)
  rw [Fintype.card_congr e] at h
  simpa only [multiplicity,IncidenceStages.Passages.multiplicity,Fintype.card_sigma,
    Fintype.card_prod,Fintype.card_bool,← Finset.sum_mul,mul_comm] using h.symm

variable (succ : ∀ i, Equiv.Perm (E i)) (cut : ∀ i, Option (E i))
  (hvertex : ∀ i e, cut i ≠ some (succ i e) →
    Γ.origin (edge i (succ i e)) = Γ.origin (Γ.reverse (edge i e)))
  (hreduced : ∀ i e, cut i ≠ some (succ i e) →
    edge i (succ i e) ≠ Γ.reverse (edge i e))

include succ hvertex hreduced in
/-- Exact vertex inequality for the actual stages
of the immersed family, derived from the literal consecutive passages. -/
theorem family_vertex_total (M : ℕ) (hm : ∀ d, multiplicity Γ edge d ≤ M) :
    (∑ j : Fin M, Fintype.card (ActiveV Γ (multiplicity Γ edge) j.val)) ≤
      (∑ i, Fintype.card (E i)) + ∑ i, if (cut i).isSome then 1 else 0 := by
  rw [sum_vertex_card Γ _ M hm]
  exact PathIncidences.family_vertex_bound Γ.origin Γ.reverse edge succ cut hvertex hreduced

omit [Fintype V] in
/-- Every traversal contributes exactly one undirected edge over all stages. -/
theorem family_edge_total (M : ℕ) (hm : ∀ d, multiplicity Γ edge d ≤ M) :
    (∑ j : Fin M, (edges (stage Γ (multiplicity Γ edge)
      (multiplicity_reverse Γ edge) j.val)).card) = ∑ i, Fintype.card (E i) :=
  sum_edge_card Γ _ (multiplicity_reverse Γ edge) M _ hm (sum_multiplicity Γ edge)

include succ hvertex hreduced in
/-- The n-exponent of actual stage embeddings is nonpositive; the initial
vertex saving is claimed only at the first stage of every rooted interval. -/
theorem family_exponent_nonpos (M : ℕ) (hM : 0 < M)
    (hm : ∀ d, multiplicity Γ edge d ≤ M) :
    (∑ j : Fin M, ((Fintype.card (ActiveV Γ (multiplicity Γ edge) j.val) : ℤ) -
      (edges (stage Γ (multiplicity Γ edge) (multiplicity_reverse Γ edge) j.val)).card -
      if j.val = 0 then (∑ i, if (cut i).isSome then 1 else 0 : ℕ) else 0)) ≤ 0 := by
  have hv := family_vertex_total Γ edge succ cut hvertex hreduced M hm
  have he := family_edge_total Γ edge M hm
  have hp : (∑ j : Fin M, if j.val = 0 then
      ((∑ i, if (cut i).isSome then 1 else 0 : ℕ) : ℤ) else 0) =
      ((∑ i, if (cut i).isSome then 1 else 0 : ℕ) : ℤ) := by
    rw [Finset.sum_eq_single (⟨0,hM⟩ : Fin M)]
    · simp
    · intro b _ hb
      have hb0 : b.val ≠ 0 := fun h => hb (Fin.ext h)
      simp [hb0]
    · simp
  simp only [Finset.sum_sub_distrib, Nat.cast_ite, Nat.cast_zero]
  rw [hp,← Nat.cast_sum,← Nat.cast_sum,he]
  have hv' : ((∑ j : Fin M, Fintype.card (ActiveV Γ (multiplicity Γ edge) j.val)) : ℤ) ≤
      ((∑ i, Fintype.card (E i)) : ℤ) +
      ((∑ i, if (cut i).isSome then 1 else 0 : ℕ) : ℤ) := by exact_mod_cast hv
  omega

end TorsionFreeZeroDivisors.StageSubgraphs

end

end OAI
