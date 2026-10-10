import OAI.Probability.FKMaps.ExcursionGeometry
import OAI.Probability.FKMaps.Noncrossing

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

lemma orbit_eq_iff {n : ℕ} (s : Equiv.Perm (Dart n)) (d e : Dart n) :
    orbit s d=orbit s e ↔ s.SameCycle d e := Quotient.eq

lemma orbit_perm {n : ℕ} (s : Equiv.Perm (Dart n)) (d : Dart n) :
    orbit s (s d)=orbit s d := by
  apply Quotient.sound
  exact (Equiv.Perm.sameCycle_apply_left).2 (Equiv.Perm.SameCycle.refl s d)

lemma closed_of_sameCycle {n : ℕ} {s : Equiv.Perm (Dart n)} {P : Dart n → Prop}
    (hs : ∀ d,P d → P (s d)) {d e : Dart n} (hd : P d) (h : s.SameCycle d e) : P e := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have hp (j : ℕ) : P ((s^j) d) := by
    induction j with
    | zero => simpa using hd
    | succ j ih => simpa only [pow_succ',Equiv.Perm.mul_apply] using hs _ ih
  exact hk ▸ hp k

/-- Graph connectivity propagates a dart property through the two generating
permutations. This is the precise permutation form of connected rooted-map
rigidity, including loops and repeated edges. -/
lemma connected_dart_induction {n : ℕ} {a s : Equiv.Perm (Dart n)}
    (ha : Function.Involutive a) (hc : (spanningGraph a s univ).Connected)
    {P : Dart n → Prop} {d₀ : Dart n} (h₀ : P d₀)
    (haP : ∀ d,P d → P (a d)) (hsP : ∀ d,P d → P (s d)) : ∀ d,P d := by
  have hcycle {d e : Dart n} (hd : P d) (he : orbit s d=orbit s e) : P e :=
    closed_of_sameCycle hsP hd ((orbit_eq_iff ..).1 he)
  have hstep {v w : Orbit s} (h : (spanningGraph a s univ).Adj v w)
      (hv : ∀ d,orbit s d=v → P d) : ∀ d,orbit s d=w → P d := by
    rcases h.2 with ⟨d,_,hd,he⟩ | ⟨d,_,he,hd⟩
    · intro e he'
      exact hcycle (haP d (hv d hd)) (he.trans he'.symm)
    · intro e he'
      have hh := haP (a d) (hv (a d) hd)
      rw [ha d] at hh
      exact hcycle hh (he.trans he'.symm)
  have hall (v : Orbit s) : ∀ d,orbit s d=v → P d := by
    have hp := (SimpleGraph.reachable_iff_reflTransGen ..).1 (hc (orbit s d₀) v)
    induction hp with
    | refl => exact fun d hd => hcycle h₀ hd.symm
    | tail hp hadj ih => exact hstep hadj ih
  exact fun d => hall (orbit s d) d rfl

lemma MapIso.refl {n : ℕ} (M : LabelledMap n) : MapIso M M :=
  ⟨Equiv.refl _,rfl,fun _ => rfl,fun _ => rfl⟩

lemma MapIso.symm {n : ℕ} {M N : LabelledMap n} (h : MapIso M N) : MapIso N M := by
  obtain ⟨r,h₀,ha,hs⟩ := h
  refine ⟨r.symm,?_,?_,?_⟩
  · exact (r.symm_apply_eq).2 h₀.symm
  · intro d
    apply r.injective
    simpa using (ha (r.symm d)).symm
  · intro d
    apply r.injective
    simpa using (hs (r.symm d)).symm

lemma MapIso.trans {n : ℕ} {M N K : LabelledMap n} (h : MapIso M N) (h' : MapIso N K) :
    MapIso M K := by
  obtain ⟨r,hr,ha,hs⟩ := h
  obtain ⟨r',hr',ha',hs'⟩ := h'
  refine ⟨r.trans r',?_,?_,?_⟩
  · simp [hr,hr']
  · intro d
    simp only [Equiv.trans_apply,ha',ha]
  · intro d
    simp only [Equiv.trans_apply,hs',hs]

lemma mapIso_eqvGen {n : ℕ} {M N : LabelledMap n} :
    Relation.EqvGen MapIso M N ↔ MapIso M N := by
  constructor
  · intro h
    induction h with
    | rel _ _ he => exact he
    | refl M => exact MapIso.refl M
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  · exact Relation.EqvGen.rel _ _

/-- A rooted connected rotation system has no nontrivial automorphisms.
Consequently the source's distinguished corners carry no symmetry divisor. -/
lemma rooted_automorphism_eq_one {n : ℕ} (M : LabelledMap n) (r : Equiv.Perm (Dart n))
    (h₀ : r 0=0) (ha : ∀ d,M.val.1 (r d)=r (M.val.1 d))
    (hs : ∀ d,M.val.2 (r d)=r (M.val.2 d)) : r=1 := by
  apply Equiv.ext
  change ∀ d,r d=d
  apply connected_dart_induction M.property.1 M.property.2.2.1 (P := fun d => r d=d) h₀
  · intro d hd
    rw [← ha,hd]
  · intro d hd
    rw [← hs,hd]

lemma root_isomorphism_unique {n : ℕ} {M N : LabelledMap n}
    {r r' : Equiv.Perm (Dart n)}
    (hr : r 0=0) (ha : ∀ d,N.val.1 (r d)=r (M.val.1 d))
    (hs : ∀ d,N.val.2 (r d)=r (M.val.2 d))
    (hr' : r' 0=0) (ha' : ∀ d,N.val.1 (r' d)=r' (M.val.1 d))
    (hs' : ∀ d,N.val.2 (r' d)=r' (M.val.2 d)) : r=r' := by
  have hh : r.trans r'.symm=1 := by
    apply rooted_automorphism_eq_one M
    · change r'.symm (r 0)=0
      rw [hr]
      exact r'.symm_apply_eq.mpr hr'.symm
    · intro d
      apply r'.injective
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
      rw [← ha',Equiv.apply_symm_apply,ha]
    · intro d
      apply r'.injective
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
      rw [← hs',Equiv.apply_symm_apply,hs]
  apply Equiv.ext
  intro d
  have he := congrArg (fun e : Equiv.Perm (Dart n) => r' (e d)) hh
  simpa using he

end FKCRT
end


noncomputable section
open Set Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT.MapFinite

abbrev CycleQuot {α : Type*} (s : Equiv.Perm α) := Quotient (Equiv.Perm.SameCycle.setoid s)

instance {α : Type*} [Finite α] (s : Equiv.Perm α) : Fintype (CycleQuot s) := Fintype.ofFinite _

lemma sameCycle_involution {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (x y : α) : s.SameCycle x y ↔ y=x ∨ y=s x := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    rw [← hk]
    clear h hk y
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      rcases ih with he | he
      · exact Or.inr (congrArg s he)
      · exact Or.inl ((congrArg s he).trans (hs x))
  · intro h
    rcases h with h | h
    · simpa only [h] using Equiv.Perm.SameCycle.refl s x
    · rw [h]
      exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl s x)

lemma mk_eq_iff_involution {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (d : α) (q : CycleQuot s) :
    Quotient.mk _ d=q ↔ d=q.out ∨ d=s q.out := by
  calc
    Quotient.mk _ d=q ↔ Quotient.mk _ d=Quotient.mk _ q.out := by rw [Quotient.out_eq]
    _ ↔ s.SameCycle d q.out := Quotient.eq
    _ ↔ s.SameCycle q.out d := ⟨Equiv.Perm.SameCycle.symm,Equiv.Perm.SameCycle.symm⟩
    _ ↔ d=q.out ∨ d=s q.out := sameCycle_involution s hs q.out d

lemma card_orbit_fiber {α : Type*} [Fintype α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (q : CycleQuot s) :
    Fintype.card {d : α // Quotient.mk (Equiv.Perm.SameCycle.setoid s) d=q}=
      if s q.out=q.out then 1 else 2 := by
  classical
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun d : α => Quotient.mk (Equiv.Perm.SameCycle.setoid s) d=q)=
      {q.out,s q.out} := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    exact mk_eq_iff_involution s hs d q
  rw [he]
  by_cases h : s q.out=q.out
  · simp [h]
  · simp [h,Ne.symm h]

lemma fixed_out_iff {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (d : α) :
    s (Quotient.mk (Equiv.Perm.SameCycle.setoid s) d).out=
      (Quotient.mk (Equiv.Perm.SameCycle.setoid s) d).out ↔ s d=d := by
  have he := (mk_eq_iff_involution s hs d (Quotient.mk _ d)).mp rfl
  rcases he with he | he
  · conv_rhs => rw [he]
  · conv_rhs => rw [he,hs]
    exact eq_comm

def fixedOrbitEquiv {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) : {d : α // s d=d} ≃ {q : CycleQuot s // s q.out=q.out} where
  toFun d := ⟨Quotient.mk _ d.val,(fixed_out_iff s hs d.val).mpr d.property⟩
  invFun q := ⟨q.val.out,q.property⟩
  left_inv d := by
    apply Subtype.ext
    have he := (mk_eq_iff_involution s hs d.val (Quotient.mk _ d.val)).mp rfl
    rcases he with he | he
    · exact he.symm
    · have hh := congrArg s he
      rw [d.property,hs] at hh
      exact hh.symm
  right_inv q := Subtype.ext (Quotient.out_eq q.val)

/-- Orbit count for an involution, retaining its fixed points. A reversal
has no fixed darts, whereas the path-map vertex rotation has exactly two. -/
lemma twice_card_orbits {α : Type*} [Fintype α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) :
    2*Fintype.card (CycleQuot s)=Fintype.card α+Fintype.card {d : α // s d=d} := by
  classical
  have hd : Fintype.card α=∑ q : CycleQuot s,if s q.out=q.out then 1 else 2 := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (Equiv.Perm.SameCycle.setoid s))),
      Fintype.card_sigma]
    exact Finset.sum_congr rfl (fun q _ => card_orbit_fiber s hs q)
  have hf : Fintype.card {d : α // s d=d}=∑ q : CycleQuot s,if s q.out=q.out then 1 else 0 := by
    rw [Fintype.card_congr (fixedOrbitEquiv s hs),Fintype.card_subtype]
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [hd,hf,← Finset.sum_add_distrib]
  calc
    2*Fintype.card (CycleQuot s)=∑ _q : CycleQuot s,2 := by simp [mul_comm]
    _ = _ := Finset.sum_congr rfl (fun q _ => by split_ifs <;> rfl)

end FKCRT.MapFinite
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

lemma spanningGraph_reachable_reversal {n : ℕ} (a s : Equiv.Perm (Dart n)) (d : Dart n) :
    (spanningGraph a s univ).Reachable (orbit s d) (orbit s (a d)) := by
  classical
  by_cases h : orbit s d=orbit s (a d)
  · rw [h]
  · apply SimpleGraph.Adj.reachable
    exact ⟨h,Or.inl ⟨d,mem_univ _,rfl,rfl⟩⟩

lemma spanningGraph_connected_of_face_cycle {n : ℕ} (a s : Equiv.Perm (Dart n))
    (hc : ∀ d e,(s*a).SameCycle d e) : (spanningGraph a s univ).Connected := by
  refine {preconnected := ?_, nonempty := ⟨orbit s 0⟩}
  intro v w
  induction v using Quotient.inductionOn with | h d =>
    induction w using Quotient.inductionOn with | h e =>
      obtain ⟨k,hk⟩ := (hc d e).exists_nat_pow_eq
      rw [← hk]
      have hp (j : ℕ) : (spanningGraph a s univ).Reachable (orbit s d) (orbit s (((s*a)^j) d)) := by
        induction j with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ j ih =>
          rw [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,orbit_perm]
          exact ih.trans (spanningGraph_reachable_reversal a s _)
      exact hp k

def pathRotation (n : ℕ) : Equiv.Perm (Dart n) := finRotate (2*(n+1))*Fin.revPerm

lemma pathRotation_val (n : ℕ) (d : Dart n) :
    (pathRotation n d).val=if d.val=0 then 0 else 2*(n+1)-d.val := by
  simp only [pathRotation,Equiv.Perm.mul_apply,Fin.revPerm_apply,finRotate_apply,
    Fin.val_add,Fin.val_rev,Fin.val_one]
  by_cases h : d.val=0
  · rw [ite_eq_left h,h]
    have he : 2*(n+1)-(0+1)+1=2*(n+1) := by omega
    rw [he,Nat.mod_self]
  · rw [ite_eq_right h,Nat.mod_eq_of_lt (by have := d.isLt; omega)]
    omega

lemma pathRotation_involutive (n : ℕ) : Function.Involutive (pathRotation n) := by
  intro d
  apply Fin.ext
  rw [pathRotation_val,pathRotation_val]
  have := d.isLt
  split_ifs <;> omega

lemma pathRotation_fixed (n : ℕ) (d : Dart n) : pathRotation n d=d ↔ d.val=0 ∨ d.val=n+1 := by
  rw [Fin.ext_iff,pathRotation_val]
  have := d.isLt
  split_ifs <;> omega

lemma pathRotation_fixed_card (n : ℕ) : Nat.card {d : Dart n // pathRotation n d=d}=2 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : Finset.univ.filter (fun d : Dart n => pathRotation n d=d)=
      {(0 : Dart n),⟨n+1,by omega⟩} := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [pathRotation_fixed]
    simp only [Fin.ext_iff,Fin.val_zero]
  rw [he]
  have hd : (0 : Dart n)≠⟨n+1,by omega⟩ := by intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
  simp [hd]

lemma pathRotation_orbits (n : ℕ) : Nat.card (Orbit (pathRotation n))=n+2 := by
  have hh := MapFinite.twice_card_orbits (pathRotation n) (pathRotation_involutive n)
  simp only [← Nat.card_eq_fintype_card,pathRotation_fixed_card] at hh
  have hd : Nat.card (Dart n)=2*(n+1) := by simp [Dart]
  rw [hd] at hh
  change 2*Nat.card (Orbit (pathRotation n))=2*(n+1)+2 at hh
  omega

lemma rotate_sameCycle (n : ℕ) (d e : Dart n) : (finRotate (2*(n+1))).SameCycle d e := by
  apply (isCycle_finRotate_of_le (by omega : 2≤2*(n+1))).sameCycle
  · apply Equiv.Perm.mem_support.mp
    rw [support_finRotate_of_le (by omega : 2≤2*(n+1))]
    exact Finset.mem_univ _
  · apply Equiv.Perm.mem_support.mp
    rw [support_finRotate_of_le (by omega : 2≤2*(n+1))]
    exact Finset.mem_univ _

lemma pathRotation_face (n : ℕ) : pathRotation n*Fin.revPerm=finRotate (2*(n+1)) := by
  ext d
  simp only [pathRotation,Equiv.Perm.mul_apply,Fin.revPerm_apply,Fin.rev_rev]

lemma rotate_orbits (n : ℕ) : Nat.card (Orbit (finRotate (2*(n+1))))=1 := by
  have : Subsingleton (Orbit (finRotate (2*(n+1)))) := ⟨fun v w => by
    induction v using Quotient.inductionOn with | h d =>
      induction w using Quotient.inductionOn with | h e =>
        exact Quotient.sound (rotate_sameCycle n d e)⟩
  have : Nonempty (Orbit (finRotate (2*(n+1)))) := ⟨orbit _ 0⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

/-- A concrete genus-zero path map with every positive edge size. -/
def pathLabelledMap (n : ℕ) : LabelledMap n := ⟨(Fin.revPerm,pathRotation n),by
  refine ⟨Fin.rev_involutive,?_,?_,?_⟩
  · intro d h
    have he := congrArg Fin.val h
    simp only [Fin.revPerm_apply,Fin.val_rev] at he
    have := d.isLt
    omega
  · apply spanningGraph_connected_of_face_cycle
    rw [pathRotation_face]
    exact rotate_sameCycle n
  · change Nat.card (Orbit (pathRotation n))+Nat.card (Orbit (pathRotation n*Fin.revPerm))=n+3
    rw [pathRotation_face,pathRotation_orbits,rotate_orbits]⟩

instance rootedMap_nonempty (n : ℕ) : Nonempty (RootedMap n) := ⟨Quotient.mk _ (pathLabelledMap n)⟩

lemma partition_pos {q : ℝ} (hq : 0<q) (n : ℕ) : 0<partition q n := by
  classical
  unfold partition
  apply Finset.sum_pos
  · intro M _
    apply Finset.sum_pos
    · intro A _
      exact fkWeight_pos hq M A
    · exact Finset.univ_nonempty
  · exact Finset.univ_nonempty

end FKCRT
end



/-! The exact edge-reversal tour of the rotation-system maps. -/
noncomputable section
open Equiv Equiv.Perm Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

private lemma partial_involutive (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    Function.Involutive (fun d => if orbit a d ∈ A then a d else d) := by
  classical
  intro d
  by_cases hd : orbit a d ∈ A
  · simp only [orbit_perm, hd, ite_true]
    exact ha d
  · simp only [hd, ite_false]

def partialReversal (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : Perm (Dart n) := by
  classical
  exact (partial_involutive a ha A).toPerm _

lemma partialReversal_apply (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (d : Dart n) :
    partialReversal a ha A d = if orbit a d ∈ A then a d else d := rfl

lemma partialReversal_involutive (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : Function.Involutive (partialReversal a ha A) :=
  partial_involutive a ha A

lemma partialReversal_empty (a : Perm (Dart n)) (ha : Function.Involutive a) :
    partialReversal a ha ∅ = 1 := by
  apply Equiv.ext
  intro d
  simp [partialReversal_apply]

lemma partialReversal_self (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : partialReversal a ha A * partialReversal a ha A = 1 := by
  apply Equiv.ext
  intro d
  exact partialReversal_involutive a ha A d

lemma partialReversal_compl (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : partialReversal a ha A * a = partialReversal a ha Aᶜ := by
  classical
  apply Equiv.ext
  intro d
  simp only [mul_apply, partialReversal_apply, orbit_perm, Finset.mem_compl]
  by_cases h : orbit a d ∈ A
  · simpa only [h, ite_true, not_true_eq_false, ite_false] using ha d
  · simp only [h, ite_false, not_false_eq_true, ite_true]

lemma partialReversal_insert (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a) (he : e ∉ A) :
    partialReversal a ha (insert e A) =
      partialReversal a ha A * swap e.out (a e.out) := by
  classical
  have heq (d : Dart n) : orbit a d = e ↔ d = e.out ∨ d = a e.out :=
    MapFinite.mk_eq_iff_involution a ha d e
  have ho : orbit a e.out = e := Quotient.out_eq e
  apply Equiv.ext
  intro d
  by_cases hd₁ : d = e.out
  · subst d
    simp only [mul_apply, swap_apply_left, partialReversal_apply, orbit_perm,
      ho, Finset.mem_insert_self, ite_true, he, ite_false]
  by_cases hd₂ : d = a e.out
  · subst d
    simp only [mul_apply, swap_apply_right, partialReversal_apply, orbit_perm,
      ho, Finset.mem_insert_self, ite_true, he, ite_false]
    exact ha e.out
  · have hd : orbit a d ≠ e := fun h => (heq d).mp h |>.elim hd₁ hd₂
    simp only [mul_apply, swap_apply_of_ne_of_ne hd₁ hd₂, partialReversal_apply,
      Finset.mem_insert, hd, false_or]

lemma card_orbit_mul_swap_le (p : Perm (Dart n)) (d e : Dart n) :
    Nat.card (Orbit (p * swap d e)) ≤ Nat.card (Orbit p) + 1 := by
  rw [mul_swap_eq_swap_mul]
  exact MapCycles.card_orbits_swap_le p (p d) (p e)

lemma card_orbit_partialReversal_le (a s : Perm (Dart n))
    (ha : Function.Involutive a) (A : Finset (Orbit a)) :
    Nat.card (Orbit (s * partialReversal a ha A)) ≤ Nat.card (Orbit s) + A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [partialReversal_empty]
  | @insert e A he ih =>
    rw [partialReversal_insert a ha A e he, ← mul_assoc, Finset.card_insert_of_notMem he]
    have hh := card_orbit_mul_swap_le (s * partialReversal a ha A) e.out (a e.out)
    omega

lemma card_orbit_eq_one_iff (p : Perm (Dart n)) :
    Nat.card (Orbit p) = 1 ↔ ∀ d e, p.SameCycle d e := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · intro hh d e
    have : Subsingleton (Orbit p) := hh.1
    exact Quotient.exact (Subsingleton.elim (orbit p d) (orbit p e))
  · intro hh
    refine ⟨⟨fun v w => ?_⟩, ⟨orbit p 0⟩⟩
    induction v using Quotient.inductionOn with | h d =>
      induction w using Quotient.inductionOn with | h e =>
        exact Quotient.sound (hh d e)

lemma spanningGraph_reachable_partial (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (d : Dart n) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable
      (orbit s d) (orbit s (partialReversal a ha A d)) := by
  classical
  rw [partialReversal_apply]
  split_ifs with h
  · by_cases hd : orbit s d = orbit s (a d)
    · rw [hd]
    · exact SimpleGraph.Adj.reachable ⟨hd, Or.inl ⟨d, h, rfl, rfl⟩⟩
  · exact SimpleGraph.Reachable.refl _

lemma spanningGraph_connected_of_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (hc : ∀ d e, (s * partialReversal a ha A).SameCycle d e) :
    (spanningGraph a s (A : Set (Orbit a))).Connected := by
  refine {preconnected := ?_, nonempty := ⟨orbit s 0⟩}
  intro v w
  induction v using Quotient.inductionOn with | h d =>
    induction w using Quotient.inductionOn with | h e =>
      obtain ⟨k,hk⟩ := (hc d e).exists_nat_pow_eq
      rw [← hk]
      have hp (j : ℕ) : (spanningGraph a s (A : Set (Orbit a))).Reachable
          (orbit s d) (orbit s (((s * partialReversal a ha A)^j) d)) := by
        induction j with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ j ih =>
          rw [pow_succ', mul_apply, mul_apply, orbit_perm]
          exact ih.trans (spanningGraph_reachable_partial a s ha A _)
      exact hp k

lemma reversal_card (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d, a d ≠ d) : Fintype.card (Orbit a) = n + 1 := by
  have hn : Fintype.card {d : Dart n // a d = d} = 0 := by
    have : IsEmpty {d : Dart n // a d = d} := ⟨fun d => hf d d.property⟩
    exact Fintype.card_eq_zero
  have hh := MapFinite.twice_card_orbits a ha
  rw [Fintype.card_eq_nat_card] at hn
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  change 2*Nat.card (Orbit a)=Nat.card (Dart n)+Nat.card {d : Dart n // a d=d} at hh
  rw [hn] at hh
  simp only [Dart, Nat.card_fin, add_zero] at hh
  omega

/-- A one-cycle tour in a genuine planar map has exactly V-1 chosen edges.
The proof uses the Euler equality and the two complementary tour
bounds, so loops and parallel edges are fully retained. -/
theorem tour_edge_card (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (hc : ∀ d e, (M.val.2 * partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    Nat.card (Orbit M.val.2) = A.card + 1 := by
  classical
  let a := M.val.1
  let s := M.val.2
  let ha := M.property.1
  let p := s * partialReversal a ha A
  have hp : Nat.card (Orbit p) = 1 := (card_orbit_eq_one_iff _).mpr hc
  have hv := card_orbit_partialReversal_le a p ha A
  have hf := card_orbit_partialReversal_le a p ha Aᶜ
  have hv_eq : p * partialReversal a ha A = s := by
    dsimp [p]
    rw [mul_assoc, partialReversal_self, mul_one]
  have hf_eq : p * partialReversal a ha Aᶜ = s * a := by
    dsimp [p]
    rw [← partialReversal_compl a ha A, ← mul_assoc, mul_assoc s,
      partialReversal_self, mul_one]
  rw [hv_eq, hp] at hv
  rw [hf_eq, hp, Finset.card_compl, reversal_card a ha M.property.2.1] at hf
  have he := M.property.2.2.2
  change Nat.card (Orbit s) + Nat.card (Orbit (s * a)) = n + 3 at he
  have ha_card : A.card ≤ n + 1 := by
    have hh := Finset.card_le_univ A
    change A.card ≤ Fintype.card (Orbit a) at hh
    rwa [reversal_card a ha M.property.2.1] at hh
  change Nat.card (Orbit s)=A.card+1
  omega

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- An edge's unordered endpoints; representatives do not change this pair. -/
def edgeEnds (a s : Perm (Dart n)) (e : Orbit a) : Sym2 (Orbit s) :=
  s(orbit s e.out, orbit s (a e.out))

lemma edgeEnds_orbit (a s : Perm (Dart n)) (ha : Function.Involutive a) (d : Dart n) :
    edgeEnds a s (orbit a d) = s(orbit s d, orbit s (a d)) := by
  have hh := (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl
  rcases hh with hh | hh
  · conv_rhs => rw [hh]
    rfl
  · conv_rhs => rw [hh, ha]
    exact Sym2.eq_swap

lemma spanningGraph_edgeSet_subset (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (spanningGraph a s (A : Set (Orbit a))).edgeSet ⊆ edgeEnds a s '' (A : Set (Orbit a)) := by
  rintro e he
  induction e using Sym2.ind with | _ v w =>
    rcases (SimpleGraph.mem_edgeSet _).mp he with ⟨_,h | h⟩
    · obtain ⟨d,hd,hv,hw⟩ := h
      refine ⟨orbit a d, hd, ?_⟩
      rw [edgeEnds_orbit a s ha d, hv, hw]
    · obtain ⟨d,hd,hw,hv⟩ := h
      refine ⟨orbit a d, hd, ?_⟩
      rw [edgeEnds_orbit a s ha d, hv, hw]
      exact Sym2.eq_swap

lemma spanningGraph_card_edgeSet_le (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    Nat.card (spanningGraph a s (A : Set (Orbit a))).edgeSet ≤ A.card := by
  rw [Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard (spanningGraph_edgeSet_subset a s ha A)).trans
    ((Set.ncard_image_le (f := edgeEnds a s) (s := (A : Set (Orbit a)))).trans
      (Set.ncard_coe_finset A).le)

/-- The selected edges of a one-cycle planar tour form an actual spanning tree
of the all-edge graph. There are no suppressed loop/parallel edges in
its size: the cardinality equality forces every chosen edge to be distinct
and non-loop. -/
theorem tour_spanningTree (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (hc : ∀ d e, (M.val.2 * partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    (spanningGraph M.val.1 M.val.2 (A : Set (Orbit M.val.1))).IsTree ∧
      Nat.card (spanningGraph M.val.1 M.val.2 (A : Set (Orbit M.val.1))).edgeSet = A.card := by
  have hconn := spanningGraph_connected_of_tour M.val.1 M.val.2 M.property.1 A hc
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  have hle' := spanningGraph_card_edgeSet_le M.val.1 M.val.2 M.property.1 A
  have he := tour_edge_card M A hc
  have hh : Nat.card (spanningGraph M.val.1 M.val.2
      (A : Set (Orbit M.val.1))).edgeSet = A.card := by omega
  exact ⟨SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, by omega⟩, hh⟩

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma card_orbit_mul_comm (p q : Perm (Dart n)) :
    Nat.card (Orbit (p*q)) = Nat.card (Orbit (q*p)) := by
  apply Nat.card_congr
  apply Quotient.congr q
  intro d e
  change (p*q).SameCycle d e ↔ (q*p).SameCycle (q d) (q e)
  have he : q * (p*q) * q⁻¹ = q*p := by group
  rw [← he, sameCycle_conj]
  simp

lemma card_orbit_partialReversal_mul_le (a p : Perm (Dart n))
    (ha : Function.Involutive a) (A : Finset (Orbit a)) :
    Nat.card (Orbit (partialReversal a ha A * p)) ≤ Nat.card (Orbit p) + A.card := by
  rw [card_orbit_mul_comm]
  exact card_orbit_partialReversal_le a p ha A

lemma edgeSwap_eq (a : Perm (Dart n)) (ha : Function.Involutive a) (d : Dart n) :
    swap (orbit a d).out (a (orbit a d).out) = swap d (a d) := by
  have hh := (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl
  rcases hh with hh | hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh, ha]
    exact swap_comm _ _

lemma partialReversal_insert_orbit (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (d : Dart n) (hd : orbit a d ∉ A) :
    partialReversal a ha (insert (orbit a d) A) = partialReversal a ha A * swap d (a d) := by
  rw [partialReversal_insert a ha A (orbit a d) hd, edgeSwap_eq a ha d]

/-- Alternating chords first split and then rejoin a tour cycle. -/
lemma crossing_two_swaps (p : Perm (Dart n)) (x y z w : Dart n)
    (L M N R : List (Dart n))
    (he : MapCycles.orbitList p x = x :: (L ++ y :: (M ++ z :: (N ++ w :: R)))) :
    Nat.card (Orbit (swap y w * (swap x z * p))) = Nat.card (Orbit p) := by
  have hn := MapCycles.nodup_orbitList p x
  rw [he] at hn
  have hxz : x ≠ z := fun h => hn.notMem (by simp [h])
  have hcycle : p.SameCycle x z := by
    apply (MapCycles.mem_orbitList p x z).mp
    rw [he]
    simp
  have hcount := MapCycles.card_orbits_swap_of_sameCycle p hxz hcycle
  let U := x :: (L ++ y :: M)
  let V := z :: (N ++ w :: R)
  have hnodup : (U ++ V).Nodup := by simpa [U,V,List.append_assoc] using hn
  have hdisj := (List.nodup_append.mp hnodup).2.2
  have hyU : y ∈ U := by simp [U]
  have hwV : w ∈ V := by simp [V]
  have hp (d : Dart n) (hd : d ∈ U ++ V) : p d = (U ++ V).formPerm d := by
    have he' : MapCycles.orbitList p x = U ++ V := by simpa [U,V,List.append_assoc] using he
    simpa only [he'] using MapCycles.orbitList_action p x d (he' ▸ hd)
  have hq (d : Dart n) (hd : d ∈ U) : (swap x z * p) d = U.formPerm d := by
    change swap x z (p d) = U.formPerm d
    rw [hp d (List.mem_append_left _ hd)]
    have hh := congrArg (fun r : Perm (Dart n) => r d)
      (MapCycles.swap_mul_formPerm_cut x z (L ++ y :: M) (N ++ w :: R) hnodup)
    change swap x z ((U ++ V).formPerm d) = U.formPerm (V.formPerm d) at hh
    have hdV : d ∉ V := fun hv =>
      List.disjoint_left.mp (List.disjoint_iff_ne.mpr hdisj) hd hv
    rw [hh, List.formPerm_apply_of_notMem hdV]
  have hnot : ¬ (swap x z * p).SameCycle y w := by
    intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    have hh := (MapCycles.pow_eq_on_list (swap x z * p) U hq hyU k).2
    rw [hk] at hh
    exact hdisj w hh w hwV rfl
  have hh := MapCycles.card_orbits_swap_of_not_sameCycle (swap x z * p) hnot
  change Nat.card (Orbit (swap x z * p)) = Nat.card (Orbit p) + 1 at hcount
  change Nat.card (Orbit (swap y w * (swap x z * p))) + 1 =
    Nat.card (Orbit (swap x z * p)) at hh
  omega

/-- An orbit-count-maximal matching on a tour has no alternating pair of
selected edges. This is the exact combinatorial planarity criterion needed
for the two parenthesis families, rather than a topological picture. -/
theorem no_crossing_of_maximal_orbits (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a))
    (hmax : Nat.card (Orbit (partialReversal a ha A * p)) = Nat.card (Orbit p) + A.card)
    (x y : Dart n) (hx : orbit a x ∈ A) (hy : orbit a y ∈ A)
    (hxy : orbit a x ≠ orbit a y) (L M N R : List (Dart n)) :
    MapCycles.orbitList p x ≠ x :: (L ++ y :: (M ++ a x :: (N ++ a y :: R))) := by
  classical
  intro he
  let B := (A.erase (orbit a x)).erase (orbit a y)
  have hxB : orbit a x ∉ B := by simp [B]
  have hyB : orbit a y ∉ B := by simp [B]
  have hyxB : orbit a y ∉ insert (orbit a x) B := by simp [hyB, Ne.symm hxy]
  have hA : A = insert (orbit a y) (insert (orbit a x) B) := by
    ext e
    simp only [B,Finset.mem_insert,Finset.mem_erase]
    constructor
    · intro hh
      by_cases he₁ : e=orbit a y
      · exact Or.inl he₁
      by_cases he₂ : e=orbit a x
      · exact Or.inr (Or.inl he₂)
      · exact Or.inr (Or.inr ⟨he₁,he₂,hh⟩)
    · rintro (rfl | rfl | ⟨_,_,hh⟩) <;> assumption
  have hcard : A.card = B.card + 2 := by
    rw [hA,Finset.card_insert_of_notMem hyxB,Finset.card_insert_of_notMem hxB]
  have hP : partialReversal a ha A * p =
      partialReversal a ha B * (swap y (a y) * (swap x (a x) * p)) := by
    have hx_yB : orbit a x ∉ insert (orbit a y) B := by simp [hxB,hxy]
    have hA' : A = insert (orbit a x) (insert (orbit a y) B) := by
      rw [hA,Finset.insert_comm]
    rw [hA',partialReversal_insert_orbit a ha _ x hx_yB,
      partialReversal_insert_orbit a ha _ y hyB]
    group
  have hle := card_orbit_partialReversal_mul_le a
    (swap y (a y) * (swap x (a x) * p)) ha B
  rw [← hP,crossing_two_swaps p x y (a x) (a y) L M N R he,hmax,hcard] at hle
  omega

/-- For every actual planar map and every one-cycle tour, both edge colours
are noncrossing in that tour. -/
theorem planar_tour_no_crossing (M₀ : LabelledMap n) (A : Finset (Orbit M₀.val.1))
    (hc : ∀ d e, (M₀.val.2 * partialReversal M₀.val.1 M₀.property.1 A).SameCycle d e)
    (x y : Dart n) (hx : orbit M₀.val.1 x ∈ A) (hy : orbit M₀.val.1 y ∈ A)
    (hxy : orbit M₀.val.1 x ≠ orbit M₀.val.1 y) (L M N R : List (Dart n)) :
    MapCycles.orbitList (M₀.val.2 * partialReversal M₀.val.1 M₀.property.1 A) x ≠
      x :: (L ++ y :: (M ++ M₀.val.1 x :: (N ++ M₀.val.1 y :: R))) := by
  apply no_crossing_of_maximal_orbits M₀.val.1 _ M₀.property.1 A ?_ x y hx hy hxy
  rw [card_orbit_mul_comm, mul_assoc,partialReversal_self,mul_one]
  have hv := tour_edge_card M₀ A hc
  have hp := (card_orbit_eq_one_iff _).mpr hc
  omega

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma dualRotation_mul (a s : Perm (Dart n)) (ha : Function.Involutive a) :
    s*a*a=s := by
  apply Equiv.ext
  intro d
  exact congrArg s (ha d)

lemma spanningGraph_dual_connected (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (hc : (spanningGraph a s univ).Connected) : (spanningGraph a (s*a) univ).Connected := by
  let t := s*a
  have hreach : ∀ d, (spanningGraph a t univ).Reachable (orbit t 0) (orbit t d) := by
    apply connected_dart_induction ha hc (P := fun d =>
      (spanningGraph a t univ).Reachable (orbit t 0) (orbit t d))
      (SimpleGraph.Reachable.refl _)
    · exact fun d hd => hd.trans (spanningGraph_reachable_reversal a t d)
    · intro d hd
      have he : s d = t (a d) := (congrArg s (ha d)).symm
      rw [he,orbit_perm]
      exact hd.trans (spanningGraph_reachable_reversal a t d)
  refine {preconnected := ?_, nonempty := ⟨orbit t 0⟩}
  intro v w
  induction v using Quotient.inductionOn with | h d =>
    induction w using Quotient.inductionOn with | h e =>
      exact (hreach d).symm.trans (hreach e)

/-- The combinatorial dual in the dart convention. Choosing the
inverse face orientation is unnecessary: this rotation gives the same
planar oriented dual after reversing edge darts. -/
def dualLabelledMap (M : LabelledMap n) : LabelledMap n :=
  ⟨(M.val.1,M.val.2*M.val.1),M.property.1,M.property.2.1,
    spanningGraph_dual_connected M.val.1 M.val.2 M.property.1 M.property.2.2.1,by
      rw [dualRotation_mul _ _ M.property.1]
      exact (Nat.add_comm _ _).trans M.property.2.2.2⟩

lemma dual_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (s*a)*partialReversal a ha Aᶜ=s*partialReversal a ha A := by
  rw [← partialReversal_compl a ha A]
  apply Equiv.ext
  intro d
  simp only [mul_apply,partialReversal_apply,orbit_perm]
  by_cases h : orbit a d ∈ A
  · simp only [h,ite_true]
    rw [ha]
  · simp only [h,ite_false]
    rw [ha]

theorem planar_tour_compl_card (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (hc : ∀ d e, (M.val.2 * partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    Nat.card (Orbit (M.val.2*M.val.1))=Aᶜ.card+1 := by
  apply tour_edge_card (dualLabelledMap M) Aᶜ
  change ∀ d e, (M.val.2*M.val.1*partialReversal M.val.1 M.property.1 Aᶜ).SameCycle d e
  rw [dual_tour M.val.1 M.val.2 M.property.1 A]
  exact hc

/-- The non-tree pairs are noncrossing in precisely the same rooted tour
order, proved via actual dual rotation systems rather than a disk axiom. -/
theorem planar_tour_compl_no_crossing (M₀ : LabelledMap n) (A : Finset (Orbit M₀.val.1))
    (hc : ∀ d e, (M₀.val.2 * partialReversal M₀.val.1 M₀.property.1 A).SameCycle d e)
    (x y : Dart n) (hx : orbit M₀.val.1 x ∉ A) (hy : orbit M₀.val.1 y ∉ A)
    (hxy : orbit M₀.val.1 x ≠ orbit M₀.val.1 y) (L M N R : List (Dart n)) :
    MapCycles.orbitList (M₀.val.2 * partialReversal M₀.val.1 M₀.property.1 A) x ≠
      x :: (L ++ y :: (M ++ M₀.val.1 x :: (N ++ M₀.val.1 y :: R))) := by
  have hh := planar_tour_no_crossing (dualLabelledMap M₀) Aᶜ
    (by
      change ∀ d e, (M₀.val.2*M₀.val.1*partialReversal M₀.val.1 M₀.property.1 Aᶜ).SameCycle d e
      rw [dual_tour M₀.val.1 M₀.val.2 M₀.property.1 A]
      exact hc) x y
    (Finset.mem_compl.mpr hx) (Finset.mem_compl.mpr hy) hxy L M N R
  change MapCycles.orbitList (M₀.val.2*M₀.val.1*partialReversal M₀.val.1 M₀.property.1 Aᶜ) x ≠
    x :: (L ++ y :: (M ++ M₀.val.1 x :: (N ++ M₀.val.1 y :: R))) at hh
  rwa [dual_tour M₀.val.1 M₀.val.2 M₀.property.1 A] at hh

end FKCRT
end



/-! A genuine multigraph spanning tree has one complete edge-reversal tour.
This is the converse direction of the source's finite encoding, proved
without invoking a topological thickening or assuming planarity. -/
noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_mono (a s : Perm (Dart n)) {A B : Set (Orbit a)} (h : A ⊆ B) :
    spanningGraph a s A ≤ spanningGraph a s B := by
  rintro v w ⟨hne, hh | hh⟩
  · obtain ⟨d,hd,hv,hw⟩ := hh
    exact ⟨hne,Or.inl ⟨d,h hd,hv,hw⟩⟩
  · obtain ⟨d,hd,hw,hv⟩ := hh
    exact ⟨hne,Or.inr ⟨d,h hd,hw,hv⟩⟩

lemma spanningGraph_reachable_of_sameCycle (a s : Perm (Dart n))
    (ha : Function.Involutive a) (A : Finset (Orbit a)) {d e : Dart n}
    (h : (s * partialReversal a ha A).SameCycle d e) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s d) (orbit s e) := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  clear hk
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    rw [pow_succ',mul_apply,mul_apply,orbit_perm]
    exact ih.trans (spanningGraph_reachable_partial a s ha A _)

lemma spanningGraph_edgeSet_of_card (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a))
    (hc : Nat.card (spanningGraph a s (A : Set (Orbit a))).edgeSet = A.card) :
    (spanningGraph a s (A : Set (Orbit a))).edgeSet = edgeEnds a s '' (A : Set (Orbit a)) ∧
      Set.InjOn (edgeEnds a s) (A : Set (Orbit a)) := by
  have hh := spanningGraph_edgeSet_subset a s ha A
  have hi := Set.ncard_image_le (f := edgeEnds a s) (s := (A : Set (Orbit a)))
  have hec : (spanningGraph a s (A : Set (Orbit a))).edgeSet.ncard = A.card := by
    simpa only [Nat.card_coe_set_eq] using hc
  have him : (edgeEnds a s '' (A : Set (Orbit a))).ncard = A.card := by
    have := Set.ncard_le_ncard hh
    rw [Set.ncard_coe_finset] at hi
    omega
  refine ⟨Set.eq_of_subset_of_ncard_le hh (by omega),?_⟩
  apply Set.injOn_of_ncard_image_eq _ A.finite_toSet
  simpa only [Set.ncard_coe_finset] using him

lemma spanningGraph_delete_edge_le (a s : Perm (Dart n)) (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (e : Orbit a) (he : e ∉ A)
    (hi : Set.InjOn (edgeEnds a s) ((insert e A : Finset (Orbit a)) : Set (Orbit a))) :
    spanningGraph a s (A : Set (Orbit a)) ≤
      (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).deleteEdges {edgeEnds a s e} := by
  intro v w hvw
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨spanningGraph_mono a s (by intro x hx; exact Finset.mem_insert_of_mem hx) hvw,?_⟩
  intro heq
  have hh := spanningGraph_edgeSet_subset a s ha A ((SimpleGraph.mem_edgeSet _).mpr hvw)
  obtain ⟨f,hf,hfvw⟩ := hh
  have hfe : f = e := hi (Finset.mem_insert_of_mem hf) (Finset.mem_insert_self _ _) (by
    exact hfvw.trans (Set.mem_singleton_iff.mp heq))
  exact he (hfe ▸ hf)

/-- Each chosen forest edge joins two tour cycles, hence the exact cycle count. -/
theorem forest_tour_cycle_card (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a))
    (ht : (spanningGraph a s (A : Set (Orbit a))).IsAcyclic)
    (hn : ∀ e ∈ A, orbit s e.out ≠ orbit s (a e.out))
    (hi : Set.InjOn (edgeEnds a s) (A : Set (Orbit a))) :
    Nat.card (Orbit (s * partialReversal a ha A)) + A.card = Nat.card (Orbit s) := by
  induction A using Finset.induction_on with
  | empty => simp [partialReversal_empty]
  | @insert e A he ih =>
    have hsub : (A : Set (Orbit a)) ⊆ ((insert e A : Finset (Orbit a)) : Set (Orbit a)) := by
      intro f hf; exact Finset.mem_insert_of_mem hf
    have htA := ht.anti (spanningGraph_mono a s hsub)
    have hni : ∀ f ∈ A, orbit s f.out ≠ orbit s (a f.out) := fun f hf => hn f (hsub hf)
    have hii : Set.InjOn (edgeEnds a s) (A : Set (Orbit a)) := hi.mono hsub
    have ih' := ih htA hni hii
    have hedge : (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).Adj
        (orbit s e.out) (orbit s (a e.out)) := by
      refine ⟨hn e (Finset.mem_insert_self _ _), Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
      change orbit a e.out ∈ insert e A
      rw [show orbit a e.out = e from Quotient.out_eq e]
      exact Finset.mem_insert_self e A
    have hbridge := SimpleGraph.isAcyclic_iff_forall_isBridge.mp ht
      ((SimpleGraph.mem_edgeSet _).mpr hedge)
    have hnr : ¬(spanningGraph a s (A : Set (Orbit a))).Reachable
        (orbit s e.out) (orbit s (a e.out)) := by
      intro hh
      apply (SimpleGraph.isBridge_iff.mp hbridge)
      exact hh.mono (spanningGraph_delete_edge_le a s ha e he hi)
    have hnc : ¬(s * partialReversal a ha A).SameCycle e.out (a e.out) :=
      fun h => hnr (spanningGraph_reachable_of_sameCycle a s ha A h)
    have hjoin := MapCycles.card_orbits_swap_of_not_sameCycle
      (s * partialReversal a ha A) (a := (s * partialReversal a ha A) e.out)
      (b := (s * partialReversal a ha A) (a e.out)) (by
        simpa only [sameCycle_apply_left, sameCycle_apply_right] using hnc)
    rw [← mul_swap_eq_swap_mul] at hjoin
    rw [partialReversal_insert a ha A e he, ← mul_assoc,
      Finset.card_insert_of_notMem he]
    change Nat.card (Orbit ((s * partialReversal a ha A) * swap e.out (a e.out))) + (A.card+1) = _
    change Nat.card (Orbit ((s * partialReversal a ha A) * swap e.out (a e.out))) + 1 = Nat.card (Orbit (s * partialReversal a ha A)) at hjoin
    omega

/-- No suppressed parallel edge or loop is allowed in a multigraph tree; the
cardinality condition records precisely this source convention. -/
theorem spanningTree_one_cycle_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a))
    (ht : (spanningGraph a s (A : Set (Orbit a))).IsTree)
    (hc : Nat.card (spanningGraph a s (A : Set (Orbit a))).edgeSet = A.card) :
    ∀ d e, (s * partialReversal a ha A).SameCycle d e := by
  obtain ⟨hedges,hi⟩ := spanningGraph_edgeSet_of_card a s ha A hc
  have hn : ∀ e ∈ A, orbit s e.out ≠ orbit s (a e.out) := by
    intro e he
    have hh : edgeEnds a s e ∈ (spanningGraph a s (A : Set (Orbit a))).edgeSet :=
      hedges.symm ▸ ⟨e,he,rfl⟩
    exact ((SimpleGraph.mem_edgeSet _).mp hh).ne
  have hcount := forest_tour_cycle_card a s ha A ht.isAcyclic hn hi
  have hcard := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  apply (card_orbit_eq_one_iff _).mp
  omega

end FKCRT
end



/-! Exact reconstruction in the rotation-system convention. The
Euler equalities on the two coloured matchings are equivalent to their
noncrossing property; maximum orbit counts are proved for stack matchings
in `WorkNoncrossing`, rather than postulated for a map. -/
noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma reconstructed_tour (a t : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (t * partialReversal a ha A) * partialReversal a ha A = t := by
  rw [mul_assoc,partialReversal_self,mul_one]

lemma reconstructed_face (a t : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (t * partialReversal a ha A) * a = t * partialReversal a ha Aᶜ := by
  rw [mul_assoc,partialReversal_compl]

/-- Reconstructing a two-coloured noncrossing tour gives a genuine connected
planar map, including the empty-tree and all-loop cases. -/
theorem reconstruction_conditions (a t : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d,a d ≠ d) (A : Finset (Orbit a))
    (ht : ∀ d e,t.SameCycle d e)
    (hv : Nat.card (Orbit (t * partialReversal a ha A)) = A.card+1)
    (hF : Nat.card (Orbit (t * partialReversal a ha Aᶜ)) = Aᶜ.card+1) :
    MapConditions (a,t * partialReversal a ha A) := by
  refine ⟨ha,hf,?_,?_⟩
  · have hc := spanningGraph_connected_of_tour a (t * partialReversal a ha A) ha A
      (by simpa only [reconstructed_tour] using ht)
    exact hc.mono (spanningGraph_mono _ _ (Set.subset_univ _))
  · change Nat.card (Orbit (t * partialReversal a ha A)) +
        Nat.card (Orbit ((t * partialReversal a ha A)*a)) = n+3
    rw [reconstructed_face,hv,hF]
    have hc := Finset.card_add_card_compl A
    rw [reversal_card a ha hf] at hc
    omega

/-- The inverse is literal permutation multiplication, so it retains the
cyclic seam and the designated root dart without any quotient choice. -/
lemma reconstruction_inverse (M : LabelledMap n) (A : Finset (Orbit M.val.1)) :
    (M.val.2 * partialReversal M.val.1 M.property.1 A) *
      partialReversal M.val.1 M.property.1 A = M.val.2 :=
  reconstructed_tour M.val.1 M.val.2 M.property.1 A

/-- Both maximum orbit counts follow from a genuine map and any genuine
spanning tree. Together with reconstruction this is an algebraic form of the
classical tree-rooted-map/two-colour matching correspondence. -/
theorem spanningTree_colour_euler (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (ht : (spanningGraph M.val.1 M.val.2 (A : Set (Orbit M.val.1))).IsTree)
    (hc : Nat.card (spanningGraph M.val.1 M.val.2 (A : Set (Orbit M.val.1))).edgeSet = A.card) :
    let t := M.val.2 * partialReversal M.val.1 M.property.1 A
    (∀ d e,t.SameCycle d e) ∧
    Nat.card (Orbit (t * partialReversal M.val.1 M.property.1 A)) = A.card+1 ∧
    Nat.card (Orbit (t * partialReversal M.val.1 M.property.1 Aᶜ)) = Aᶜ.card+1 := by
  have hone := spanningTree_one_cycle_tour M.val.1 M.val.2 M.property.1 A ht hc
  refine ⟨hone,?_,?_⟩
  · rw [reconstructed_tour]
    exact tour_edge_card M A hone
  · have hh := planar_tour_compl_card M A hone
    have he := reconstructed_face M.val.1
      (M.val.2 * partialReversal M.val.1 M.property.1 A) M.property.1 A
    rw [reconstructed_tour] at he
    rw [← he]
    exact hh

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles
variable {n : ℕ}

/-- Edges of the first colour, in the edge-orbit quotient of the complete
matching. -/
def matchingEdges (E F : List (Dart n × Dart n)) : Finset (Orbit (turns (E++F))) :=
  E.toFinset.image (fun e => orbit (turns (E++F)) e.1)

lemma mem_matchingEdges (E F : List (Dart n × Dart n))
    (hn : (endpoints (E++F)).Nodup) (d : Dart n) :
    orbit (turns (E++F)) d ∈ matchingEdges E F ↔ d∈endpoints E := by
  classical
  simp only [matchingEdges,Finset.mem_image,List.mem_toFinset]
  constructor
  · rintro ⟨e,he,hde⟩
    have hh : (turns (E++F)).SameCycle e.1 d := Quotient.exact hde
    rw [MapFinite.sameCycle_involution _ (turns_involutive hn),
      (turns_pair hn e (List.mem_append_left _ he)).1] at hh
    exact mem_endpoints.mpr ⟨e,he,hh⟩
  · intro hd
    obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hd
    · exact ⟨e,he,rfl⟩
    · refine ⟨e,he,?_⟩
      apply Quotient.sound
      apply (MapFinite.sameCycle_involution _ (turns_involutive hn) _ _).mpr
      exact Or.inr (turns_pair hn e (List.mem_append_left _ he)).1.symm

lemma partialReversal_matchingEdges (E F : List (Dart n × Dart n))
    (hn : (endpoints (E++F)).Nodup) :
    partialReversal (turns (E++F)) (turns_involutive hn) (matchingEdges E F)=turns E := by
  apply Equiv.ext
  intro d
  simp only [partialReversal_apply,mem_matchingEdges E F hn]
  split_ifs with hd
  · exact (turns_sublist_apply hn (List.sublist_append_left _ _) hd).symm
  · exact (turns_fixed_of_notMem hd).symm

lemma turns_mul_complete (E F : List (Dart n × Dart n))
    (hn : (endpoints (E++F)).Nodup) : turns E * turns (E++F)=turns F := by
  have hE : turns E*turns E=1 := turns_self ((by rw [endpoints_append] at hn; exact hn.of_append_left))
  have hF : turns F*turns F=1 := turns_self ((by rw [endpoints_append] at hn; exact hn.of_append_right))
  have hEF := turns_self hn
  have he : turns (E++F)=turns E*turns F := by
    have h1 : (turns (E++F))⁻¹=turns (E++F) := inv_eq_of_mul_eq_one_left hEF
    have h2 : (turns E)⁻¹=turns E := inv_eq_of_mul_eq_one_left hE
    have h3 : (turns F)⁻¹=turns F := inv_eq_of_mul_eq_one_left hF
    rw [turns_append,mul_inv_rev,h2,h3] at h1
    simpa only [turns_append] using h1.symm
  rw [he,← mul_assoc,hE,one_mul]

/-- Two complete noncrossing colour matchings construct an actual planar
rotation system in the map model, with no topological assumptions. -/
theorem matching_map_conditions (E F : List (Dart n × Dart n))
    (hE : Arches (List.finRange (2*(n+1))) E)
    (hF : Arches (List.finRange (2*(n+1))) F)
    (hc : (endpoints (E++F)).Perm (List.finRange (2*(n+1)))) :
    MapConditions (turns (E++F),(List.finRange (2*(n+1))).formPerm * turns E) := by
  classical
  let l := List.finRange (2*(n+1))
  let t := l.formPerm
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have ha := turns_involutive hn
  have hf (d : Dart n) : turns (E++F) d≠d := by
    intro hh
    exact (turns_eq_self_iff hn d).mp hh (hc.mem_iff.mpr (List.mem_finRange d))
  have ht : ∀ d e,t.SameCycle d e := by
    intro d e
    exact sameCycle_of_list t (List.nodup_finRange _) (fun _ _ => rfl)
      (List.mem_finRange d) (List.mem_finRange e)
  have htcard : Nat.card (Orbit t)=1 := (card_orbit_eq_one_iff t).mpr ht
  have hturn : (t*turns E)*partialReversal (turns (E++F)) ha (matchingEdges E F)=t := by
    rw [partialReversal_matchingEdges E F hn,mul_assoc,turns_self (by rw [endpoints_append] at hn; exact hn.of_append_left)]
    simp
  have hconn := spanningGraph_connected_of_tour (turns (E++F)) (t*turns E) ha
    (matchingEdges E F) (by simpa only [hturn] using ht)
  refine ⟨ha,hf,hconn.mono (spanningGraph_mono _ _ (Set.subset_univ _)),?_⟩
  have he := hE.card_orbits_turns [] t (by simpa using List.nodup_finRange (2*(n+1)))
    (fun _ _ => rfl)
  have hff := hF.card_orbits_turns [] t (by simpa using List.nodup_finRange (2*(n+1)))
    (fun _ _ => rfl)
  change Nat.card (Orbit (t*turns E)) + Nat.card (Orbit ((t*turns E)*turns (E++F)))=n+3
  rw [mul_assoc,turns_mul_complete E F hn,card_orbit_mul_comm t (turns E),
    card_orbit_mul_comm t (turns F),he,hff,htcard]
  have hlen := hc.length_eq
  have hl (Q : List (Dart n × Dart n)) : (endpoints Q).length=2*Q.length := by
    induction Q with
    | nil => rfl
    | cons e Q ih => simp only [endpoints_cons,List.length_cons,ih]; omega
  rw [hl,List.length_append,List.length_finRange] at hlen
  omega

end FKCRT
end

end OAI
