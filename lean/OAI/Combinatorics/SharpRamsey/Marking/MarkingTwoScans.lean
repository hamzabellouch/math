import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingActual
import OAI.Combinatorics.SharpRamsey.Marking.MarkingDeficit

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def pairDuality : ProjectivePair (K:=K) (V:=V) ≃
    ProjectivePair (K:=K) (V:=Module.Dual K V) where
  toFun f := (f.2,bidual f.1)
  invFun f := (bidual.symm f.2,f.1)
  left_inv f := by simp
  right_inv f := by simp

def reversedPairs {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    Fin N → ProjectivePair (K:=K) (V:=Module.Dual K V) := fun i => pairDuality (F i.rev)

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma reversedPairs_consistent {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hF : ScanConsistent ((List.ofFn F).map toScan)) :
    ScanConsistent ((List.ofFn (reversedPairs F)).map toScan) := by
  rw [List.map_ofFn] at hF ⊢
  have hh := List.pairwise_ofFn.mp hF
  apply List.pairwise_ofFn.mpr
  intro i j hij
  change Incidence.Incident (F j.rev).2 (bidual (F i.rev).1) →
    Incidence.Incident (F i.rev).2 (bidual (F j.rev).1)
  simp only [incident_bidual]
  exact hh (Fin.rev_lt_rev.mpr hij)

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma reversedPairs_incident {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hF : ∀ i, Incidence.Incident (F i).1 (F i).2) (i : Fin N) :
    Incidence.Incident (reversedPairs F i).1 (reversedPairs F i).2 :=
  (incident_bidual _ _).mpr (hF i.rev)

abbrev TwoMask (N : ℕ) := (Fin N → RankMask (K:=K) (V:=V)) ×
  (Fin N → RankMask (K:=K) (V:=Module.Dual K V))

def twoMask {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) : TwoMask (K:=K) (V:=V) N :=
  (tupleMask q F,tupleMask q (reversedPairs F))

def bothExpensive {N : ℕ} (m : TwoMask (K:=K) (V:=V) N) : Finset (Fin N) :=
  expensiveMask m.1 ∪ (expensiveMask m.2).image Fin.rev

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma bothExpensive_mem {N : ℕ} (m : TwoMask (K:=K) (V:=V) N) (i : Fin N) :
    i∈bothExpensive m ↔ i∈expensiveMask m.1 ∨ i.rev∈expensiveMask m.2 := by
  simp only [bothExpensive,mem_union,mem_image]
  constructor
  · rintro (h|⟨j,hj,hji⟩)
    · exact Or.inl h
    · right
      simpa only [←hji,Fin.rev_rev] using hj
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨i.rev,h,Fin.rev_rev i⟩

abbrev TwoMessage (Γ : Type*) (N : ℕ) :=
  (Fin N → Option (ProjectivePair (K:=K) (V:=V))) × (Γ × TwoMask (K:=K) (V:=V) N)

def firstMessage {Γ : Type*} {N : ℕ} (z : TwoMessage (K:=K) (V:=V) Γ N) :
    (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V))) :=
  (fun i => if i∈expensiveMask z.2.2.1 then z.1 i else none,(z.2.1,z.2.2.1))

def secondMessage {Γ : Type*} {N : ℕ} (z : TwoMessage (K:=K) (V:=V) Γ N) :
    (Fin N → Option (ProjectivePair (K:=K) (V:=Module.Dual K V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=Module.Dual K V))) :=
  (fun i => if i∈expensiveMask z.2.2.2 then (z.1 i.rev).map pairDuality else none,(z.2.1,z.2.2.2))

def cheapBoth {Γ : Type*} {N : ℕ} (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  cheapTuple (firstMessage z) i ∩ (cheapTuple (secondMessage z) i.rev).map pairDuality.symm.toEmbedding

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstMessage_actual {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (x : Ω) (q : ℝ) :
    firstMessage (Selection.markingMessage C (fun x => twoMask q (F x)) bothExpensive F x) =
      (Selection.maskedValues (expensiveMask (tupleMask q (F x))) (F x),
        (C x,tupleMask q (F x))) := by
  apply Prod.ext
  · funext i
    change (if i∈expensiveMask (tupleMask q (F x)) then
      Selection.maskedValues (bothExpensive (twoMask q (F x))) (F x) i else none)=_
    by_cases hi : i∈expensiveMask (tupleMask q (F x))
    · have hb : i∈bothExpensive (twoMask q (F x)) := (bothExpensive_mem _ _).mpr (Or.inl hi)
      simp only [hi,ite_true,Selection.maskedValues,hb]
    · simp only [hi,ite_false,Selection.maskedValues]
  · rfl

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondMessage_actual {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (x : Ω) (q : ℝ) :
    secondMessage (Selection.markingMessage C (fun x => twoMask q (F x)) bothExpensive F x) =
      (Selection.maskedValues (expensiveMask (tupleMask q (reversedPairs (F x))))
        (reversedPairs (F x)),(C x,tupleMask q (reversedPairs (F x)))) := by
  apply Prod.ext
  · funext i
    change (if i∈expensiveMask (tupleMask q (reversedPairs (F x))) then
      (Selection.maskedValues (bothExpensive (twoMask q (F x))) (F x) i.rev).map pairDuality
      else none)=_
    by_cases hi : i∈expensiveMask (tupleMask q (reversedPairs (F x)))
    · have hb : i.rev∈bothExpensive (twoMask q (F x)) := by
        apply (bothExpensive_mem _ _).mpr
        right
        simpa only [Fin.rev_rev,twoMask] using hi
      simp only [hi,ite_true,Selection.maskedValues,hb,Option.map_some,reversedPairs]
    · simp only [hi,ite_false,Selection.maskedValues]
  · rfl

lemma cheapBoth_mem {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (x : Ω)
    (hcons : ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ i, Incidence.Incident (F x i).1 (F x i).2) (i : Fin N)
    (hi : i∉bothExpensive (twoMask (Nat.card K) (F x))) :
    F x i∈cheapBoth (Selection.markingMessage C (fun x => twoMask (Nat.card K) (F x))
      bothExpensive F x) i := by
  have hn := not_or.mp ((bothExpensive_mem _ _).not.mp hi)
  apply mem_inter.mpr
  constructor
  · change F x i∈cheapTuple (firstMessage _) i
    rw [firstMessage_actual]
    exact cheapTuple_mem (C x) (F x) hcons hinc i hn.1
  · change F x i∈(cheapTuple (secondMessage _) i.rev).map pairDuality.symm.toEmbedding
    rw [secondMessage_actual]
    apply mem_map.mpr
    refine ⟨reversedPairs (F x) i.rev,?_,?_⟩
    · exact cheapTuple_mem (C x) (reversedPairs (F x)) (reversedPairs_consistent _ hcons)
        (reversedPairs_incident _ hinc) i.rev hn.2
    · simp only [Equiv.coe_toEmbedding,reversedPairs,Fin.rev_rev,Equiv.symm_apply_apply]

variable [Finite K]
lemma cheapBoth_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    ((cheapBoth z i).card:ℝ) ≤ 64*(Nat.card K:ℝ)^(n+2) := by
  have h : ((cheapBoth z i).card:ℝ) ≤ (cheapTuple (firstMessage z) i).card := by
    exact_mod_cast (card_le_card (inter_subset_left : cheapBoth z i⊆_))
  exact h.trans (cheapTuple_card hdim (firstMessage z) i)

lemma cheapBoth_log_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    Real.log (cheapBoth z i).card≤Real.log (64*(Nat.card K:ℝ)^(n+2)) := by
  by_cases hz : (cheapBoth z i).card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
    exact Real.log_nonneg (by nlinarith [(one_le_pow₀ hq : (1:ℝ)≤(Nat.card K:ℝ)^(n+2))])
  · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hz)) (cheapBoth_card hdim z i)

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K] in

lemma bothExpensive_card {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    (bothExpensive (twoMask q F)).card ≤
      (expensiveMask (tupleMask q F)).card+
      (expensiveMask (tupleMask q (reversedPairs F))).card := by
  exact card_union_le _ _ |>.trans (Nat.add_le_add_left (card_image_le) _)

end
end SharpLogRamsey.Marking

end

end OAI
