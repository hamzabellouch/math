import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.Popular
import OAI.Combinatorics.SharpRamsey.Marking.MarkingMessage

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

def toScan (f : ProjectivePair (K:=K) (V:=V)) : ScanFlag (K:=K) (V:=V) :=
  (f.2.rep,f.1)

def pairStep (W : State (K:=K) (V:=V)) (s : Option (ProjectivePair (K:=K) (V:=V))) :
    State (K:=K) (V:=V) := replayStep W (s.map toScan)

def pairReplay : State (K:=K) (V:=V) → List (Option (ProjectivePair (K:=K) (V:=V))) →
    State (K:=K) (V:=V)
  | W,[] => W
  | W,s::ss => pairReplay (pairStep W s) ss

def pairCode (q : ℝ) : State (K:=K) (V:=V) → List (ProjectivePair (K:=K) (V:=V)) →
    List (RankMask (K:=K) (V:=V) × Option (ProjectivePair (K:=K) (V:=V)))
  | _,[] => []
  | W,f::fs =>
    let s := if IsExpensive W q (toScan f) then some f else none
    (maskAt q W (toScan f),s)::pairCode q (pairStep W s) fs

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma pairCode_length (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V))) : (pairCode q W fs).length=fs.length := by
  induction fs generalizing W with
  | nil => rfl
  | cons f fs ih => simp only [pairCode,List.length_cons,ih]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma pairCode_mask_sent (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V))) :
    (pairCode q W fs).Forall (fun z => z.1.2=.expensive ↔ z.2.isSome) := by
  induction fs generalizing W with
  | nil => trivial
  | cons f fs ih =>
    simp only [pairCode,List.forall_cons]
    constructor
    · simp only [maskAt,flagKind_expensive]
      split_ifs <;> simp_all
    · exact ih _

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma pairReplay_eq (W : State (K:=K) (V:=V))
    (ss : List (Option (ProjectivePair (K:=K) (V:=V)))) :
    pairReplay W ss = replay W (ss.map (Option.map toScan)) := by
  induction ss generalizing W with
  | nil => rfl
  | cons s ss ih => exact ih _

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma pairCode_eq (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V))) :
    (pairCode q W fs).map (fun z => (z.1,z.2.map toScan)) =
      markingCode q W (fs.map toScan) := by
  induction fs generalizing W with
  | nil => rfl
  | cons f fs ih =>
    simp only [pairCode,List.map_cons,markingCode]
    by_cases h : IsExpensive W q (toScan f)
    · simp [sentAt,h,pairStep,ih]
    · simp [sentAt,h,pairStep,ih]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma pairCode_count (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V))) :
    ((pairCode q W fs).filter (fun z => z.1.2=.expensive)).length =
      (scan q W (fs.map toScan)).1 := by
  induction fs generalizing W with
  | nil => rfl
  | cons f fs ih =>
    by_cases h : IsExpensive W q (toScan f)
    · simp [pairCode,maskAt,flagKind_expensive,scan,h,pairStep,replayStep,ih]
    · simp [pairCode,maskAt,flagKind_expensive,scan,h,pairStep,replayStep,ih]

lemma pairCode_spec (q : ℝ) (hq : q=(Nat.card K:ℝ)) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V)))
    (hcons : ScanConsistent (fs.map toScan))
    (hinc : ∀ f∈fs, Incidence.Incident f.1 f.2)
    (hW : ∀ f∈fs, W f.1 ≤ LinearMap.ker f.2.rep) (n : ℕ) (hn : n<fs.length) :
    let cs := pairCode q W fs
    let z := cs[n]'(by rw [pairCode_length]; exact hn)
    let Wn := pairReplay W ((cs.map Prod.snd).take n)
    z.2=(if z.1.2=.expensive then some fs[n] else none) ∧
      (z.1.2≠.expensive → fs[n]∈projectiveCheapDomain Wn z.1) := by
  induction fs generalizing W n with
  | nil => simp at hn
  | cons f fs ih =>
    have hp := List.pairwise_cons.mp hcons
    cases n with
    | zero =>
      simp only [pairCode,List.getElem_cons_zero,List.take_zero,pairReplay,maskAt]
      constructor
      · simp only [flagKind_expensive]
      · intro hc
        have he : ¬IsExpensive W q (toScan f) :=
          fun he => hc ((flagKind_expensive q W (toScan f)).mpr he)
        have he' : ¬IsExpensive W (Nat.card K) (f.2.rep,f.1) := by
          simpa only [←hq,toScan] using he
        simpa only [←hq,maskAt,toScan] using
          cheapDomain_membership W f (hinc f (by simp)) (hW f (by simp)) he'
    | succ n =>
      let s := if IsExpensive W q (toScan f) then some f else none
      have HW (g : ProjectivePair (K:=K) (V:=V)) (hg : g∈fs) :
          pairStep W s g.1 ≤ LinearMap.ker g.2.rep := by
        have hw := hW g (by simp [hg])
        by_cases he : IsExpensive W q (toScan f)
        · simp only [s,ite_eq_left he,pairStep,Option.map_some,replayStep]
          apply update_annihilates_later W (toScan f) (toScan g) hw
          exact hp.1 _ (List.mem_map.mpr ⟨g,hg,rfl⟩)
        · simpa only [s,ite_eq_right he,pairStep,Option.map_none,replayStep] using hw
      have hh := ih (pairStep W s) hp.2 (fun g hg => hinc g (by simp [hg])) HW n (by simpa using hn)
      exact hh

def codeTuple {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (i : Fin N) : RankMask (K:=K) (V:=V) × Option (ProjectivePair (K:=K) (V:=V)) :=
  (pairCode q (fun _ => ⊥) (List.ofFn F))[i.val]'(by rw [pairCode_length,List.length_ofFn]; exact i.isLt)

def tupleMask {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    Fin N → RankMask (K:=K) (V:=V) := fun i => (codeTuple q F i).1

def expensiveMask {N : ℕ} (M : Fin N → RankMask (K:=K) (V:=V)) : Finset (Fin N) :=
  univ.filter (fun i => (M i).2=.expensive)

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma mem_expensiveMask {N : ℕ} (M : Fin N → RankMask (K:=K) (V:=V)) (i : Fin N) :
    i∈expensiveMask M ↔ (M i).2=.expensive := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma ofFn_codeTuple {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    List.ofFn (codeTuple q F) = pairCode q (fun _ => ⊥) (List.ofFn F) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,pairCode_length]
  · intro i h1 h2
    simp only [List.getElem_ofFn,codeTuple]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma expensiveMask_card {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    (expensiveMask (tupleMask q F)).card =
    (scan q (fun _ => ⊥) ((List.ofFn F).map toScan)).1 := by
  have hfilter (xs : List (RankMask (K:=K) (V:=V) × Option (ProjectivePair (K:=K) (V:=V)))) :
      (xs.filter (fun a => a.1.2=.expensive)).length =
        (xs.map (fun a => if a.1.2=.expensive then 1 else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => by_cases h : a.1.2=.expensive <;> simp [h,ih,Nat.add_comm]
  rw [←pairCode_count,←ofFn_codeTuple,hfilter, List.map_ofFn,List.sum_ofFn]
  rw [expensiveMask,Finset.card_filter]
  rfl

def cheapTuple {Γ : Type*} {N : ℕ}
    (θ : (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V)))) (i : Fin N) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  projectiveCheapDomain (pairReplay (fun _ => ⊥) ((List.ofFn θ.1).take i.val)) (θ.2.2 i)

lemma tuple_sent_eq {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hcons : ScanConsistent ((List.ofFn F).map toScan))
    (hinc : ∀ i, Incidence.Incident (F i).1 (F i).2) (i : Fin N) :
    (codeTuple (Nat.card K) F i).2 =
      Selection.maskedValues (expensiveMask (tupleMask (Nat.card K) F)) F i := by
  have hh := pairCode_spec (Nat.card K) rfl (fun _ => ⊥) (List.ofFn F) hcons
    (by intro f hf; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf; exact hinc j)
    (fun _ _ => bot_le) i.val (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [Selection.maskedValues,mem_expensiveMask,tupleMask,codeTuple,List.getElem_ofFn] using hh.1

lemma cheapTuple_mem {Γ : Type*} {N : ℕ} (c : Γ)
    (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hcons : ScanConsistent ((List.ofFn F).map toScan))
    (hinc : ∀ i, Incidence.Incident (F i).1 (F i).2) (i : Fin N)
    (hi : i∉expensiveMask (tupleMask (Nat.card K) F)) :
    F i∈cheapTuple (Selection.maskedValues (expensiveMask (tupleMask (Nat.card K) F)) F,
      (c,tupleMask (Nat.card K) F)) i := by
  have hs : List.ofFn (Selection.maskedValues (expensiveMask (tupleMask (Nat.card K) F)) F) =
      (pairCode (Nat.card K) (fun _ => ⊥) (List.ofFn F)).map Prod.snd := by
    rw [←ofFn_codeTuple,List.map_ofFn]
    exact congrArg List.ofFn (funext (fun j => (tuple_sent_eq F hcons hinc j).symm))
  have hh := pairCode_spec (Nat.card K) rfl (fun _ => ⊥) (List.ofFn F) hcons
    (by intro f hf; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf; exact hinc j)
    (fun _ _ => bot_le) i.val (by simpa only [List.length_ofFn] using i.isLt)
  have hc : (codeTuple (Nat.card K) F i).1.2≠.expensive := by
    exact fun hc => hi ((mem_expensiveMask _ _).mpr hc)
  simp only [cheapTuple,hs,tupleMask]
  simpa only [codeTuple,List.getElem_ofFn] using hh.2 hc

variable [Finite K]
lemma cheapTuple_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (θ : (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V)))) (i : Fin N) :
    ((cheapTuple θ i).card:ℝ) ≤ 64*(Nat.card K:ℝ)^(n+2) :=
  projectiveCheapDomain_card hdim _ _

lemma cheapTuple_log_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (θ : (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V)))) (i : Fin N) :
    Real.log (cheapTuple θ i).card ≤ Real.log (64*(Nat.card K:ℝ)^(n+2)) := by
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
  by_cases hz : (cheapTuple θ i).card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    exact Real.log_nonneg (by nlinarith [(one_le_pow₀ hq : (1:ℝ)≤(Nat.card K:ℝ)^(n+2))])
  · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hz)) (cheapTuple_card hdim θ i)

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem actual_entropy_upper {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω → Γ) (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V))
    (D : Γ → Fin N → Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x, p.mass x≠0 → ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x, p.mass x≠0 → ∀ i, Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x, p.mass x≠0 → ∀ i, F x i∈D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card≤Jprev) :
    Selection.entropy (p.map F) ≤ Selection.entropy (p.map C)+
      N*Real.log ((Module.finrank K V+1)*3:ℝ)+
      N*Real.log (64*(Nat.card K:ℝ)^(n+2))+
      (∑ x, p.mass x*((expensiveMask (tupleMask (Nat.card K) (F x))).card:ℝ))*
        (Jprev-Real.log (64*(Nat.card K:ℝ)^(n+2))) := by
  have hh := Selection.marking_entropy_upper p C (fun x => tupleMask (Nat.card K) (F x))
    expensiveMask F D cheapTuple Jprev (Real.log (64*(Nat.card K:ℝ)^(n+2))) hD hprev
    (fun x hx i hi => cheapTuple_mem (C x) (F x) (hcons x hx) (hinc x hx) i hi)
    (fun θ i _ => cheapTuple_log_card hdim θ i)
  convert hh using 1 <;>
    try simp only [Fintype.card_fun,Fintype.card_fin,rankMask_card,Nat.cast_pow,Real.log_pow,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  congr 2 <;> exact Subsingleton.elim _ _

omit [Fintype (Projectivization K (Module.Dual K V))] in

lemma expected_expensive_bound {N : ℕ} (p : Selection.Law Ω)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) :
    (∑ x, p.mass x*((expensiveMask (tupleMask (Nat.card K) (F x))).card:ℝ)) ≤
      32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
        Real.log (Fintype.card (Points (K:=K) (V:=V))+1:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).trans' Nat.zero_lt_one
  calc
    _ ≤ ∑ x, p.mass x*(32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
        Real.log (Fintype.card (Points (K:=K) (V:=V))+1:ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      rw [expensiveMask_card]
      exact mul_le_mul_of_nonneg_left (scan_expensive_bound _ hq _ _) (p.nonneg x)
    _ = _ := by rw [← Finset.sum_mul,p.total,one_mul]

end
end SharpLogRamsey.Marking

end

end OAI
