import OAI.Combinatorics.ParityLifts.UniformHeaders

namespace OAI

namespace ParityWL.Complexity

lemma Emits.mono {M : Machine} {bs : List Bool} {s t : ℕ} {b : Bool}
    (h : Emits M bs s b) (hst : s ≤ t) : Emits M bs t b := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t ht ih =>
    change M.output ((step M)^[t+1] (initialConfiguration M bs)).state=some b
    rw [Function.iterate_succ_apply']
    change M.output (step M (run M bs t)).state=some b
    unfold Emits at ih
    simp only [step,ih]

lemma Emits.unique {M : Machine} {bs : List Bool} {s t : ℕ} {b c : Bool}
    (h : Emits M bs s b) (hg : Emits M bs t c) : b=c := by
  rcases le_total s t with hst | hts
  · have hh := h.mono hst
    unfold Emits at hh hg
    simp_all
  · have hh := hg.mono hts
    unfold Emits at h hh
    simp_all

lemma boundedAnswer_of_emits {M : Machine} {bs : List Bool} {s n : ℕ} {b : Bool}
    (h : Emits M bs s b) (hs : s ≤ n) : boundedAnswer M n bs=(true,b) := by
  have hh := smallRun_output (h.mono hs)
  simp only [boundedAnswer,boundedConfiguration,hh,Option.isSome_some,decide_true,Option.getD_some]

lemma boundedAnswer_emits {M : Machine} {bs : List Bool} {n : ℕ}
    (h : (boundedAnswer M n bs).1=true) : Emits M bs n (boundedAnswer M n bs).2 := by
  have hr := (smallRun_represents M bs n).1
  unfold boundedAnswer boundedConfiguration at *
  unfold Emits
  rw [hr]
  generalize M.output ((smallStep M)^[n] (smallInitial M bs)).1=o at *
  cases o <;> simp_all

def PolyProgram.trueTicks : PolyProgram ℕ (List Bool) (fun n => List.replicate n true) :=
  (PolyProgram.ticks.comp (PolyProgram.const true |>.map)).congr (by intro n; simp)

def PolyProgram.trialInput : PolyProgram ((ℕ × ℕ) × List Bool) (List Bool)
    (fun x => Complexity.trialInput x.1.1 x.1.2 x.2) := by
  let p := PolyProgram.fst (ℕ × ℕ) (List Bool)
  let j := (p.comp (PolyProgram.fst ℕ ℕ)).comp PolyProgram.trueTicks
  let k := (p.comp (PolyProgram.snd ℕ ℕ)).comp PolyProgram.trueTicks
  let bs := PolyProgram.snd (ℕ × ℕ) (List Bool)
  let tail := (k.pair (((PolyProgram.const false).pair bs).comp (PolyProgram.cons Bool))).comp (PolyProgram.append Bool)
  exact (j.pair (((PolyProgram.const false).pair tail).comp (PolyProgram.cons Bool))).comp (PolyProgram.append Bool)

def racePairs (n : ℕ) : List (ℕ × ℕ) := (List.range (n+1)).product (List.range (n+1))

def raceProbe (M : Machine) (p : ℕ × ℕ) (x : ℕ × List Bool) : Bool × Bool :=
  boundedAnswer M x.1 (trialInput (p.1+1) (p.2+4) x.2)

def raceStage (M : Machine) (n : ℕ) (bs : List Bool) : Bool × Bool :=
  (((racePairs n).map (fun p => raceProbe M p (n,bs))).filter Prod.fst).headD (false,false)

noncomputable def PolyProgram.raceProbe (M : Machine) :
    PolyProgram ((ℕ × ℕ) × (ℕ × List Bool)) (Bool × Bool) (fun x => Complexity.raceProbe M x.1 x.2) := by
  let ps := PolyProgram.fst (ℕ × ℕ) (ℕ × List Bool)
  let x := PolyProgram.snd (ℕ × ℕ) (ℕ × List Bool)
  let j := (ps.comp (PolyProgram.fst ℕ ℕ)).comp PolyProgram.natSucc
  let k := (((ps.comp (PolyProgram.snd ℕ ℕ)).pair (PolyProgram.const 4)).comp PolyProgram.natAdd)
  let bs := x.comp (PolyProgram.snd ℕ (List Bool))
  let inp := (((j.pair k).pair bs).comp PolyProgram.trialInput)
  exact ((x.comp (PolyProgram.fst ℕ (List Bool))).pair inp).comp (PolyProgram.boundedAnswer M)

def PolyProgram.racePairs : PolyProgram ℕ (List (ℕ × ℕ)) racePairs :=
  ((PolyProgram.natSucc.comp PolyProgram.range).pair (PolyProgram.natSucc.comp PolyProgram.range)).comp (PolyProgram.product ℕ ℕ)

noncomputable def PolyProgram.raceStage (M : Machine) :
    PolyProgram (ℕ × List Bool) (Bool × Bool) (fun x => Complexity.raceStage M x.1 x.2) :=
  (((((PolyProgram.fst ℕ (List Bool)).comp PolyProgram.racePairs).pair (PolyProgram.id (ℕ × List Bool))).comp
    (PolyProgram.raceProbe M).mapWith).comp ((PolyProgram.fst Bool Bool).filter)).comp (PolyProgram.head (Bool × Bool) (false,false))

lemma filter_first_sound (xs : List (Bool × Bool)) (P : Bool → Prop)
    (h : ∀ x∈xs, x.1=true → P x.2)
    (ht : ((xs.filter Prod.fst).headD (false,false)).1=true) :
    P ((xs.filter Prod.fst).headD (false,false)).2 := by
  cases he : xs.filter Prod.fst with
  | nil => simp [he] at ht
  | cons a ys =>
    have ha : a∈xs.filter Prod.fst := by rw [he]; simp
    rw [he] at ht
    exact h a (List.mem_filter.mp ha).1 ht

lemma filter_first_complete (xs : List (Bool × Bool))
    (h : ∃ x∈xs, x.1=true) : ((xs.filter Prod.fst).headD (false,false)).1=true := by
  obtain ⟨x,hx,ht⟩ := h
  have hm : x∈xs.filter Prod.fst := List.mem_filter.mpr ⟨hx,ht⟩
  cases he : xs.filter Prod.fst with
  | nil => simp [he] at hm
  | cons a ys =>
    have ha : a∈xs.filter Prod.fst := by rw [he]; simp
    simpa [he] using (List.mem_filter.mp ha).2

lemma raceStage_sound (M : Machine) (bs : List Bool) (P : Bool → Prop)
    (hM : ∀ j : ℕ, 0<j → ∀ k : ℕ, 4 ≤ k → ∃ s b, Emits M (trialInput j k bs) s b ∧ P b)
    (n : ℕ) (h : (raceStage M n bs).1=true) : P (raceStage M n bs).2 := by
  apply filter_first_sound _ P ?_ h
  intro x hx ht
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨s,b,hb,hP⟩ := hM (p.1+1) (by omega) (p.2+4) (by omega)
  have hh := boundedAnswer_emits ht
  have he := hh.unique hb
  change (raceProbe M p (n,bs)).2=b at he
  rwa [he]

lemma raceStage_complete (M : Machine) (bs : List Bool) (j k s n : ℕ) (b : Bool)
    (hj : 0<j) (hk : 4 ≤ k) (hj' : j ≤ n+1) (hk' : k ≤ n+4) (hs : s ≤ n)
    (h : Emits M (trialInput j k bs) s b) : (raceStage M n bs).1=true := by
  apply filter_first_complete
  have hp : (j-1,k-4)∈racePairs n := by
    change (j-1,k-4)∈(List.range (n+1)).product (List.range (n+1))
    exact List.mem_product.mpr ⟨List.mem_range.mpr (by omega), List.mem_range.mpr (by omega)⟩
  refine ⟨raceProbe M (j-1,k-4) (n,bs),List.mem_map.mpr ⟨_,hp,rfl⟩,?_⟩
  dsimp only [raceProbe]
  rw [show j-1+1=j by omega,show k-4+4=k by omega,boundedAnswer_of_emits h hs]

end ParityWL.Complexity

end OAI
