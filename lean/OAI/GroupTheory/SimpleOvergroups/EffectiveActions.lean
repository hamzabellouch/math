import Mathlib
import OAI.Computability.FiniteCompiler.Effectivity
import OAI.Computability.FiniteCompiler.Quotients
import OAI.Computability.FiniteCompiler.Rewriting
import OAI.Computability.FiniteCompiler.Selectors
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.SimpleOvergroups.EffectiveFold
import OAI.GroupTheory.SimpleOvergroups.NamedActions

namespace OAI



namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap
namespace Operations
variable {G X K L : Type*} (N : Operations G X) [DecidableEq L]

def compare (fx : X → Part L) (x y : X) : Part Bool :=
  (fx x).bind fun a => (fx y).map fun b => decide (a=b)

def step (fx : X → Part L) (a : Letter G X) (f : Form G X) : Part (Form G X) :=
  (N.plan a f).elim Part.some (fun p =>
    (compare fx p.1 p.2.1).map (fun b => bif b then p.2.2 else none))

def run (N : Operations G X) (fx : X → Part L) : List (Letter G X) → Form G X → Part (Form G X)
  | [], f => Part.some f
  | a::w, f => (run N fx w f).bind (N.step fx a)

def key (fg : G → Part K) (fx : X → Part L) : Form G X → Part (Result K L)
  | none => Part.some none
  | some (l,g,r) => (fg g).bind fun k =>
      (Effect.traverse fx l).bind fun ls =>
        (Effect.traverse fx r).map fun rs => some (ls,k,rs)

def test (fg : G → Part K) (fx : X → Part L) (w : List (Letter G X)) :
    Part (Result K L) :=
  (N.run fx w (some ([],N.one,[]))).bind (key fg fx)

theorem compare_full (fx : X → Part L) (kx : X → L) {x y : X}
    (hx : kx x ∈ fx x) (hy : kx y ∈ fx y) :
    decide (kx x = kx y) ∈ compare fx x y :=
  Part.mem_bind_iff.mpr ⟨_,hx,Part.mem_map _ hy⟩

theorem step_full (fx : X → Part L) (kx : X → L) {d : ℕ}
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (a : Letter G X) (f : Form G X) (hb : N.letterCost a + N.formCost f ≤ d) :
    N.totalStep kx a f ∈ N.step fx a f := by
  cases f with
  | none => exact Part.mem_some _
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> exact Part.mem_some _
    · exact Part.mem_some _
    · cases y with
      | none => exact Part.mem_some _
      | some y =>
        cases l with
        | nil => exact Part.mem_some _
        | cons x l =>
          have hy : N.xcost y ≤ d := by simp only [letterCost,formCost] at hb; omega
          have hh : N.xcost x ≤ d := by
            simp only [letterCost,formCost,List.map_cons,List.sum_cons] at hb; omega
          have ht := compare_full fx kx (hx _ hy) (hx _ hh)
          simpa only [step,plan,totalStep,Sum.elim_inr,Bool.cond_decide] using
            Part.mem_map (fun b => bif b then some (l,g,r) else none) ht

theorem run_full (fx : X → Part L) (kx : X → L) {d : ℕ}
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (w : List (Letter G X)) (f : Form G X) (hb : N.wordCost w + N.formCost f ≤ d) :
    N.totalRun kx w f ∈ N.run fx w f := by
  induction w with
  | nil => exact Part.mem_some _
  | cons a w ih =>
    refine Part.mem_bind_iff.mpr ⟨N.totalRun kx w f,ih ?_,N.step_full fx kx hx a _ ?_⟩
    · rw [wordCost_cons] at hb; omega
    · have hc := N.totalRun_cost kx w f
      rw [wordCost_cons] at hb
      omega

omit [DecidableEq L] in
theorem key_full (fg : G → Part K) (fx : X → Part L) (kg : G → K) (kx : X → L)
    {d : ℕ} (hg : ∀ g, N.gcost g ≤ d → kg g ∈ fg g)
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (f : Form G X) (hb : N.formCost f ≤ d) : formKey kg kx f ∈ key fg fx f := by
  cases f with
  | none => exact Part.mem_some _
  | some p =>
    rcases p with ⟨l,g,r⟩
    change (l.map N.xcost).sum + N.gcost g + (r.map N.xcost).sum ≤ d at hb
    have hl : l.map kx ∈ Effect.traverse fx l := by
      apply Search.traverse_map
      intro x hm
      apply hx
      have hh : N.xcost x ≤ (l.map N.xcost).sum := List.single_le_sum (by simp) _
        (List.mem_map.mpr ⟨x,hm,rfl⟩)
      omega
    have hr : r.map kx ∈ Effect.traverse fx r := by
      apply Search.traverse_map
      intro x hm
      apply hx
      have hh : N.xcost x ≤ (r.map N.xcost).sum := List.single_le_sum (by simp) _
        (List.mem_map.mpr ⟨x,hm,rfl⟩)
      omega
    exact Part.mem_bind_iff.mpr ⟨_,hg g (by omega),Part.mem_bind_iff.mpr ⟨_,hl,Part.mem_map _ hr⟩⟩

theorem test_full (fg : G → Part K) (fx : X → Part L) (kg : G → K) (kx : X → L)
    {d : ℕ} (hg : ∀ g, N.gcost g ≤ d → kg g ∈ fg g)
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (w : List (Letter G X)) (hb : N.wordCost w ≤ d) :
    N.totalTest kg kx w ∈ N.test fg fx w := by
  apply Part.mem_bind_iff.mpr
  refine ⟨N.totalNormalize kx w,?_,N.key_full fg fx kg kx hg hx _ ((N.totalNormalize_cost kx w).trans hb)⟩
  apply N.run_full fx kx hx
  simpa only [formCost,List.map_nil,List.sum_nil,N.cost_one,zero_add,add_zero] using hb

variable {P : Type*} [Primcodable P] [Primcodable G] [Primcodable X]
  [Primcodable K] [Primcodable L]
variable {fg : P → G → Part K} {fx : P → X → Part L}

theorem partrec_compare (hx : Partrec₂ fx) :
    Partrec (fun p : P × X × X => compare (fx p.1) p.2.1 p.2.2) := by
  have ha : Partrec (fun p : P × X × X => fx p.1 p.2.1) :=
    hx.comp Computable.fst (Computable.fst.comp Computable.snd)
  apply ha.bind
  have hb : Partrec (fun p : (P × X × X) × L => fx p.1.1 p.1.2.2) :=
    hx.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
  exact (hb.map (Primrec.eq.decide.to_comp.comp
    (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂

theorem partrec_step (hn : Computable₂ N.plan) (hx : Partrec₂ fx) :
    Partrec (fun p : P × Letter G X × Form G X => N.step (fx p.1) p.2.1 p.2.2) := by
  let S := P × Letter G X × Form G X
  have hp : Computable (fun p : S => N.plan p.2.1 p.2.2) :=
    hn.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
  have hb : Partrec₂ (fun (s : S) (p : X × X × Form G X) =>
      (compare (fx s.1) p.1 p.2.1).map (fun b => bif b then p.2.2 else none)) := by
    have hc : Partrec (fun p : S × (X × X × Form G X) =>
        compare (fx p.1.1) p.2.1 p.2.2.1) :=
      (partrec_compare hx).comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp Computable.snd).pair
          (Computable.fst.comp (Computable.snd.comp Computable.snd))))
    exact (hc.map (Computable.cond Computable.snd
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
      (Computable.const none)).to₂).to₂
  exact (Partrec.sumCasesOn_right hp Computable.snd.to₂ hb).of_eq
    (by intro p; unfold step; cases N.plan p.2.1 p.2.2 <;> rfl)

omit [Primcodable P] [Primcodable G] [Primcodable X] [Primcodable L] in
theorem run_eq_fold (p : P) (w : List (Letter G X)) (f : Form G X) :
    N.run (fx p) w f = EffectiveNames.PartialFold.right
      (fun s : P × Letter G X × Form G X => N.step (fx s.1) s.2.1 s.2.2) p w f := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [run,EffectiveNames.PartialFold.right,ih]

theorem partrec_run (hn : Computable₂ N.plan) (hx : Partrec₂ fx) :
    Partrec (fun p : P × List (Letter G X) × Form G X => N.run (fx p.1) p.2.1 p.2.2) :=
  (EffectiveNames.PartialFold.partrec_right _ (N.partrec_step hn hx)).of_eq
    (fun ⟨p,w,f⟩ => (N.run_eq_fold p w f).symm)

omit [DecidableEq L] in
theorem partrec_key (hg : Partrec₂ fg) (hx : Partrec₂ fx) :
    Partrec₂ (fun p : P => key (fg p) (fx p)) := by
  let S := P × Form G X
  have hs : Partrec₂ (fun (s : S) (t : List X × G × List X) =>
      (fg s.1 t.2.1).bind fun k =>
        (Effect.traverse (fx s.1) t.1).bind fun ls =>
          (Effect.traverse (fx s.1) t.2.2).map fun rs => some (ls,k,rs)) := by
    have hf : Partrec (fun p : S × (List X × G × List X) => fg p.1.1 p.2.2.1) :=
      hg.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
    apply hf.bind
    have hl : Partrec (fun p : (S × (List X × G × List X)) × K =>
        Effect.traverse (fx p.1.1.1) p.1.2.1) :=
      (Effect.partrec_traverse_parameter hx).comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (Computable.fst.comp (Computable.snd.comp Computable.fst))
    apply hl.bind
    have hr : Partrec (fun p : ((S × (List X × G × List X)) × K) × List L =>
        Effect.traverse (fx p.1.1.1.1) p.1.1.2.2.2) :=
      (Effect.partrec_traverse_parameter hx).comp
        (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.fst.comp Computable.fst))))
    exact (hr.map (Computable.option_some.comp
      ((Computable.snd.comp Computable.fst).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair Computable.snd))).to₂).to₂
  exact (Partrec.optionCasesOn_right Computable.snd (Computable.const none) hs).of_eq
    (by intro ⟨p,f⟩; cases f <;> rfl)

theorem partrec_test (hn : Computable₂ N.plan) (hg : Partrec₂ fg) (hx : Partrec₂ fx) :
    Partrec₂ (fun p : P => N.test (fg p) (fx p)) := by
  have hr : Partrec (fun p : P × List (Letter G X) =>
      N.run (fx p.1) p.2 (some ([],N.one,[]))) :=
    (N.partrec_run hn hx).comp (Computable.fst.pair
      (Computable.snd.pair (Computable.const (some ([],N.one,[])))))
  exact hr.bind ((partrec_key hg hx).comp
    (Computable.fst.comp Computable.fst) Computable.snd).to₂

end Operations
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction

end OAI
