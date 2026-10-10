import Mathlib
import OAI.Computability.FiniteCompiler.Effectivity
import OAI.Computability.FiniteCompiler.Quotients
import OAI.Computability.FiniteCompiler.SelfReference
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.SimpleOvergroups.ContextualTables

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace CodedSearch
variable {A S Q : Type*} [DecidableEq S] [DecidableEq Q]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : DelimiterCode A S)

def lt (u v : List A) : Bool := decide (List.Shortlex r (C.encode u) (C.encode v))

def compute (E : FiniteSearch C) (z : S) (f : List A → Part (Option Q)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (f w).map (w,·)) (E.words n)).map
    (Uniform.table C.encode (lt (r := r) C) z)

variable (wf : WellFounded r) [Std.Trichotomous r] (q : List A → Option Q)

omit [DecidableEq S] [Std.Trichotomous r] in
theorem pick_class {ps : List (List A × Option Q)} {w v : List A}
    (hps : ∀ p ∈ ps, p.2 = q p.1) (hv : q v = q w) :
    q (Uniform.pick (lt (r := r) C) ps v (q w)) = q w := by
  induction ps generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    simp only [Uniform.pick, List.foldl_cons]
    apply ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
    simp only [Uniform.pickStep]
    split
    next h => exact (hps p List.mem_cons_self).symm.trans h.1
    next h => exact hv

omit [DecidableEq S] in
theorem pick_least_fixed {ps : List (List A × Option Q)} {w : List A}
    (hps : ∀ p ∈ ps, p.2 = q p.1) :
    Uniform.pick (lt (r := r) C) ps (EncodedCanonical.least C wf q w) (q w) =
      EncodedCanonical.least C wf q w := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hh : ¬ (p.2 = q w ∧ lt (r := r) C p.1 (EncodedCanonical.least C wf q w) = true) := by
      rintro ⟨hq, hr⟩
      exact EncodedCanonical.least_global_min C wf q
        ((hps p List.mem_cons_self).symm.trans hq) (of_decide_eq_true hr)
    simp only [Uniform.pick, List.foldl_cons, Uniform.pickStep, ite_eq_right hh]
    exact ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))

omit [DecidableEq S] in
theorem pick_eq_least {ps : List (List A × Option Q)} {w : List A}
    (hps : ∀ p ∈ ps, p.2 = q p.1)
    (hm : (EncodedCanonical.least C wf q w, q w) ∈ ps) :
    Uniform.pick (lt (r := r) C) ps w (q w) = EncodedCanonical.least C wf q w := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hm
  have hb : ∀ p ∈ before, p.2 = q p.1 := fun p hp => hps p (List.mem_append_left _ hp)
  have ha : ∀ p ∈ after, p.2 = q p.1 := fun p hp =>
    hps p (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have hclass := pick_class (r := r) C q hb (w := w) rfl
  have hsel : Uniform.pickStep (lt (r := r) C) (q w)
      (Uniform.pick (lt (r := r) C) before w (q w))
      (EncodedCanonical.least C wf q w, q w) = EncodedCanonical.least C wf q w := by
    unfold Uniform.pickStep
    simp only [true_and, lt, decide_eq_true_eq]
    split
    · rfl
    next h =>
      apply C.encode_injective
      exact Std.Trichotomous.trichotomous _ _
        (EncodedCanonical.least_global_min C wf q hclass) h
  simp only [Uniform.pick, List.foldl_append, List.foldl_cons]
  change after.foldl (Uniform.pickStep (lt (r := r) C) (q w))
    (Uniform.pickStep (lt (r := r) C) (q w)
      (Uniform.pick (lt (r := r) C) before w (q w))
      (EncodedCanonical.least C wf q w, q w)) = _
  rw [hsel]
  exact pick_least_fixed C wf q ha

variable (E : FiniteSearch C) (z : S)

omit [DecidableEq S] in
theorem output_full {n : ℕ} {w : List A} (hw : (C.encode w).length ≤ n) :
    Uniform.output C.encode (lt (r := r) C) z
      ((E.words n).map fun v => (v,q v)) (w,q w) = CodeTable.output C wf q z w := by
  have hps : ∀ p ∈ (E.words n).map (fun v => (v,q v)), p.2 = q p.1 := by
    intro p hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
    rfl
  have hm : (EncodedCanonical.least C wf q w, q w) ∈ (E.words n).map (fun v => (v,q v)) :=
    List.mem_map.mpr ⟨EncodedCanonical.least C wf q w, (E.mem_words _ _).mpr
      ((EncodedCanonical.least_length C wf q w).trans hw), by simp [EncodedCanonical.least_class]⟩
  simp only [Uniform.output, CodeTable.output, pick_eq_least C wf q hps hm]

theorem table_full (n : ℕ) :
    Uniform.table C.encode (lt (r := r) C) z ((E.words n).map fun v => (v,q v)) =
      CodeTable.table C E wf q z n := by
  classical
  unfold Uniform.table CodeTable.table
  rw [List.flatMap_map]
  have hh : ∀ w ∈ E.words n,
      (if w ≠ [] ∧ Uniform.output C.encode (lt (r := r) C) z
        ((E.words n).map fun v => (v,q v)) (w,q w) ≠ C.encode w
        then [(C.encode w, Uniform.output C.encode (lt (r := r) C) z
          ((E.words n).map fun v => (v,q v)) (w,q w))] else []) =
      (if w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w
        then [(C.encode w, CodeTable.output C wf q z w)] else []) := by
    intro w hw
    rw [output_full C wf q E z ((E.mem_words _ _).mp hw)]
  rw [List.flatMap_congr hh]
  have he (l : List (List A)) :
      l.flatMap (fun w => if w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w
        then [(C.encode w, CodeTable.output C wf q z w)] else []) =
      (l.filter fun w => w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w).map
        (fun w => (C.encode w, CodeTable.output C wf q z w)) := by
    induction l with
    | nil => rfl
    | cons w l ih =>
      by_cases h : w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w
      · simp only [List.flatMap_cons, List.filter_cons, decide_eq_true_eq, ite_eq_left h,
          List.map_cons, List.singleton_append, ih]
      · simp only [List.flatMap_cons, List.filter_cons, decide_eq_true_eq, ite_eq_right h,
          List.nil_append, ih]
  refine (he _).trans ?_
  congr 1
  apply List.filter_congr
  intro w hw
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

theorem compute_full {f : List A → Part (Option Q)} {n : ℕ}
    (h : ∀ w, (C.encode w).length ≤ n → q w ∈ f w) :
    CodeTable.table C E wf q z n ∈ compute (r := r) C E z f n := by
  apply (Part.mem_map_iff _).mpr
  refine ⟨(E.words n).map (fun w => (w,q w)), ?_, table_full C wf q E z n⟩
  apply Search.traverse_map
  intro w hw
  exact (Part.mem_map_iff _).mpr ⟨_, h w ((E.mem_words _ _).mp hw), rfl⟩

omit [Std.Trichotomous r] in
theorem compute_domain {f : List A → Part (Option Q)} {n : ℕ}
    (hc : (compute (r := r) C E z f n).Dom) :
    ∀ w, (C.encode w).length ≤ n → (f w).Dom := by
  obtain ⟨rs, hrs⟩ := Part.dom_iff_mem.mp hc
  obtain ⟨ps, hps, _⟩ := (Part.mem_map_iff _).mp hrs
  have ht := Effect.traverse_domain hps.1
  intro w hw
  obtain ⟨p, hp⟩ := Part.dom_iff_mem.mp (ht w ((E.mem_words _ _).mpr hw))
  obtain ⟨v, hv, _⟩ := (Part.mem_map_iff _).mp hp
  exact hv.1

theorem compute_eq {f : List A → Part (Option Q)} {n : ℕ}
    {rs : List (List S × List S)} (hc : rs ∈ compute (r := r) C E z f n) :
    rs = CodeTable.table C E wf (Search.value f) z n :=
  Part.mem_unique hc (compute_full C wf (Search.value f) E z
    (fun w hw => Search.value_mem (compute_domain C E z hc.1 w hw)))

end CodedSearch

namespace CodedProgram
variable {P A S Q : Type*}
  [Primcodable P] [Primcodable A] [Primcodable S] [Primcodable Q]
  [DecidableEq S] [DecidableEq Q]

def compute (words : P → ℕ → List (List A)) (code : P → List A → List S)
    (lt : P → List A → List A → Bool) (z : S)
    (f : P → List A → Part (Option Q)) (p : P) (n : ℕ) :
    Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (f p w).map (w,·)) (words p n)).map
    (Uniform.table (code p) (lt p) z)

 theorem partrec_compute (words : P → ℕ → List (List A))
    (code : P → List A → List S) (lt : P → List A → List A → Bool) (z : S)
    (hw : Primrec₂ words) (hc : Primrec₂ code)
    (hl : Primrec (fun x : P × List A × List A => lt x.1 x.2.1 x.2.2))
    {f : P → List A → Part (Option Q)} (hf : Partrec₂ f) :
    Partrec₂ (compute words code lt z f) := by
  have hp : Partrec₂ (fun p w => (f p w).map (w,·)) :=
    (hf.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂
  exact (((Effect.partrec_traverse_parameter hp).comp Computable.fst hw.to_comp).map
    ((Uniform.primrec_table code lt z hc hl).to_comp.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂).to₂

 theorem partrec_search {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
    (C : DelimiterCode A S) (E : FiniteSearch C) (z : S)
    (hw : Primrec E.words) (hc : Primrec C.encode)
    (hl : PrimrecRel (List.Shortlex r))
    {f : P → List A → Part (Option Q)} (hf : Partrec₂ f) :
    Partrec₂ (fun p => CodedSearch.compute (r := r) C E z (f p)) := by
  apply partrec_compute (fun _ => E.words) (fun _ => C.encode)
    (fun _ => CodedSearch.lt (r := r) C) z (hw.comp Primrec.snd).to₂
      (hc.comp Primrec.snd).to₂ _ hf
  exact hl.decide.comp
    (hc.comp (Primrec.fst.comp Primrec.snd))
    (hc.comp (Primrec.snd.comp Primrec.snd))

end CodedProgram
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
