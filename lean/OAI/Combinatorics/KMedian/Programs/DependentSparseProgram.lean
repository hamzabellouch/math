import Mathlib
import OAI.Combinatorics.KMedian.Process.RoundingStateCompiler

namespace OAI


                                              
section
namespace MetricKMedian.SparseIntegerLaw.DependentProgram
open Binary Binary.PolyProgram Function BinarySparse
variable {C A : Type} (T : C → Type)

structure Bundle where
  ctx : C
  law : SparseIntegerLaw (T ctx)

variable {T} (ec : C → List Bool) (ea : A → List Bool) (view : ∀ c, T c → A)

def Bundle.raw (x : Bundle T) : C × Data A :=
  (x.ctx,((x.law.law.denominator,List.ofFn x.law.law.numerator),x.law.states.toList.map (view x.ctx)))
def Bundle.encode (x : Bundle T) : List Bool := encodePair ec (ed ea) (x.raw view)

def Bundle.branch (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c) (x : Bundle T) : Bundle T :=
  ⟨x.ctx,x.law.branch (p x.ctx) (hp x.ctx) (next x.ctx)⟩
def Bundle.compress (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ) (x : Bundle T) : Bundle T :=
  ⟨x.ctx,x.law.compressAuto (v x.ctx)⟩
def Bundle.compressionInput (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ) (x : Bundle T) :
    IntegerLaw.BinaryCompression.RationalInput :=
  ⟨x.law.length,d x.ctx,x.law.law,fun i => v x.ctx x.law.states[i.val]⟩

 theorem trim_view (c : C) (μ : SparseIntegerLaw (T c)) :
    trimData ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map (view c))=
      (((μ.trim).law.denominator,List.ofFn (μ.trim).law.numerator),μ.trim.states.toList.map (view c)) := by
  change trimData ((raw μ).1,(raw μ).2.map (view c))=_
  rw [RoundingProgram.trimData_map,trimData_raw]
  rfl

noncomputable def contextProgram : PolyProgram (Bundle.encode ec ea view) ec (fun x : Bundle T => x.ctx) :=
  (fst ec (ed ea)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def statesProgram : PolyProgram (Bundle.encode ec ea view) (encodeList ea)
    (fun x : Bundle T => x.law.states.toList.map (view x.ctx)) :=
  ((snd ec (ed ea)).comp (snd el (encodeList ea))).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def lawProgram : PolyProgram (Bundle.encode ec ea view) el
    (fun x : Bundle T => (x.law.law.denominator,List.ofFn x.law.law.numerator)) :=
  ((snd ec (ed ea)).comp (fst el (encodeList ea))).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)

noncomputable def compressionInputProgram (a0 : A) (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ)
    (F : C × A → List ℚ) (hF : ∀ c a, F (c,view c a)=List.ofFn (v c a))
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr F) :
    PolyProgram (Bundle.encode ec ea view) IntegerLaw.BinaryCompression.RationalInput.encode
      (Bundle.compressionInput d v) := by
  let ctx := contextProgram ec ea view
  let rows := (ctx.fanout (statesProgram ec ea view)).comp (V.listMapWith a0 [])
  let work := (ctx.comp D).fanout ((lawProgram ec ea view).fanout rows)
  exact work.recode id (fun _ => rfl) (fun x => by
    change IntegerLaw.BinaryCompression.eqd (List.replicate (d x.ctx) (),
      ((x.law.law.denominator,List.ofFn x.law.law.numerator),
        (x.law.states.toList.map (view x.ctx)).map (fun a => F (x.ctx,a))))=_
    simp only [states_list,List.map_ofFn,Function.comp_def,hF]
    rfl)

noncomputable def compressProgram (a0 : A) (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ)
    (F : C × A → List ℚ) (hF : ∀ c a, F (c,view c a)=List.ofFn (v c a))
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr F) :
    PolyProgram (Bundle.encode ec ea view) (Bundle.encode ec ea view) (Bundle.compress d v) := by
  let law := (compressionInputProgram ec ea view a0 d v F hF D V).comp IntegerLaw.BinaryCompression.rationalCompressProgram
  let trimmed := (law.fanout (statesProgram ec ea view)).comp (trimDataProgram ea a0)
  let work := (contextProgram ec ea view).fanout trimmed
  exact work.recode id (fun _ => rfl) (fun x => by
    change encodePair ec (ed ea) (x.ctx,
      trimData (((x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])).denominator,
       List.ofFn (x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])).numerator),
         x.law.states.toList.map (view x.ctx)))=_
    rw [show trimData _= _ from trim_view view x.ctx
      (⟨x.law.length,x.law.states,x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])⟩ : SparseIntegerLaw (T x.ctx))]
    rfl)

 theorem raw_branch (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c)
    (P : C × A → ℚ) (E0 E1 : C × A → A)
    (hP : ∀ c a, P (c,view c a)=p c a)
    (hE0 : ∀ c a, E0 (c,view c a)=view c (next c a 0))
    (hE1 : ∀ c a, E1 (c,view c a)=view c (next c a 1)) (x : Bundle T) :
    (x.ctx,(branchLawData ((x.raw view).2.1,(x.raw view).2.2.map (fun a => P (x.ctx,a))),
      (x.raw view).2.2.flatMap (fun a => [E0 (x.ctx,a),E1 (x.ctx,a)])))=
       (x.branch p hp next).raw view := by
  simp only [Bundle.raw,Bundle.branch,states_list,List.map_ofFn,Function.comp_def,hP]
  rw [branchLaw_ofFn x.law.law _ (fun i => hp x.ctx x.law.states[i.val])]
  congr 2
  simp only [SparseIntegerLaw.branch,Vector.getElem_ofFn,List.flatMap_def,List.map_ofFn,
    Function.comp_def,hE0,hE1]
  exact (two_expand (fun i b => view x.ctx (next x.ctx x.law.states[i.val] b))).symm

noncomputable def branchProgram (a0 : A) (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c)
    (P : C × A → ℚ) (E0 E1 : C × A → A)
    (hP : ∀ c a, P (c,view c a)=p c a)
    (hE0 : ∀ c a, E0 (c,view c a)=view c (next c a 0))
    (hE1 : ∀ c a, E1 (c,view c a)=view c (next c a 1))
    (PP : PolyProgram (encodePair ec ea) Ratio.encode P)
    (PE0 : PolyProgram (encodePair ec ea) ea E0) (PE1 : PolyProgram (encodePair ec ea) ea E1) :
    PolyProgram (Bundle.encode ec ea view) (Bundle.encode ec ea view) (Bundle.branch p hp next) := by
  let c := contextProgram ec ea view
  let states := statesProgram ec ea view
  let probs := (c.fanout states).comp (PP.listMapWith a0 0)
  let law := ((lawProgram ec ea view).fanout probs).comp branchLawProgram
  let endpoints := (PE0.fanout PE1).comp pairList
  let outputstates := (c.fanout states).comp (endpoints.listFlatMapWith a0 a0)
  let work := c.fanout (law.fanout outputstates)
  exact work.recode id (fun _ => rfl) (fun x => by
    exact congrArg (encodePair ec (ed ea)) (raw_branch view p hp next P E0 E1 hP hE0 hE1 x))

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
