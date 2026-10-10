import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRepeat
import OAI.Combinatorics.KMedian.Process.RoundingStateCompiler
import OAI.Combinatorics.KMedian.Process.RoundingRunHeight

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

structure Input (signed : Bool) where
  n : ℕ
  β : Fin n → ℚ
  p : Vector ℚ n
  positive : signed=false → ∀ i, 0<β i
  feasible : ∀ i, 0 ≤ RationalWeightedStep.point p i ∧ RationalWeightedStep.point p i ≤ 1

def Input.raw {s : Bool} (x : Input s) : Row × Row := (List.ofFn x.β,x.p.toList)
abbrev Input.encode {s : Bool} (x : Input s) := encodePair erow erow x.raw
def Input.start {s : Bool} (x : Input s) : State s := ⟨x.n,x.β,x.positive,.dirac x.p⟩
def Input.run {s : Bool} (x : Input s) (t : ℕ) : State s :=
  ⟨x.n,x.β,x.positive,if hs : s=true then SparseSignedPartial.run x.β x.p t
    else SparseWeightedPartial.run x.β (x.positive (by simpa using hs)) x.p t⟩

theorem input_iterate {s : Bool} (x : Input s) (t : ℕ) :
    State.step^[t] x.start=x.run t := by
  cases s <;> induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    rfl

noncomputable def startProgram (s : Bool) : PolyProgram Input.encode State.encode (@Input.start s) := by
  let β := fst erow erow
  let p := snd erow erow
  let law := constant (encodePair erow erow) el ((1:ℤ),[(1:ℤ)])
  let ps := (p.fanout (constant (encodePair erow erow) (encodeList erow) [])).comp (listCons erow)
  let work := β.fanout (law.fanout ps)
  exact work.recode Input.raw (fun _ => rfl) (fun x => by
    change encodePair erow (ed erow) (List.ofFn x.β,((1,[1]),[x.p.toList]))=_
    rw [← State.encode_raw]
    rfl)

noncomputable def countProgram (s : Bool) : PolyProgram Input.encode Nat.bits (@Input.n s) :=
  ((fst erow erow).comp (listLength Ratio.encode 0)).recode Input.raw (fun _ => rfl)
    (fun x => by simp only [Function.comp_def,Input.raw,List.length_ofFn])

theorem input_bounds {s : Bool} (x : Input s) :
    x.n ≤ x.encode.length ∧ (erow (List.ofFn x.β)).length ≤ x.encode.length ∧
      (∀ i, HasHeight (x.β i) x.encode.length) ∧
      ∀ i, HasHeight (RationalWeightedStep.point x.p i) x.encode.length := by
  have he : x.encode.length=2*(erow (List.ofFn x.β)).length+1+(erow x.p.toList).length := by
    simp only [Input.encode,Input.raw,encodePair_length]
  have hn := EncodedList.length_le Ratio.encode (List.ofFn x.β)
  change (List.ofFn x.β).length ≤ (erow (List.ofFn x.β)).length at hn
  simp only [List.length_ofFn] at hn
  refine ⟨by omega,by omega,?_,?_⟩
  · intro i
    exact (Ratio.height_length _).mono ((EncodedList.member_length Ratio.encode _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).trans (by change (erow (List.ofFn x.β)).length ≤ x.encode.length; omega))
  · intro i
    have hm : RationalWeightedStep.point x.p i∈x.p.toList := by
      exact List.mem_iff_getElem.mpr ⟨i.val,by simp,by simp [RationalWeightedStep.point]⟩
    exact (Ratio.height_length _).mono ((EncodedList.member_length Ratio.encode _ _ hm).trans (by change (erow x.p.toList).length ≤ x.encode.length; omega))

def heightBound (L : ℕ) := RoundingHeight.stepHeight L L*L
def coordinateBound (L : ℕ) := 2*L*L+L
def supportBound (L : ℕ) := L+L*L+1
def stateBound (L : ℕ) :=
  2*L+1+ (2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*(L*(2*(3*coordinateBound L+10)+1))+1))

noncomputable def CPoly : Polynomial ℕ := 2*X*X+X
noncomputable def NPoly : Polynomial ℕ := X+X*X+1
noncomputable def HPoly : Polynomial ℕ :=
  ((3*(CPoly+2*X+1)+1)*NPoly+
    (2*(X+X*X+1)*(X+X*X+1+(2*CPoly)*(2*NPoly+1)))*(2*NPoly+1)*(2*NPoly))*X
noncomputable def statePolynomial : Polynomial ℕ :=
  2*X+1+(2*(2*(HPoly+4)+1+NPoly*(2*(HPoly+4)+1))+1+NPoly*(2*(X*(2*(3*CPoly+10)+1))+1))

theorem statePolynomial_eval (L : ℕ) : statePolynomial.eval L=stateBound L := by
  simp only [statePolynomial,stateBound,heightBound,coordinateBound,supportBound,CPoly,NPoly,HPoly,
    RoundingHeight.stepHeight,SparseIntegerLaw.stepHeight,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]

 theorem run_size {s : Bool} (x : Input s) (t : ℕ) (ht : t ≤ x.n) :
    (State.encode (x.run t)).length ≤ statePolynomial.eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hβ,hb,hp⟩ := input_bounds x
  have hH : RoundingHeight.stepHeight x.n L*t ≤ heightBound L := by
    unfold heightBound RoundingHeight.stepHeight SparseIntegerLaw.stepHeight
    gcongr
    exact ht.trans hn
  have hC : 2*x.n*L+L ≤ coordinateBound L := by unfold coordinateBound; gcongr
  have hN : x.n+x.n*x.n+1 ≤ supportBound L := by unfold supportBound; gcongr
  have hrow (p : Vector ℚ x.n) (hp : ∀ i, HasHeight (RationalWeightedStep.point p i) (2*x.n*L+L)) :
      (erow p.toList).length  ≤  L*(2*(3*coordinateBound L+10)+1) := by
    apply (EncodedList.length_bound Ratio.encode p.toList (3*coordinateBound L+10) ?_).trans
    · simpa only [Vector.length_toList] using Nat.mul_le_mul_right (2*(3*coordinateBound L+10)+1) hn
    · intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
      have hh := hp ⟨i,by simpa only [Vector.length_toList] using hi⟩
      exact Ratio.length_height (hh.mono hC)
  have hsize : (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length ≤ 
      2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
      supportBound L*(2*(L*(2*(3*coordinateBound L+10)+1))+1) := by
    cases s
    · apply SparseIntegerLaw.encode_length_bound _ _ (supportBound L) (heightBound L) _
      · exact (SparseWeightedPartial.run_length x.β (x.positive rfl) x.p t).trans hN
      · exact (RoundingHeight.weighted_denominator x.β (x.positive rfl) x.p L t hb hp x.feasible).trans
          (pow_le_pow_right₀ (by norm_num) hH)
      · intro i; exact hrow _ (RoundingHeight.weighted_run x.β (x.positive rfl) x.p L t hb hp x.feasible i)
    · apply SparseIntegerLaw.encode_length_bound _ _ (supportBound L) (heightBound L) _
      · exact (SparseSignedPartial.run_length x.β x.p t).trans hN
      · exact (RoundingHeight.signed_denominator x.β x.p L t hb hp x.feasible).trans
          (pow_le_pow_right₀ (by norm_num) hH)
      · intro i; exact hrow _ (RoundingHeight.signed_run x.β x.p L t hb hp x.feasible i)
  rw [statePolynomial_eval]
  have he : (State.encode (x.run t)).length = 2*(erow (List.ofFn x.β)).length+1+
      (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length := by
    exact encodePair_length _ _ _
  rw [he]
  change 2*(erow (List.ofFn x.β)).length+1+
    (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length ≤ stateBound L
  unfold stateBound
  omega

noncomputable def runProgram (s : Bool) : PolyProgram Input.encode State.encode (fun x : Input s => x.run x.n) :=
  ((stepProgram s).repeatFrom (startProgram s) (countProgram s) X statePolynomial
    (fun x => by simpa using (input_bounds x).1) (fun x i hi => by
      rw [input_iterate]; exact run_size x i hi)).congr _ (fun x => input_iterate x _)

end MetricKMedian.RoundingProgram
end

end OAI
