import Mathlib
import OAI.Computability.QuantumFactoring.DyadicCompletion

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion

abbrev totalWidth (q W t d : ℕ) := t+(q+(W+coinBits W t d))

def rareWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) t :=
  select (Fin.castAdd (q+(W+coinBits W t d)))
def ordinaryWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) q :=
  select (fun i => Fin.natAdd t (i.castAdd (W+coinBits W t d)))
def guessWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) W :=
  select (fun i => Fin.natAdd t (Fin.natAdd q (i.castAdd (coinBits W t d))))
def retentionWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) (coinBits W t d) :=
  select (fun i => Fin.natAdd t (Fin.natAdd q (Fin.natAdd W i)))

lemma rareWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareWires q W t d).eval (layout q W t d r)=r.1 := by
  funext i
  simp only [rareWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left]
lemma ordinaryWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (ordinaryWires q W t d).eval (layout q W t d r)=r.2.1 := by
  funext i
  simp only [ordinaryWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma guessWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (guessWires q W t d).eval (layout q W t d r)=r.2.2.1 := by
  funext i
  simp only [guessWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma retentionWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (retentionWires q W t d).eval (layout q W t d r)=r.2.2.2 := by
  funext i
  simp only [retentionWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_right]

def rareNet (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) 1 :=
  equalOn (rareWires q W t d) (wordConstant (BitVec.ofNat t 0))
lemma rareNet_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareNet q W t d).eval (layout q W t d r) 0=true ↔ rare r.1 := by
  rw [rareNet,equalOn_value,rareWires_eval,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,rare]
lemma rareNet_count (q W t d : ℕ) : (rareNet q W t d).net.count ≤ 97*t+21 := by
  have h := equalOn_count (rareWires q W t d) (wordConstant (BitVec.ofNat t 0))
  apply h.trans
  simp only [rareWires,count_select,wordConstant_count]
  omega

/-- Runtime output selection retains the entire unused ordinary computation even
on the rare branch. Neither success statistics nor future auxiliary data enter
this network. -/
def outputNet {q W : ℕ} (ordinary : BooleanNetwork q W) (t d : ℕ) :
    BooleanNetwork (totalWidth q W t d) W :=
  wordMux (rareNet q W t d) (guessWires q W t d)
    ((ordinaryWires q W t d).comp ordinary)
lemma outputNet_eval {q W t d : ℕ} (ordinary : BooleanNetwork q W)
    (r : Raw (Basis q) W t d) :
    (outputNet ordinary t d).eval (layout q W t d r)=output ordinary.eval r := by
  rw [outputNet,wordMux_eval,guessWires_eval,eval_comp,ordinaryWires_eval,output]
  simp only [rareNet_eval r]
lemma outputNet_count {q W : ℕ} (ordinary : BooleanNetwork q W) (t d : ℕ) :
    (outputNet ordinary t d).net.count ≤ ordinary.net.count+97*t+7*W+21 := by
  rw [outputNet,wordMux_count,count_comp]
  have h := rareNet_count q W t d
  simp only [guessWires,ordinaryWires,count_select] at *
  omega

/-- Constant-zero fresh blocks are explicit gates, rather than analytical
initialization assumptions about the raw sampler layout. -/
def zeros (k m : ℕ) : BooleanNetwork k m := vector (fun _ => constant false)
lemma zeros_eval (k m : ℕ) (x : Basis k) : (zeros k m).eval x=fun _ => false := by
  funext i
  simp only [zeros,eval_vector,eval_constant]
lemma zeros_count (k m : ℕ) : (zeros k m).net.count=m := by
  simp [zeros]

def initialNet {k q : ℕ} (ordinary : BooleanNetwork k q) (W t d : ℕ) :
    BooleanNetwork k (totalWidth q W t d) :=
  (zeros k t).pair (ordinary.pair ((zeros k W).pair (zeros k (coinBits W t d))))
lemma initialNet_eval {k q W t d : ℕ} (ordinary : BooleanNetwork k q) (x : Basis k) :
    (initialNet ordinary W t d).eval x=
      layout q W t d ((fun _ => false),ordinary.eval x,(fun _ => false),(fun _ => false)) := by
  simp only [initialNet,eval_pair,zeros_eval,layout,productLayout_apply,Equiv.refl_apply]
lemma initialNet_count {k q : ℕ} (ordinary : BooleanNetwork k q) (W t d : ℕ) :
    (initialNet ordinary W t d).net.count=ordinary.net.count+t+W+coinBits W t d := by
  simp only [initialNet,count_pair,zeros_count]
  omega

end Completion
end ExactQuantumFactoring


end

end OAI
