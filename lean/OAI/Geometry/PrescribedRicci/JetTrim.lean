import Mathlib
import OAI.Geometry.PrescribedRicci.ComplexJetProduct
import OAI.Geometry.PrescribedRicci.JetRemainder

namespace OAI

/-! Jet Trim. -/

section

 

noncomputable section
open Set Finset MeasureTheory
open scoped ContDiff Classical BigOperators ENNReal
namespace TameInterpolation
variable {ι κ : Type*}

def trimWord : List ι → List ι
  | [] => []
  | [_] => []
  | a::b::ws => a::trimWord (b::ws)
def baseDirection : List ι → Option ι
  | [] => none
  | [a] => some a
  | _::b::ws => baseDirection (b::ws)

lemma trimWord_length (ws : List ι) : (trimWord ws).length = ws.length-1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih => cases ws <;> simp_all [trimWord]

lemma trimWord_length_add (ws : List ι) :
    (trimWord ws).length + (if ws = [] then 0 else 1) = ws.length := by
  rw [trimWord_length]
  cases ws <;> simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def initialJet (e : ι → E) (f : κ → E → ℂ) (q : κ × Option ι) : E → ℂ :=
  match q.2 with
  | none => f q.1
  | some a => cdir (e a) (f q.1)

lemma initialJet_smooth (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (q : κ × Option ι) :
    ContDiff ℝ ∞ (initialJet e f q) := by
  rcases q with ⟨i,q⟩; cases q
  · exact hf i
  · exact cdir_smooth _ (hf i)

lemma initialJet_compact (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ i, HasCompactSupport (f i)) (q : κ × Option ι) :
    HasCompactSupport (initialJet e f q) := by
  rcases q with ⟨i,q⟩; cases q
  · exact hf i
  · exact cdir_compact _ (hf i)

lemma cword_trim (e : ι → E) (f : κ → E → ℂ) (i : κ) (ws : List ι) :
    cword e (f i) ws = cword e (initialJet e f (i,baseDirection ws)) (trimWord ws) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    cases ws with
    | nil => rfl
    | cons b ws => exact congrArg (cdir (e a)) ih

lemma cword_eq_cjet (e : ι → E) (f : E → ℂ) (ws : List ι) :
    cword e f ws = cjet e f ws.get := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change cdir (e a) (cword e f ws) = cdir (e a) (cjet e f (fun i => (a::ws).get i.succ))
    rw [ih]
    rfl

variable [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ] in
lemma trimmed_order (s : κ → List ι) :
    (∑ i, (trimWord (s i)).length) + (activeSet s).card = stateOrder s := by
  have hcard : (activeSet s).card = ∑ i, if s i = [] then 0 else 1 := by
    classical
    simp [activeSet,Finset.card_filter,ite_not]
  rw [hcard,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => trimWord_length_add (s i))

lemma remainder_trimmed_order {ws : List ι} {s : κ → List ι} (hs : s ∈ monoRemainder ws) :
    ∑ i, (trimWord (s i)).length ≤ ws.length-2 := by
  have h := monoRemainder_order ws s hs
  have he := trimmed_order s
  omega

variable [Fintype ι] [Nonempty ι] [Nonempty κ]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq κ] in
theorem monoEval_tame_positive (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (s : κ → List ι) (hm : 0 < ∑ i, (trimWord (s i)).length) :
    let m := ∑ i, (trimWord (s i)).length
    lpNorm (monoEval e f s) 2 volume ≤
      2^(Fintype.card κ) * ((2*(m:ℝ))^(∑ i, (trimWord (s i)).length*(m-(trimWord (s i)).length)) *
        familyJetNorm e (realComponents (initialJet e f)) 0 ∞ ^ (Fintype.card κ-1) *
          familyJetNorm e (realComponents (initialJet e f)) m 2) := by
  dsimp only
  have he : monoEval e f s = fun x => ∏ i, cjet e
      (initialJet e f (i,baseDirection (s i))) (trimWord (s i)).get x := by
    funext x
    unfold monoEval
    apply Finset.prod_congr rfl
    intro i _
    rw [cword_trim e f i (s i),cword_eq_cjet]
  rw [he]
  exact cjet_product_L2 e (initialJet e f) (initialJet_smooth e f hf)
    (initialJet_compact e f hc) _ hm Finset.univ
    (fun i => (i,baseDirection (s i))) (fun i => (trimWord (s i)).length)
    (fun i => (trimWord (s i)).get) rfl
end TameInterpolation

end
end

end OAI
