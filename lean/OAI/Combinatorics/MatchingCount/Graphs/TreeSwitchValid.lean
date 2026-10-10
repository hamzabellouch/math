import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeQuadDistinct

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
abbrev SwitchInput (C E V : Type) := (C×Finset E)×(Quad V×Quad E)
def switchValid (p : C×(E×(V×V))→Bool) (x : SwitchInput C E V) : Bool :=
  decide (Function.Injective (quadFn x.2.1) ∧
    (∀ i : Fin 4,p (x.1.1,(quadFn x.2.2 i,(quadFn x.2.1 i,quadFn x.2.1 (i+1))))=true) ∧
    x.2.2.1.1≠x.2.2.2.1 ∧ x.2.2.1.1∈x.1.2 ∧ x.2.2.2.1∈x.1.2)

def switchValidRealizer {p : C×(E×(V×V))→Bool} (P : Realizer p)
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchValid p) := by
  let V0 : Realizer (fun x : SwitchInput C E V=>x.2.1.1.1) := second.fst.fst.fst
  let V1 : Realizer (fun x : SwitchInput C E V=>x.2.1.1.2) := second.fst.fst.snd
  let V2 : Realizer (fun x : SwitchInput C E V=>x.2.1.2.1) := second.fst.snd.fst
  let V3 : Realizer (fun x : SwitchInput C E V=>x.2.1.2.2) := second.fst.snd.snd
  let E0 : Realizer (fun x : SwitchInput C E V=>x.2.2.1.1) := second.snd.fst.fst
  let E1 : Realizer (fun x : SwitchInput C E V=>x.2.2.1.2) := second.snd.fst.snd
  let E2 : Realizer (fun x : SwitchInput C E V=>x.2.2.2.1) := second.snd.snd.fst
  let E3 : Realizer (fun x : SwitchInput C E V=>x.2.2.2.2) := second.snd.snd.snd
  let T0 := composition (pair first.fst (pair E0 (pair V0 V1))) P
  let T1 := composition (pair first.fst (pair E1 (pair V1 V2))) P
  let T2 := composition (pair first.fst (pair E2 (pair V2 V3))) P
  let T3 := composition (pair first.fst (pair E3 (pair V3 V0))) P
  let allFits := composition (pair (composition (pair T0 T1) boolAnd) (composition (pair T2 T3) boolAnd)) boolAnd
  let distinctEdges := composition (composition (pair E0 E2) EqE) boolNot
  let membership := composition (pair (composition (pair E0 first.snd) (finsetMember EqE))
    (composition (pair E2 first.snd) (finsetMember EqE))) boolAnd
  exact (composition (pair (composition second.fst (quadInjective EqV LeV))
    (composition (pair allFits (composition (pair distinctEdges membership) boolAnd)) boolAnd)) boolAnd).congr (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,
        decide_eq_true_eq,switchValid]
      apply and_congr_right'
      apply and_congr_left'
      constructor
      · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ i
        fin_cases i <;> assumption
      · intro h
        exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩)
lemma polynomial_switchValid {p : C×(E×(V×V))→Bool} {P : Realizer p}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime EqE) (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (switchValidRealizer P EqE EqV LeV) := by
  unfold switchValidRealizer Realizer.fst Realizer.snd
  dsimp only
  have := polynomial_quadInjective hV hlV
  apply polynomial_congr
  tree_cost

omit [Codec E] [Codec V] [Codec C] in
lemma switchValid_eq [Fintype E] [Fintype V] (ends : E→Sym2 V)
    (p : C×(E×(V×V))→Bool) (c : C)
    (hp : ∀ e v w,p (c,(e,(v,w)))=decide (ends e=s(v,w))) (M : Finset E) (q : Quad V×Quad E) :
    switchValid p ((c,M),q)=true ↔ (quadFn q.1,quadFn q.2)∈Transport.Sparse.switchPatterns ends M := by
  have he (e : E) (v w : V) : ends e=s(v,w) ↔ ∀ x,x∈ends e ↔ x=v ∨ x=w := by
    constructor
    · intro h; simp [h]
    · intro h; apply Sym2.ext; intro x; simpa using h x
  simp only [switchValid,decide_eq_true_eq,Transport.Sparse.switchPatterns,
    Finset.mem_filter,Finset.mem_univ,true_and,hp,Finset.insert_subset_iff,
    Finset.singleton_subset_iff]
  change (_ ∧ (∀ i,ends (quadFn q.2 i)=s(quadFn q.1 i,quadFn q.1 (i+1))) ∧ _ ∧ _ ∧ _) ↔ _
  simp_rw [he]
  rfl
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
