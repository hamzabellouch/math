import OAI.NumberTheory.Ostmann.Construction.CanonicalPrimeRecurrence
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalPair

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

def actualNodeTerm (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (X G : ℝ) (g : (q:ℕ)→ZMod q→ℂ) (bins : List ℕ→State→ℝ) (outside : List ℕ)
    (l : ℕ) (a : State) (v w : AllowedFrequency V l)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l))) : ℂ :=
  let f := canonicalFrame sources seed V l a v w u
  if f.Valid V outside l then f.scalar Ostmann.smoothPartition G*
    actualCoefficient sources seed V X G g bins outside l f.plusState*
    conj (actualCoefficient sources seed V X G g bins outside l f.minusState) else 0

theorem pivotPair_frequency_term (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l) (s : AllowedFrequency V (l+1))
    (hseed : ∀q∈seed,∀j,q.role=.compensation j → 0<j)
    (hgiants : ∀j≤l+1,V j<x.1.val ∧ V j<y.1.val)
    (hlarge : ∀q∈assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x.2,
      V (l+1)<q.value) :
    let N := joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val
    let U := ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod
    let p := reversalPivot N U s.val
    (if N≠0 ∧ p∈integerPivotCell G ∧ N=s.val*(U:ℤ)*(p:ℤ)
      then pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p else 0)=
    regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside
      (joinedRemainingState sources (Template.remainder (l+1) (Template.current seed l)) giant x y s.val)*
      actualNodeTerm sources seed V X G (residueTransform d) bins outside l
        (joinedRemainingState sources (Template.remainder (l+1) (Template.current seed l)) giant x y s.val) v w u := by
  let T := Template.current seed l
  let R := Template.remainder (l+1) T
  let us := assignedSlots sources (Template.extracted (l+1) T) u
  let N := joinedNumerator sources R giant x y v.val w.val
  let U := (us.map SmallSlot.value).prod
  let p := reversalPivot N U s.val
  let a := joinedRemainingState sources R giant x y s.val
  let f : NodeFrame := ⟨a,p,us,assignedSlots sources R x.2,assignedSlots sources R y.2,
    remainingState sources T (l+1) giant p u x v.val,
    remainingState sources T (l+1) giant p u y w.val⟩
  let W := pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p
  have hframe : canonicalFrame sources seed V l a v w u=f := canonicalFrame_joined sources seed V giant l x y s.val v w u
  have hsV := allowedFrequency_bound V (l+1) s
  have hU : (U:ℤ)≠0 := by exact_mod_cast (assignedSlots_product_pos sources _ u).ne'
  dsimp only
  unfold actualNodeTerm
  rw [hframe]
  change (if N≠0 ∧ p∈integerPivotCell G ∧ N=s.val*(U:ℤ)*(p:ℤ) then W else 0)=
    regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside a*
      (if f.Valid V outside l then f.scalar Ostmann.smoothPartition G*
        actualCoefficient sources seed V X G (residueTransform d) bins outside l f.plusState*
        conj (actualCoefficient sources seed V X G (residueTransform d) bins outside l f.minusState) else 0)
  by_cases hf : f.Valid V outside l
  · have hs : s.val≠0 := hf.1.2.2.2.2.1
    have hp : 0<p := hf.2.2.1
    have heq : N=s.val*(U:ℤ)*(p:ℤ) := hf.2.2.2.2.2.2.2.2.2.2.2
    have hN : N≠0 := by rw [heq]; exact mul_ne_zero (mul_ne_zero hs hU) (by exact_mod_cast hp.ne')
    have he := pivotPairWeight_reversal d P sources seed V giant X G bins outside l p u x y v w s.val hs
      (hsV.trans_lt (hgiants (l+1) le_rfl).1) (fun q hq => hsV.trans_lt (hlarge q hq)) heq
    change W=regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside a*
      (f.scalar Ostmann.smoothPartition G*
        actualCoefficient sources seed V X G (residueTransform d) bins outside l f.plusState*
        conj (actualCoefficient sources seed V X G (residueTransform d) bins outside l f.minusState)) at he
    rw [ite_eq_left hf,←he]
    by_cases hW : W=0
    · simp only [hW,ite_self]
    · exact ite_eq_left ⟨hN,pivotPairWeight_mem_integerCell d P sources seed V giant X G bins outside l u x y v w p hW,heq⟩
  · rw [ite_eq_right hf,mul_zero]
    split_ifs with hc
    · by_contra hW
      have hp : 0<p := (Finset.mem_Ioc.mp hc.2.1).1
      have hs : s.val≠0 := by intro hs; apply hc.1; rw [hc.2.2,hs,zero_mul,zero_mul]
      have hw := pivotPairWeight_nonzero d P sources seed V giant X G bins outside l u x y v w p hW
      have hv := canonicalFrame_joined_valid_of_remainingIntegrand_ne_zero d P sources seed V giant X G bins
        outside l p x y s.val v w u hseed hp hs hsV hgiants hlarge hw.2.1 hw.2.2 hc.2.2
      exact hf (hframe ▸ hv)
    · rfl

end Ostmann.Construction

end

end OAI
