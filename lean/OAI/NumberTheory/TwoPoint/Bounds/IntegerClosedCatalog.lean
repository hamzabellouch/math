import OAI.NumberTheory.TwoPoint.Bounds.IntegerShiftGeometry

namespace OAI

/-! A fixed-length numerical closed word remembers both forced matrix paths.
Only their starting site and external copy indices remain outside this code. -/

namespace TwoPointCorrelations

variable {D : Type*}

theorem integerStepWord_injective (Q : Finset ℕ) (tuple : D → ℕ)
    (hinj : Function.Injective tuple) (k : ℕ) :
    Function.Injective (integerStepWord (D := D) Q tuple (k := k)) := by
  intro a b hab
  have hs : (fun i => SignedStep.mk (a i).2.2 (tuple (a i).1) (a i).2.1.val) =
      (fun i => SignedStep.mk (b i).2.2 (tuple (b i).1) (b i).2.1.val) := by
    apply List.ofFn_injective
    simpa only [integerStepWord, List.map_ofFn, Function.comp_def] using hab
  funext i
  apply Prod.ext
  · exact hinj (congrArg SignedStep.tuple (congrFun hs i))
  · apply Prod.ext
    · exact Subtype.ext (congrArg SignedStep.padding (congrFun hs i))
    · exact congrArg SignedStep.forward (congrFun hs i)

def integerClosedWordCode (Q : Finset ℕ) (tuple : D → ℕ) {k : ℕ}
    (a : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool))) : List SignedStep :=
  integerStepWord Q tuple a.1 ++ reverseWord (integerStepWord Q tuple a.2)

theorem integerClosedWordCode_injective (Q : Finset ℕ) (tuple : D → ℕ)
    (hinj : Function.Injective tuple) (k : ℕ) :
    Function.Injective (integerClosedWordCode (D := D) Q tuple (k := k)) := by
  intro a b hab
  have hlen (w : Fin k → D × (Q × Bool)) : (integerStepWord Q tuple w).length = k := by
    simp only [integerStepWord, List.length_map, List.length_ofFn]
  have htake (w : Fin k → D × (Q × Bool)) : (integerStepWord Q tuple w).take k =
      integerStepWord Q tuple w := by
    simpa only [hlen] using (List.take_length (l := integerStepWord Q tuple w))
  have hdrop (w : Fin k → D × (Q × Bool)) : (integerStepWord Q tuple w).drop k = [] := by
    simpa only [hlen] using (List.drop_length (l := integerStepWord Q tuple w))
  apply Prod.ext
  · apply integerStepWord_injective Q tuple hinj k
    have he := congrArg (List.take k) hab
    simpa only [integerClosedWordCode, List.take_append, hlen, Nat.sub_self,
      List.take_zero, List.append_nil, htake] using he
  · apply integerStepWord_injective Q tuple hinj k
    have he := congrArg (List.drop k) hab
    have hr : reverseWord (integerStepWord Q tuple a.2) =
        reverseWord (integerStepWord Q tuple b.2) := by
      simpa only [integerClosedWordCode, List.drop_append, hlen, Nat.sub_self,
        List.drop_zero, hdrop, List.nil_append] using he
    simpa only [reverseWord_reverseWord] using congrArg reverseWord hr

end TwoPointCorrelations

end OAI
