import OAI.NumberTheory.DirichletL.Detector.HighRowsEuler
import OAI.NumberTheory.DirichletL.Detector.HighExcludedLocal

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem excludedIdealHighSeries_row_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI
