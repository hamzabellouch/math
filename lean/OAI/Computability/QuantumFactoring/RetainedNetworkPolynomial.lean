import Mathlib
import OAI.Computability.QuantumFactoring.VerifiedTableOrder
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds
import OAI.Computability.QuantumFactoring.TableFavorableCount
import OAI.Computability.QuantumFactoring.PolyAt

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace RetainedPolynomial
variable {α : Type*} {len n f c : α→ℕ}
lemma primeComponentBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>primeComponentBound (n x) (c x)) := by
  have hw : PolyAt len (fun x=>componentWidth (n x)) := by unfold componentWidth;poly_at
  unfold primeComponentBound
  exact (((hc.add hw).add (hw.add (hn.mul (((hc.add hw).add
    (((PolyAt.const len 90).mul hw).mul hw)).add ((PolyAt.const len 14).mul hw) |>.add
      (PolyAt.const len 6))))).add (((PolyAt.const len 2).mul hw).mul
        (((PolyAt.const len 216).mul hw |>.mul hw).add ((PolyAt.const len 300).mul hw) |>.add
          (PolyAt.const len 100)))).add hn
lemma tableOrderBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableOrderBound (n x) (f x) (c x)) := by
  have hw : PolyAt len (fun x=>tableOrderWidth (n x) (f x)) := by unfold tableOrderWidth;poly_at
  have hC : PolyAt len (fun x=>3*c x+220*n x+50+tableOrderWidth (n x) (f x)) := by poly_at
  have hs : PolyAt len (fun x=>stripStepBound (tableOrderWidth (n x) (f x))
      (3*c x+220*n x+50+tableOrderWidth (n x) (f x))) := by unfold stripStepBound;poly_at
  unfold tableOrderBound
  exact ((hn.mul hf).mul ((((hC.add (((PolyAt.const len 90).mul hw).mul hw)).add
    ((PolyAt.const len 14).mul hw)).add (PolyAt.const len 6)).add hs) |>.add hw).add hn
lemma totientStepBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>totientStepBound (n x) (c x)) := by unfold totientStepBound;poly_at
lemma tableTotientBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableTotientBound (n x) (f x) (c x)) :=
  (hc.add hn).add ((hn.mul hf).mul (totientStepBound_at hn
    (((PolyAt.const len 3).mul hc).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50))))
lemma oddPartBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>oddPartBound (n x) (c x)) := by
  have hp:=primeComponentBound_at hn (hc.add hn)
  unfold oddPartBound;poly_at
lemma closedLevelBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>closedLevelBound (n x) (c x)) := by
  have ho:=oddPartBound_at hn hc
  unfold closedLevelBound;poly_at
lemma componentLevelBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>componentLevelBound (n x) (c x)) := by
  have hp:=primeComponentBound_at hn hc
  have hphi : PolyAt len (fun x=>componentPhiBound (n x) (c x)) := by unfold componentPhiBound;poly_at
  have hclosed:=closedLevelBound_at hn hphi
  unfold componentLevelBound;poly_at
lemma tableFavorableCountBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableFavorableCountBound (n x) (f x) (c x)) := by
  have hstep:=totientStepBound_at hn hc
  have hlev:=componentLevelBound_at hn hc
  have hinner : PolyAt len (fun x=>2*c x+96*n x+25) := by poly_at
  have hmiddle : PolyAt len (fun x=>componentLevelBound (n x) (c x)+90*n x*n x+22*n x+7+f x*(2*c x+96*n x+25)) :=
    ((((hlev.add (((PolyAt.const len 90).mul hn).mul hn)).add ((PolyAt.const len 22).mul hn)).add
      (PolyAt.const len 7)).add (hf.mul hinner))
  have hbad : PolyAt len (fun x=>tableBadCountBound (n x) (f x) (c x)) :=
    ((hn.add (PolyAt.const len 1)).mul ((((hf.mul hmiddle).add hn).add
      ((PolyAt.const len 86).mul hn)).add (PolyAt.const len 6))).add hn
  unfold tableFavorableCountBound;poly_at
lemma tableCanonicalBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableCanonicalBound (n x) (f x) (c x)) := by
  have hp:=primeComponentBound_at hn hc
  have hi : PolyAt len (fun x=>4*c x+216*n x*n x+202*n x+42) := by poly_at
  have hh : PolyAt len (fun x=>componentCongruenceBound (n x) (f x) (c x)) :=
    (((((hc.add ((PolyAt.const len 3).mul hp)).add (((PolyAt.const len 216).mul hn).mul hn)).add
      ((PolyAt.const len 500).mul hn)).add (PolyAt.const len 100)).add (hf.mul hi))
  have hi' : PolyAt len (fun x=>2*c x+216*n x*n x+154*n x+33+componentCongruenceBound (n x) (f x) (c x)) :=
    (((((PolyAt.const len 2).mul hc).add (((PolyAt.const len 216).mul hn).mul hn)).add
      ((PolyAt.const len 154).mul hn)).add (PolyAt.const len 33)).add hh
  exact (((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 48).mul hn)).add
    (PolyAt.const len 10)).add (hf.mul hi')).add (PolyAt.const len 2)
lemma resultBound_at (hn : PolyAt len n) : PolyAt len (fun x=>PhysicalNode.resultBound (n x)) :=
  (hn.mul hn).add ((hn.mul hn).mul (((PolyAt.const len 498).mul hn).add (PolyAt.const len 114)))
end RetainedPolynomial
end ExactQuantumFactoring

end



end OAI
