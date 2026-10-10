import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialFields
import OAI.Computability.QuantumFactoring.NetworkAt

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b c d : α→ℕ}
lemma wordMux {s : ∀x,BooleanNetwork (a x) 1} {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hs : NetworkAt len s) (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordMux (s x) (f x) (g x)) := by
  simpa only [NetworkAt,wordMux_count] using ((hs.add hf).add hg).add ((PolyAt.const len 7).mul hb)
lemma wordLt {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordLt (f x) (g x)) :=
  of_le (((hf.add hg).add ((PolyAt.const len 48).mul hb)).add (PolyAt.const len 8))
    fun x=>wordLt_count (f x) (g x)
lemma wordLe {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordLe (f x) (g x)) := (hg.wordLt hf hb).bnot
lemma toWidth {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>OrderTrial.toWidth (c x) (f x)) :=
  hf.comp (resizeWord hb hc)
lemma modularPower (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.modularPower (b x) (c x)) := by
  apply of_le (bound:=fun x=>b x+c x*(3672*b x*b x+436*b x+36))
  · exact hb.add (hc.mul (((PolyAt.const len 3672).mul hb |>.mul hb).add
      ((PolyAt.const len 436).mul hb) |>.add (PolyAt.const len 36)))
  · exact fun x=>modularPower_count (b x) (c x)
lemma gcdNet (hb : PolyAt len b) : NetworkAt len (fun x=>BitArithmetic.gcdNet (b x)) := by
  apply of_le (bound:=fun x=>2*b x*(216*b x*b x+300*b x+100))
  · exact ((PolyAt.const len 2).mul hb).mul
      ((((PolyAt.const len 216).mul hb).mul hb).add ((PolyAt.const len 300).mul hb) |>.add
        (PolyAt.const len 100))
  · exact fun x=>gcdNet_count (b x)
lemma convergentNet (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.convergentNet (b x) (c x)) := by
  apply of_le (bound:=fun x=>(c x+1)*(600*b x*b x+600*b x+120))
  · exact (hc.add (PolyAt.const len 1)).mul
      ((((PolyAt.const len 600).mul hb).mul hb).add ((PolyAt.const len 600).mul hb) |>.add
        (PolyAt.const len 120))
  · exact fun x=>convergentNet_count (b x) (c x)
lemma pairChoice (hb : PolyAt len b) : NetworkAt len (fun x=>OrderTrial.pairChoice (b x)) := by
  apply of_le (bound:=fun x=>120*b x+31)
  · poly_at
  · exact fun x=>OrderTrial.pairChoice_count (b x)
lemma boundedRootNet (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.boundedRootNet (b x) (c x)) := by
  have hr : PolyAt len (fun x=>rootWidth (b x)) := by
    unfold rootWidth; poly_at
  apply of_le (bound:=fun x=>rootWidth (b x)+b x*(230*rootWidth (b x)+21+
      c x*(90*rootWidth (b x)*rootWidth (b x)+14*rootWidth (b x)+6)))
  · exact hr.add (hb.mul (((PolyAt.const len 230).mul hr |>.add (PolyAt.const len 21)).add
      (hc.mul ((((PolyAt.const len 90).mul hr).mul hr).add ((PolyAt.const len 14).mul hr) |>.add
        (PolyAt.const len 6)))))
  · exact fun x=>boundedRootNet_count (b x) (c x)
end NetworkAt
end ExactQuantumFactoring

end



end OAI
