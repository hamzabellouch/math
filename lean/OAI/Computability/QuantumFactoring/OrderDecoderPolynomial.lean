import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalOrderDecoder
import OAI.Computability.QuantumFactoring.RawDecoderPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NetworkAt
variable {α : Type*} {len a w K : α→ℕ}
lemma minimumNet {f : ∀x,Fin (K x)→BooleanNetwork (a x) (w x)}
    (hK : PolyAt len K) (hw : PolyAt len w)
    (hf : NetworkAt (fun xi : Σx,Fin (K x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>OrderTrial.minimumNet (f x)) := by
  obtain ⟨p,hp⟩:=hf
  have hpoly : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le (bound:=fun x=>w x+K x*(p.eval (len x)+300*w x+60))
  · exact hw.add (hK.mul ((hpoly.add ((PolyAt.const len 300).mul hw)).add (PolyAt.const len 60)))
  · exact fun x=>minimumNet_count (f x) (fun i=>hp ⟨x,i⟩)
end NetworkAt
namespace OrderSlots
variable {α : Type*} {len k : α→ℕ} {a m : ∀x,BooleanNetwork (k x) (len x)}
lemma usableOn_poly (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>usableOn (a x) (m x)) := by
  have hn:=PolyAt.self len
  exact (ha.wordLt hm hn).band
    (((ha.pair hm).comp (NetworkAt.gcdNet hn)).equalOn (NetworkAt.wordConstant _ hn) hn)
lemma orderResultNet_poly {raw : ∀x,BooleanNetwork (k x) (ordinaryWidth (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>orderResultNet (a x) (m x) (raw x)) := by
  let ix := Σx:α,Fin ((len x)^5)
  let param : ix→α:=Sigma.fst
  have hs : NetworkAt (fun xi:ix=>len xi.1)
      (fun xi=>(raw xi.1).comp (tensorSelect (rawWidth (len xi.1)
        (sampleExponent (len xi.1)) (len xi.1)) ((len xi.1)^5) xi.2)) :=
    (hr.pull param).comp (NetworkAt.select _)
  exact NetworkAt.minimumNet ((PolyAt.self len).pow 5) (PolyAt.self len)
    (trialSmallValueNet_poly (ha.pull param) (hm.pull param) hs)
lemma ordinaryOn_poly {raw : ∀x,BooleanNetwork (k x) (ordinaryWidth (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>ordinaryOn (a x) (m x) (raw x)) := by
  have hn:=PolyAt.self len
  exact ((usableOn_poly ha hm).wordMux (orderResultNet_poly ha hm hr)
    (NetworkAt.wordConstant _ hn) hn).comp
      (NetworkAt.resizeWord hn (PolyAt.ofPoly PreparationPolynomial.transitionWidth len))
lemma outputOn_poly {raw : ∀x,BooleanNetwork (k x) (width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>outputOn (a x) (m x) (raw x)) := by
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  have hra : NetworkAt len (fun x=>Completion.rareNet (ordinaryWidth (len x))
      (Completion.transitionWidth (len x)) (2*len x) ((len x+10)*(len x)^5)) := by
    apply NetworkAt.of_le (bound:=fun x=>97*(2*len x)+21)
    · poly_at
    · exact fun x=>Completion.rareNet_count ..
  exact (hr.comp hra).wordMux (hr.comp (NetworkAt.select _))
    (ordinaryOn_poly ha hm (hr.comp (NetworkAt.select _))) hw
end OrderSlots
end ExactQuantumFactoring

end



end OAI
