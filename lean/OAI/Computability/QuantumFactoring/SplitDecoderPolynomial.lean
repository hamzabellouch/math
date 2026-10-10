import Mathlib
import OAI.Computability.QuantumFactoring.WideSplitCircuit
import OAI.Computability.QuantumFactoring.NodeControlBounds
import OAI.Computability.QuantumFactoring.NetworkAtArithmetic

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace BitArithmetic
lemma firstProperNet_count {k w c : ℕ} (m : BooleanNetwork k w)
    (ds : List (BooleanNetwork k w)) (h : ∀d∈ds,d.net.count≤c) :
    (firstProperNet m ds).net.count≤w+ds.length*(2*m.net.count+4*c+216*w*w+257*w+45) := by
  induction ds with
  | nil=>simp only [firstProperNet,wordConstant_count,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons d ds ih=>
    have hd:=h d (by simp)
    have ht:=ih (fun e he=>h e (by simp [he]))
    have hp:=properOn_count m d
    simp only [firstProperNet,wordMux_count,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
end BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a w e : α→ℕ}
lemma addNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.add (w x)) :=
  of_le (((PolyAt.const len 86).mul hw).add (PolyAt.const len 6)) fun x=>add_count (w x)
lemma subNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.sub (w x)) :=
  of_le (((PolyAt.const len 158).mul hw).add (PolyAt.const len 6)) fun x=>sub_count (w x)
lemma divNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.div (w x)) :=
  of_le (((((PolyAt.const len 216).mul hw).mul hw).add ((PolyAt.const len 56).mul hw)).add
    (PolyAt.const len 6)) fun x=>div_count (w x)
lemma modNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.mod (w x)) :=
  of_le (((((PolyAt.const len 216).mul hw).mul hw).add ((PolyAt.const len 56).mul hw)).add
    (PolyAt.const len 6)) fun x=>mod_count (w x)
lemma properOn {m d : ∀x,BooleanNetwork (a x) (w x)}
    (hm : NetworkAt len m) (hd : NetworkAt len d) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.properOn (m x) (d x)) :=
  of_le ((((((PolyAt.const len 2).mul hm).add ((PolyAt.const len 3).mul hd)).add
    (((PolyAt.const len 216).mul hw).mul hw)).add ((PolyAt.const len 250).mul hw)).add
    (PolyAt.const len 45)) fun x=>properOn_count (m x) (d x)
lemma evenOn {m : ∀x,BooleanNetwork (a x) (w x)} (hm : NetworkAt len m) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.evenOn (m x)) :=
  ((hm.pair (wordConstant _ hw)).comp (modNet hw)).zeroWord hw
lemma halfWord {m : ∀x,BooleanNetwork (a x) (w x)} (hm : NetworkAt len m) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.halfWord (m x)) :=
  (hm.pair (wordConstant _ hw)).comp (divNet hw)
lemma halfPowerBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.halfPowerBits (b x) (m x) (d x)) :=
  ((hb.pair hm).pair ((hd.halfWord he).rewire _)).comp (modularPower hw he)
lemma shiftedHalfBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.shiftedHalfBits (b x) (m x) (d x)) :=
  ((((hb.halfPowerBits hm hd hw he).pair hm).comp (addNet hw)).pair
    (wordConstant _ hw)).comp (subNet hw)
lemma candidateBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.candidateBits (b x) (m x) (d x)) :=
  (((hd.zeroWord he).bnot).band (hd.evenOn he)).wordMux
    (((hb.shiftedHalfBits hm hd hw he).pair hm).comp (gcdNet hw)) (wordConstant _ hw) hw
lemma firstProperNet {m : ∀x,BooleanNetwork (a x) (w x)} {ds : ∀x,List (BooleanNetwork (a x) (w x))}
    (hm : NetworkAt len m) (hw : PolyAt len w) (hL : PolyAt len (fun x=>(ds x).length))
    (h : ∃p : Polynomial ℕ,∀x d,d∈ds x → d.net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>BitArithmetic.firstProperNet (m x) (ds x)) := by
  obtain ⟨p,hp⟩:=h
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le (hw.add (hL.mul ((((((PolyAt.const len 2).mul hm).add ((PolyAt.const len 4).mul hc)).add
    (((PolyAt.const len 216).mul hw).mul hw)).add ((PolyAt.const len 257).mul hw)).add
    (PolyAt.const len 45))))
  exact fun x=>firstProperNet_count (m x) (ds x) (hp x)
lemma rootOn {n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x+1)} (hm : NetworkAt len m)
    (hn : PolyAt len n) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.rootOn (n x) (e x) (m x)) := by
  have hr : PolyAt len (fun x=>rootWidth (n x)) := by unfold rootWidth;poly_at
  have hw:=hn.add (PolyAt.const len 1)
  exact ((hm.comp (resizeWord hw hr)).comp (boundedRootNet hn he)).comp (resizeWord hr hw)
lemma rootsOn {n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x+1)} (hm : NetworkAt len m)
    (hn : PolyAt len n) : NetworkAt len (fun x=>BitArithmetic.rootsOn (n x) (m x)) := by
  let ix:=Σx:α,Fin (n x+1)
  have he : PolyAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val) :=
    (hn.add (PolyAt.const len 1) |>.pull Sigma.fst).of_le fun xi=>Nat.le_of_lt xi.2.isLt
  obtain ⟨p,hp⟩:=(hm.pull (Sigma.fst (β:=fun x=>Fin (n x+1)))).rootOn (hn.pull Sigma.fst) he
  apply firstProperNet hm (hn.add (PolyAt.const len 1))
    (by simpa only [List.length_map,List.length_range] using hn.add (PolyAt.const len 1))
  refine ⟨p,?_⟩
  intro x d hd
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hd
  exact hp ⟨x,⟨e,List.mem_range.mp he⟩⟩
end NetworkAt
end ExactQuantumFactoring

end



end OAI
