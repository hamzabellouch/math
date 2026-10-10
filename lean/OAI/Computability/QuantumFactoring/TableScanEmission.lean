import Mathlib
import OAI.Computability.QuantumFactoring.TableDirectPhi
import OAI.Computability.QuantumFactoring.NetworkListOperationsEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k w : α→ℕ}
lemma natSubOn {a b : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.natSubOn (a x) (b x)):=
  (wordLe hb ha hw).wordMux ((ha.pair hb).comp (sub hw)) (wordConst hk hw (const _ _ 0)) hw
lemma stripOn {a m q v : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m)
    (hq : NetEmits ea q) (hv : NetEmits ea v) :
    NetEmits ea (fun x=>BitArithmetic.stripOn (a x) (m x) (q x) (v x)):=by
  have hd:=(hv.pair hq).comp (div hw)
  exact ((((hv.pair hq).comp (mod hw)).equalOn (wordConst hk hw (const _ _ 0)) hw).band
    ((TrialControlEmission.powOn hw ha hm hd).equalOn (wordConst hk hw (const _ _ 1)) hw)).wordMux hd hv hw
lemma stripUpdate {a m q : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m) (hq : NetEmits ea q) :
    NetEmits ea (fun x=>BitArithmetic.stripUpdate (a x) (m x) (q x)):=by
  have hl:=left hk hw
  exact hl.pair (stripOn (hk.unaryAdd hw) hw (hl.comp ha) (hl.comp hm) (hl.comp hq) (right hk hw))
lemma stripScan {a m : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m)
    (hq : NetsEmits ea qs) : NetEmits ea (fun x=>BitArithmetic.stripScan (a x) (m x) (qs x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((qs a).length)=>(x.2.val,x.1))
  have hmap:=hq.map (g:=fun x q=>BitArithmetic.stripUpdate (a x) (m x) q) (stripUpdate (hk.comp hx.snd) (hw.comp hx.snd) (ha.compInput hx.snd) (hm.compInput hx.snd) hq.get)
  exact (hmap.sequence (hk.unaryAdd hw)).congr (by
    intro x
    generalize qs x=l
    induction l with
    | nil=>rfl
    | cons q qs ih=>simp only [List.map_cons,BooleanNetwork.sequence,BitArithmetic.stripScan,ih])
lemma orderFromList {a m : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m)
    (hq : NetsEmits ea qs) : NetEmits ea (fun x=>BitArithmetic.orderFromList (a x) (m x) (qs x)):=
  (((identity hk).pair (hq.product hk hw)).comp (stripScan hk hw ha hm hq)).comp (right hk hw)
lemma totientPair {q v a : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (hq : NetEmits ea q) (hv : NetEmits ea v) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.totientPair (q x) (v x) (a x)):=by
  have hd:=(hv.pair hq).comp (div hw)
  have hc:=zeroWord hk hw ((hv.pair hq).comp (mod hw))
  have hweight:=(zeroWord hk hw ((hd.pair hq).comp (mod hw))).wordMux hq
    (natSubOn hk hw hq (wordConst hk hw (const _ _ 1))) hw
  exact (hc.wordMux hd hv hw).pair (hc.wordMux ((ha.pair hweight).comp (mul hw)) ha hw)
lemma totientUpdate {q : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (hq : NetEmits ea q) :
    NetEmits ea (fun x=>BitArithmetic.totientUpdate (q x)):=by
  have hl:=left hk (hw.unaryAdd hw)
  have hv:=selectSlice (hk.unaryAdd (hw.unaryAdd hw)) hw hk.unaryNat
    (fun x i=>Fin.natAdd (k x) (Fin.castAdd (w x) i)) (by intros;rfl)
  have ha:=selectSlice (hk.unaryAdd (hw.unaryAdd hw)) hw (hk.unaryNat.natAdd hw.unaryNat)
    (fun x i=>Fin.natAdd (k x) (Fin.natAdd (w x) i)) (by intros;simp only [Fin.val_natAdd];omega)
  exact hl.pair (totientPair (hk.unaryAdd (hw.unaryAdd hw)) hw (hl.comp hq) hv ha)
lemma totientScan {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hq : NetsEmits ea qs) :
    NetEmits ea (fun x=>BitArithmetic.totientScanNet (qs x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((qs a).length)=>(x.2.val,x.1))
  have hmap:=hq.map (g:=fun _ q=>BitArithmetic.totientUpdate q) (totientUpdate (hk.comp hx.snd) (hw.comp hx.snd) hq.get)
  exact (hmap.sequence (hk.unaryAdd (hw.unaryAdd hw))).congr (by
    intro x
    generalize qs x=l
    induction l with
    | nil=>rfl
    | cons q qs ih=>simp only [List.map_cons,BooleanNetwork.sequence,BitArithmetic.totientScanNet,ih])
lemma totientFromList {v : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hv : NetEmits ea v) (hq : NetsEmits ea qs) :
    NetEmits ea (fun x=>BitArithmetic.totientFromList (v x) (qs x)):=by
  have ha:=selectSlice (hk.unaryAdd (hw.unaryAdd hw)) hw (hk.unaryNat.natAdd hw.unaryNat)
    (fun x i=>Fin.natAdd (k x) (Fin.natAdd (w x) i)) (by intros;simp only [Fin.val_natAdd];omega)
  exact (((identity hk).pair (hv.pair (wordConst hk hw (const _ _ 1)))).comp (totientScan hk hw hq)).comp ha
lemma primesPhi {v : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hv : NetEmits ea v) (hq : NetsEmits ea qs) :
    NetEmits ea (fun x=>BitArithmetic.primesPhiNet (v x) (qs x)):=
  totientFromList hk hw hv (NetsEmits.repeated hw hq)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
