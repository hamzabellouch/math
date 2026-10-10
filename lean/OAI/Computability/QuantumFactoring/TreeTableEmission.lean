import Mathlib
import OAI.Computability.QuantumFactoring.FlatLookupCircuit
import OAI.Computability.QuantumFactoring.TreeVerificationEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emission
open BitStackProgram BitStackProgram.Procedure
abbrev rowCode := prodCode packCode packCode
def compRow (a : Pack) (r : Pack×Pack) : Pack×Pack:=(canonicalPack (compPack a r.1),canonicalPack (compPack a r.2))
noncomputable def compRowP : Procedure (prodCode packCode rowCode) rowCode (fun x=>compRow x.1 x.2):=by
  let a:=first packCode rowCode
  let r:=second packCode rowCode
  let b:=(first packCode packCode).comp r
  let c:=(second packCode packCode).comp r
  exact (canonicalPackP.comp (compPackP.comp (a.pair b))).pair (canonicalPackP.comp (compPackP.comp (a.pair c)))
lemma compRow_erase {k m n p : ℕ} (a : BooleanNetwork k m) (r : BooleanNetwork m n×BooleanNetwork m p) :
    compRow (erasePack a) (erasePack r.1,erasePack r.2)=(erasePack (a.comp r.1),erasePack (a.comp r.2)):=by
  apply Prod.ext <;> exact canonicalPack_erase _ _ (compPack_spec _ _ _ _ rfl rfl)
end ExactQuantumFactoring.NetworkEmission.Emission
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
def packedLog (n t : ℕ) : List (Pack×Pack):=
  ((PhysicalTree.machine n).logNets t).map (fun r=>(erasePack r.1,erasePack r.2))
lemma logCode_bound (n T j : ℕ) (hj : j≤T) :
    (listCode Emission.rowCode (packedLog n j)).length≤
      T*(8*(104*((PhysicalTree.machine n).width T+PhysicalNode.resultBound n+n+tensorWidth n n+1)^2)+4)+1:=by
  let B:=104*((PhysicalTree.machine n).width T+PhysicalNode.resultBound n+n+tensorWidth n n+1)^2
  have hw:(PhysicalTree.machine n).width j≤(PhysicalTree.machine n).width T:=by
    rw [NodeMachine.width_eq,NodeMachine.width_eq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  have h:=NativeAIG.listCode_length_bound Emission.rowCode (packedLog n j) (4*B+1) (by
    intro r hr
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
    have hc:=(PhysicalTree.machine n).logNets_counts j a ha
    have hq:(PhysicalTree.machine n).query.net.count=0:=PreparationPolynomial.treeQuery_count n
    rw [hq] at hc
    have h1: (packCode (erasePack a.1)).length≤B:=by
      have h:=packCode_bound (erasePack a.1)
      change _ ≤104*((PhysicalTree.machine n).width j+a.1.net.count+n+1)^2 at h
      exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have h2: (packCode (erasePack a.2)).length≤B:=by
      have h:=packCode_bound (erasePack a.2)
      change _ ≤104*((PhysicalTree.machine n).width j+a.2.net.count+tensorWidth n n+1)^2 at h
      exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    simp only [Emission.rowCode,prodCode,pairBits_length]
    omega)
  have hl:(packedLog n j).length=j:=by simp only [packedLog,List.length_map,NodeMachine.logNets_length]
  rw [hl] at h
  calc
    _ ≤ j*(2*(4*B+1)+2)+1:=h
    _ ≤ T*(8*B+4)+1:=by nlinarith
lemma logCode_poly {len : α→ℕ} (hn : PolyAt len n) (ht : PolyAt len t)
    (hw : PolyAt len (fun x=>(PhysicalTree.machine (n x)).width (t x))) :
    PolyAt (fun x:Σa,Fin (t a+1)=>len x.1)
      (fun x=>(listCode Emission.rowCode (packedLog (n x.1) x.2.val)).length):=by
  have hT:=ht.pull (fun x:Σa,Fin (t a+1)=>x.1)
  have hN:=hn.pull (fun x:Σa,Fin (t a+1)=>x.1)
  have hW:=hw.pull (fun x:Σa,Fin (t a+1)=>x.1)
  have hr:=PolyAt.comp PreparationPolynomial.physicalResultBound hN
  have hB:=((PolyAt.const _ 104).mul ((((hW.add hr).add hN).add (hN.mul hN) |>.add (PolyAt.const _ 1)).pow 2))
  apply ((hT.mul (((PolyAt.const _ 8).mul hB).add (PolyAt.const _ 4))).add (PolyAt.const _ 1)).of_le
  intro x
  simpa only [tensorWidth_eq] using logCode_bound (n x.1) (t x.1) x.2.val (Nat.le_of_lt_succ x.2.isLt)
lemma logNets (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) :
    Emits ea (listCode Emission.rowCode) (fun x=>packedLog (n x) (t x)):=by
  let F:=fun x j=>packedLog (n x) j
  apply stages ht (F:=F)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode Emission.rowCode)))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,F x.1 x.2.val)))
    have hN:=hn.comp hx.fst
    have hj:=hx.snd.fst
    have hp:=(previous hN hj).canonical
    have hnw:=(rowQuery hN hj).canonical.pair ((lastNode hN hj).comp (nodeResult hN)).canonical
    have hm:=(ofProcedure (Procedure.listMapWith (emptyPack,emptyPack) (emptyPack,emptyPack) Emission.compRowP)).comp (hp.pair hx.snd.snd)
    exact (hnw.listCons hm).congr (by
      intro x
      dsimp only [F,packedLog]
      simp only [NodeMachine.logNets,List.map_cons,List.map_map,Function.comp_def,Emission.compRow_erase])
  · exact logCode_poly hn.unaryPoly ht.unaryPoly (machineWidth hn ht).unaryPoly

end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
