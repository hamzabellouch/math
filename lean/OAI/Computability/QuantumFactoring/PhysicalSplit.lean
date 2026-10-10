import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalOrderNetworks
import OAI.Computability.QuantumFactoring.PhysicalListNetworks
import OAI.Computability.QuantumFactoring.FixedSplit
import OAI.Computability.QuantumFactoring.AdaptivePrepared

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace FixedSplit

abbrev ordersWidth (n : ℕ) := tensorWidth (OrderSlots.width n) (n^5)
def ordersLayout (n : ℕ) : (Fin (n^5)→OrderSlots.Result n)≃Basis (ordersWidth n) :=
  (Equiv.piCongrRight (fun _ => OrderSlots.layout n)).trans (tensorLayout (OrderSlots.width n) (n^5))
def ordersProgram (n : ℕ) : List (Instruction (ordersWidth n)) := tensorProgram (OrderSlots.program n) (n^5)

lemma ordersProgram_state {n : ℕ} (m : Basis n) (aa : Fin (n^5)→Basis n) :
    (programMatrix (ordersProgram n)).mulVec
      (basisVector (ordersLayout n (fun i=>OrderSlots.zero (aa i) m)))=
    encodeState (ordersLayout n) (productState (fun i=>OrderSlots.fresh n (aa i) m)) := by
  funext x
  obtain ⟨y,rfl⟩ := (ordersLayout n).surjective x
  rw [encodeState_at _ (ordersLayout n).injective]
  change (programMatrix (tensorProgram (OrderSlots.program n) (n^5))).mulVec
    (basisVector (tensorLayout _ _ (fun i=>OrderSlots.layout n (OrderSlots.zero (aa i) m))))
    (tensorLayout _ _ (fun i=>OrderSlots.layout n (y i)))= _
  rw [tensorProgram_entry]
  simp only [OrderSlots.program_entry,productState]

def listWires (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) (PhysicalListSlots.width n) :=
  select (targetRegister n (PhysicalListSlots.width n) (PhysicalListSlots.work n))
def modulusWires (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) n :=
  select (firstRegister n (PhysicalListSlots.width n) (PhysicalListSlots.work n))
def listEncoding {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) : Basis (PhysicalListSlots.launchWidth n) :=
  packed (PhysicalListSlots.work n) m (PhysicalListSlots.layout n l)
lemma listWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (listWires n).eval (listEncoding m l)=PhysicalListSlots.layout n l := by
  exact packed_targetRegister m _
lemma modulusWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (modulusWires n).eval (listEncoding m l)=m := packed_first m _

def baseNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (PhysicalListSlots.launchWidth n) n :=
  ((listWires n).comp (PhysicalListSlots.outputNet n)).rewire
    (fun j=>Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))
lemma baseNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (l : PhysicalListSlots.Result n) :
    (baseNet i).eval (listEncoding m l)=bases l i := by
  rw [baseNet,eval_rewire,eval_comp,listWires_eval,PhysicalListSlots.outputNet_eval]
  rfl
lemma baseNet_count {n : ℕ} (i : Fin (n^5)) :
    (baseNet i).net.count=(PhysicalListSlots.outputNet n).net.count := by
  simp only [baseNet,count_rewire,count_comp,listWires,count_select,zero_add]

def orderInitialNet {n : ℕ} (i : Fin (n^5)) :
    BooleanNetwork (PhysicalListSlots.launchWidth n) (OrderSlots.width n) :=
  ((baseNet i).pair (modulusWires n)).comp (OrderSlots.initialNet n)
lemma orderInitialNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (l : PhysicalListSlots.Result n) :
    (orderInitialNet i).eval (listEncoding m l)=OrderSlots.layout n (OrderSlots.zero (bases l i) m) := by
  rw [orderInitialNet,eval_comp,eval_pair,baseNet_eval,modulusWires_eval,OrderSlots.initialNet_eval]
lemma orderInitialNet_count {n : ℕ} (i : Fin (n^5)) :
    (orderInitialNet i).net.count=(PhysicalListSlots.outputNet n).net.count+(OrderSlots.initialNet n).net.count := by
  simp only [orderInitialNet,count_comp,count_pair,baseNet_count,modulusWires,count_select,add_zero]

def ordersInitialNet (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) (ordersWidth n) :=
  tensorNetwork (fun i=>orderInitialNet (n:=n) i)
lemma ordersInitialNet_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (ordersInitialNet n).eval (listEncoding m l)=ordersLayout n (fun i=>OrderSlots.zero (bases l i) m) := by
  rw [ordersInitialNet,tensorNetwork_eval]
  simp only [orderInitialNet_eval]
  rfl
lemma ordersInitialNet_count (n : ℕ) : (ordersInitialNet n).net.count=
    n^5*((PhysicalListSlots.outputNet n).net.count+(OrderSlots.initialNet n).net.count) := by
  rw [ordersInitialNet,tensorNetwork_count]
  simp only [orderInitialNet_count,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

abbrev work (n : ℕ) := (ordersInitialNet n).net.count
abbrev width (n : ℕ) := PhysicalListSlots.launchWidth n+ordersWidth n+work n
/-- One actual fixed-gate circuit: the completed random list is generated first;
only that same list supplies the bases for the ensuing order slots. -/
def program (n : ℕ) : List (Instruction (width n)) :=
  appendPrepared (PhysicalListSlots.launch n) (ordersInitialNet n) le_rfl (ordersProgram n)
def encoding {n : ℕ} (m : Basis n) (r : Raw n) : Basis (width n) :=
  packed (work n) (listEncoding m r.1) (ordersLayout n r.2)
def zero {n : ℕ} (m : Basis n) : Basis (width n) :=
  packed (work n) (packed (PhysicalListSlots.work n) m (fun _=>false)) (fun _=>false)

theorem program_state {n : ℕ} (m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (zero m))=encodeState (encoding m) (fresh m) := by
  apply appendPrepared_state (listEncoding m) (ordersLayout n) (PhysicalListSlots.fresh m)
    (fun l=>productState (fun i=>OrderSlots.fresh n (bases l i) m))
    (PhysicalListSlots.launch n) (packed (PhysicalListSlots.work n) m (fun _=>false))
    (PhysicalListSlots.launch_state m) (ordersInitialNet n) le_rfl (ordersProgram n)
  intro l
  rw [ordersInitialNet_eval,ordersProgram_state]

lemma encoding_injective {n : ℕ} (m : Basis n) : Function.Injective (encoding m) := by
  intro a b hh
  have he : (listEncoding m a.1,ordersLayout n a.2)=(listEncoding m b.1,ordersLayout n b.2) :=
    packed_pair_injective _ _ _ hh
  apply Prod.ext
  · apply (PhysicalListSlots.layout n).injective
    have h : (m,PhysicalListSlots.layout n a.1)=(m,PhysicalListSlots.layout n b.1) :=
      packed_pair_injective _ _ _ (congrArg Prod.fst he)
    exact congrArg Prod.snd h
  · exact (ordersLayout n).injective (congrArg Prod.snd he)

lemma program_length (n : ℕ) : (program n).length ≤
    (PhysicalListSlots.launch n).length+4*work n+2*ordersWidth n+n^5*(OrderSlots.program n).length := by
  have h := appendPrepared_length (PhysicalListSlots.launch n) (ordersInitialNet n) le_rfl (ordersProgram n)
  simpa only [program,work,ordersProgram,tensorProgram_length] using h

end FixedSplit
end ExactQuantumFactoring


end

end OAI
