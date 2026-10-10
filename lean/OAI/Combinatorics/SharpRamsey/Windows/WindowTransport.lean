import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.OutputComposition
import OAI.Combinatorics.SharpRamsey.Marking.ClassTransport
import OAI.Combinatorics.SharpRamsey.Windows.PopulationSublist

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α Ω Θ : Type} [Fintype Ω] [Fintype Θ] [Fintype α]

def windowTuple {w n : ℕ} (F : Fin (w*(4*n))→α) : Slot w n→α :=
  fun i=>F (finProdFinEquiv i)

omit [Fintype α] in
lemma flatten_window {w n : ℕ} (F : Fin (w*(4*n))→α) :
    flattenTuple (windowTuple F)=F := by
  funext i
  simp only [flattenTuple,windowTuple,Equiv.apply_symm_apply]

lemma window_entropy {w n : ℕ} (p : Law Ω) (F : Ω→Fin (w*(4*n))→α) :
    entropy (p.map (fun x=>windowTuple (F x)))=entropy (p.map F) := by
  rw [show (fun x=>windowTuple (F x))=windowTuple∘F from rfl,←Law.map_map]
  apply entropy_map_eq_of_injective
  intro f g h
  funext i
  have hh:=congrFun h (finProdFinEquiv.symm i)
  simpa only [windowTuple,Equiv.apply_symm_apply] using hh

end
end SharpLogRamsey.Selection.Windows

namespace SharpLogRamsey.Marking
open Finset Selection Selection.Windows ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype Ω] [Fintype Θ]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Fintype Θ] [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in

theorem reciprocal_parameters {N d : ℕ} (p : Law Ω) (θ : Ω→Θ)
    (S : Θ→Fin N→Finset (ProjectivePair (K:=K) (V:=V)))
    (integer : Bool) (r : Fin (d+1)) (gap : ℝ) (hN : 0<N)
    (hclass : ∀ x,p.mass x≠0→∀ i,ValidSlotClass d gap (S (θ x) i) (.inl (integer,r))) :
    let r':=if integer then d+1-r.val else d+2-r.val
    1≤r' ∧ r'≤d ∧ ∃ u : Θ→Fin N→ℝ,∀ x,p.mass x≠0→∀ i,
      (((covectorDomain (S (θ x) i)).image Prod.fst).card:ℝ)≤
        1024*Real.exp (((d:ℝ)+1)*Real.log (Nat.card K)-u (θ x) i) ∧
      (((covectorDomain (S (θ x) i)).image Prod.snd).card:ℝ)≤1024*Real.exp (u (θ x) i) ∧
      (if integer then IntegerBand r' (Real.log (Nat.card K)) gap (u (θ x) i)
        else OpenBand r' (Real.log (Nat.card K)) gap (u (θ x) i)) := by
  have hpos : ∃ x,p.mass x≠0 := by
    by_contra hh
    have hz : ∀ x,p.mass x=0:=by simpa only [not_exists,not_not] using hh
    have hh:=p.total
    simp only [hz,sum_const_zero] at hh
    norm_num at hh
  obtain ⟨x,hx⟩:=hpos
  have hh:=covectorDomain_reciprocal (S (θ x) ⟨0,hN⟩) integer r (hclass x hx _)
  refine ⟨hh.1,hh.2.1,?_,?_⟩
  · exact fun z i=>if h : ValidSlotClass d gap (S z i) (.inl (integer,r)) then
      (covectorDomain_reciprocal (S z i) integer r h).2.2.choose else 0
  · intro x hx i
    simp only [dite_eq_left (hclass x hx i)]
    have huv:=(covectorDomain_reciprocal (S (θ x) i) integer r (hclass x hx i)).2.2.choose_spec
    refine ⟨huv.2.2.1,huv.2.2.2.1,?_⟩
    cases integer <;> simp only [Bool.false_eq_true,ite_false,ite_true] at huv ⊢
    · exact huv.2.2.2.2.2
    · exact huv.2.2.2.2
end
end SharpLogRamsey.Marking

end

end OAI
