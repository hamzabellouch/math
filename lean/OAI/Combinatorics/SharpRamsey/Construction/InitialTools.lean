import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.TrackedGeometry
import OAI.Combinatorics.SharpRamsey.Construction.RectangleStreamEvent

namespace OAI

section
namespace SharpLogRamsey
open Finset Real Selection Marking
open scoped Classical BigOperators
noncomputable section

namespace Selection
variable {α : Type} [Fintype α] [Nonempty α]
def uniformLaw : Law α where
  mass _:=1/(Fintype.card α:ℝ)
  nonneg _:=by positivity
  total:=by simp [Fintype.card_ne_zero]

lemma uniformLaw_event (E : Finset α) : uniformLaw.event E=FiniteStreamTail.probability E:=by
  simp only [Law.event,uniformLaw,sum_const,nsmul_eq_mul,FiniteStreamTail.probability]
  ring

lemma uniformLaw_conditioned {E : Finset α} (hE : (1:ℝ)/2 ≤ FiniteStreamTail.probability E) :
    ∀ a,((uniformLaw.onEvent E (by rw [uniformLaw_event];linarith)).map (Subtype.val : E→α)).mass a ≤
      2/(Fintype.card α:ℝ) := by
  intro a
  have hh:=uniformLaw.onEvent_map_le_two E (by rwa [uniformLaw_event]) id a
  rw [Law.map_id] at hh
  convert hh using 1 <;> simp [uniformLaw]
  ring
end Selection

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

lemma rectangle_pair_iff [Finite K] [FiniteDimensional K V] (W : Submodule K V) (f : Flag K V) :
    (flagPair f).swap∈orthogonalRectangle Projectivization.rep Projectivization.rep W ↔
      f∈RectangleStreamEvent.rectangle W := by
  simp only [orthogonalRectangle,mem_filter,mem_univ,true_and,RectangleStreamEvent.rectangle,
    InitialRectangles.IsRectangle,Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
  rfl

def initial_context {Ω : Type} [Fintype Ω] {k : ℕ} (p : Law Ω)
    (F : Ω→Fin k→Flag K V) (B : ℝ) (hB : (Fintype.card (Flag K V):ℝ) ≤ B) :
    ContextOutput p (fun x j=>flagPair (F x j)) k B 0 1 where
  X:={x // p.mass x≠0}
  Γ:=Unit
  finiteX:=inferInstance
  finiteΓ:=inferInstance
  μ:=p.nullFree
  source:=Subtype.val
  msg:=fun _=>()
  chosen:=fun _=>OrderEmbedding.ofStrictMono id (fun _ _ h=>h)
  domains:=fun _ _=>univ.map ⟨flagPair,flagPair_injective⟩
  supported:=fun x=>x.property
  hit:=fun x j=>mem_map.mpr ⟨F x.val j,mem_univ _,rfl⟩
  size:=by intro _ _;simpa only [card_map,card_univ] using hB
  dominated:=by
    intro x
    have hh:=p.nullFree_map id
    rw [Law.map_id] at hh
    have he : p.nullFree.map (Subtype.val : {x // p.mass x≠0}→Ω)=p:=by
      convert hh using 1
      congr!
    rw [he,one_mul]
  cost:=by
    have hh:=entropy_le_log_card (p.nullFree.map (fun _=>())) univ (by simp)
    simpa using hh

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma independent_selected {N k : ℕ} (z : Fin N→Flag K V)
    (h : k ≤ (flagGraph K V z).indepNum) :
    ∃ e : Fin k↪o Fin N,Consistent (fun j=>z (e j)) := by
  obtain ⟨S,hS⟩:=(flagGraph K V z).exists_isNIndepSet_indepNum
  obtain ⟨T,hTS,hTk⟩:=exists_subset_card_eq (s:=S) (n:=k) (by rwa [hS.card_eq])
  let e:=T.orderEmbOfFin hTk
  refine ⟨e,?_⟩
  have hc : ConsistentOn z T:=(consistentOn_iff_compl_isClique _ _).mpr (by
    rw [SimpleGraph.isClique_compl]
    exact hS.isIndepSet.mono (by exact_mod_cast hTS))
  intro a b hab hi
  exact hc (e a) (T.orderEmbOfFin_mem hTk a) (e b) (T.orderEmbOfFin_mem hTk b) (e.strictMono hab) hi

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma selected_reverse_consistent {N k : ℕ} (z : Fin N→Flag K V)
    (e : Fin k↪o Fin N) (hc : Consistent (fun j=>z (e j))) :
    ScanConsistent ((List.ofFn (fun j=>flagPair (z (e j.rev)))).map toScan) := by
  have hh:=backwardScan_consistent (fun j=>z (e j)) hc
  simpa only [backwardScan,List.map_ofFn,Function.comp_def,flagPair,toScan] using hh
end
end SharpLogRamsey

end

end OAI
