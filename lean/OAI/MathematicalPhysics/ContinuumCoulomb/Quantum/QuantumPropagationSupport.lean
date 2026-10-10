import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDelta
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumScalarReindex

namespace OAI

/-! The literal, duplicate-free five-site propagation support.  Lookup in its
encoded labels agrees with the zero extension used by the actual local core. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSupport
open QuantumHistoryBitProgram QuantumHistoryDiagonal QuantumOrderedSupport
open scoped Classical

def sites (c : QMACircuit) (t : Fin c.gates.length) : List (QMACircuitQubit c) :=
  (propagationSites c t).dedup

theorem sites_nodup (c : QMACircuit) (t : Fin c.gates.length) :
    (sites c t).Nodup := List.nodup_dedup _

theorem sites_finset (c : QMACircuit) (t : Fin c.gates.length) :
    (sites c t).toFinset=qmaPropagationSites c t := by
  simpa only [sites,List.toFinset_dedup] using propagationSites_finset c t

theorem sites_length (c : QMACircuit) (t : Fin c.gates.length) :
    (sites c t).length≤5 :=
  (List.dedup_sublist _).length_le.trans (propagationSites_length c t)

def supportEquiv (c : QMACircuit) (t : Fin c.gates.length) :
    Fin (sites c t).length ≃ {q // q∈qmaPropagationSites c t} :=
  (List.Nodup.getEquiv (sites c t) (sites_nodup c t)).trans
    (Equiv.subtypeEquivRight (fun q => by
      have he := congrArg (fun S : Finset (QMACircuitQubit c) => q∈S) (sites_finset c t)
      exact List.mem_toFinset.symm.trans (Iff.of_eq he)))

theorem supportEquiv_apply (c : QMACircuit) (t : Fin c.gates.length)
    (i : Fin (sites c t).length) : (supportEquiv c t i).val=(sites c t).get i := rfl

def labels (c : QMACircuit) (t : Fin c.gates.length) : List ℕ :=
  (sites c t).map (fun q => siteNumber c (.inr q))

def data (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) : Data :=
  (labels c t,List.ofFn (fun i => (s i).val),List.ofFn (fun i => (r i).val))

theorem lookup_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s : Fin (sites c t).length → Fin 2) (q : QMACircuitQubit c) :
    QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
      List.ofFn (fun i => (s i).val))=
      (qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q).val := by
  have hf : Function.Injective (fun q : QMACircuitQubit c => siteNumber c (.inr q)) := by
    intro a b h
    exact Sum.inr_injective (siteNumber_injective c h)
  by_cases hq : q∈qmaPropagationSites c t
  · let i := (supportEquiv c t).symm ⟨q,hq⟩
    have hi : (sites c t).get i=q :=
      congrArg Subtype.val ((supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumSupportLookup.value_map_get (sites c t) (sites_nodup c t)
      (fun q => siteNumber c (.inr q)) hf (fun j => (s j).val) i
    have hv : QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
        List.ofFn (fun j => (s j).val))=(s i).val := by
      simpa only [hi,labels] using he
    exact hv.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=s i from dite_eq_left hq)).symm
  · have hn : siteNumber c (.inr q)∉labels c t := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := hf he
      subst p
      exact hq (by rw [← sites_finset]; exact List.mem_toFinset.mpr hp)
    have he := QuantumSupportLookup.value_not_mem (labels c t)
      (List.ofFn (fun i => (s i).val)) (siteNumber c (.inr q)) hn
      (by simp only [List.length_ofFn,labels,List.length_map,le_refl])
    exact he.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=0 from dite_eq_right hq)).symm

theorem readRow_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readRow c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => s ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

theorem readColumn_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readColumn c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => r ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

end ContinuumCoulomb.QuantumPropagationSupport

end

end OAI
