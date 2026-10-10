import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEndpointPorts

namespace OAI

/-! The endpoint arm assigned to an incident interaction is the number of
incident lane colors below it. This exposes the finite count used by the
literal route evaluator. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPort_orderRank {C : ℕ} (s : Finset (Fin C)) (x : s) :
    ((s.orderIsoOfFin rfl).symm x).val = (s.filter (fun y => y < x.val)).card := by
  let E := s.orderIsoOfFin rfl
  have h : (Finset.Iio (E.symm x)).card = (s.filter (fun y => y < x.val)).card := by
    apply Finset.card_bij (fun i _ => (E i).val)
    · intro i hi
      refine Finset.mem_filter.mpr ⟨(E i).property,?_⟩
      have hh := E.strictMono (Finset.mem_Iio.mp hi)
      change (E i).val < (E (E.symm x)).val at hh
      simpa only [E.apply_symm_apply] using hh
    · intro i hi j hj hij
      exact E.injective (Subtype.ext hij)
    · intro y hy
      obtain ⟨hys,hyx⟩ := Finset.mem_filter.mp hy
      refine ⟨E.symm ⟨y,hys⟩,Finset.mem_Iio.mpr ?_,?_⟩
      · exact E.symm.strictMono hyx
      · exact congrArg Subtype.val (E.apply_symm_apply ⟨y,hys⟩)
  simpa only [Fin.card_Iio] using h

theorem qmaCanonicalSortedPorts_assign_rank {κ : Type} [Fintype κ] {C : ℕ}
    (color : κ → Fin C) (hc : Fintype.card κ ≤ 3) (hi : Function.Injective color) (e : κ) :
    ((qmaCanonicalSortedPorts color hc).assign e).val =
      (Finset.univ.filter (fun f => color f < color e)).card := by
  let s := Finset.univ.image color
  have he : color e ∈ s := Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
  change ((s.orderIsoOfFin rfl).symm ⟨color e,he⟩).val = _
  rw [qmaPort_orderRank]
  symm
  apply Finset.card_bij (fun f _ => color f)
  · intro f hf
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨f,Finset.mem_univ _,rfl⟩,(Finset.mem_filter.mp hf).2⟩
  · intro f hf g hg h
    exact hi h
  · intro y hy
    obtain ⟨hys,hy⟩ := Finset.mem_filter.mp hy
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hys
    exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,rfl⟩

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointPorts_assign_rank (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) (e : M.Incident v) :
    ((M.endpointPorts hd v).assign e).val =
      (Finset.univ.filter (fun f : M.Incident v => M.laneColor f.val < M.laneColor e.val)).card :=
  qmaCanonicalSortedPorts_assign_rank _ _ (M.incident_color_injective hA v) e

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
