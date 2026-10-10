import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientNeighborhoods
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientSeparatingCuts

namespace OAI

/-! # Finite observations with uniformly small lifts on a compact set -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_finite_observation_small_lifts {n : ℕ}
    (K : Set (X n)) (hK : IsCompact K) (W : Set (G n)) (hW : W ∈ 𝓝 1) :
    ∃ (N : ℕ) (Q : X n → Fin N), Measurable Q ∧
      ∀ x ∈ K, ∀ y, Q y=Q x → ∃ g ∈ W, rightAction x g=y := by
  classical
  choose U hU hxU hsmall using fun x : X n => exists_open_small_relative_lifts x W hW
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (fun x _ => mem_iUnion.mpr ⟨x,hxU x⟩)
  let bits : X n → (s → Bool) := fun x i => decide (x ∈ U i.val)
  have hbits : Measurable bits := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_to_bool
    have he : (fun x => bits x i) ⁻¹' {true} = U i.val := by
      ext x
      simp [bits]
    rw [he]
    exact (hU i.val).measurableSet
  let Q : X n → Fin (Fintype.card (s → Bool)) := fun x => Fintype.equivFin _ (bits x)
  refine ⟨_,Q,(measurable_of_finite (Fintype.equivFin _)).comp hbits,?_⟩
  intro x hx y heq
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
  have hxy : bits y=bits x := (Fintype.equivFin _).injective heq
  have hbit := congrFun hxy ⟨i,hi⟩
  have hyi : y ∈ U i := by
    simpa only [bits,hxi,decide_true,decide_eq_true_eq] using hbit
  exact hsmall i x hxi y hyi

end DukePrimeDegree

end

end OAI
