import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.Dual
import OAI.Combinatorics.KMedianRecovery.Recovery.ClassSlotsMem
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricArrays

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
def equiv_dual (D : Finset V) : Fin D.card ≃ D := (D.orderIsoOfFin rfl).toEquiv
lemma equiv_dual_val (D : Finset V) (i : Fin D.card) : (equiv_dual D i).val=enum D i := rfl
lemma enum_symm (D : Finset V) (j : D) : enum D ((equiv_dual D).symm j)=j.val := by
  rw [←equiv_dual_val,Equiv.apply_symm_apply]
lemma image_enum (D : Finset V) : Finset.univ.image (enum D)=D := by
  ext j
  constructor
  · intro hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact enum_mem D i
  · intro hj
    exact Finset.mem_image.mpr ⟨(equiv_dual D).symm ⟨j,hj⟩,Finset.mem_univ _,enum_symm D ⟨j,hj⟩⟩
lemma sum_enum_dual {M : Type*} [AddCommMonoid M] (D : Finset V) (f : V→M) :
    (∑ j,f (enum D j))=∑ p∈D,f p := by
  rw [←Finset.sum_coe_sort D f]
  exact Equiv.sum_comp (equiv_dual D) (fun j:D=>f j.val)
variable [PseudoMetricSpace V]
lemma sum_cost (D S : Finset V) : (∑ j,nearestDistance (enum D j) S)=LocalSearch.cost D S := by
  exact sum_enum_dual D (fun p=>nearestDistance p S)
lemma dual_on_points (D F : Finset V) (v lam : ℝ) (alpha : Fin D.card→ℝ)
    (h : PhaseOriginalLedger.Dual (enum D) F v lam alpha) :
    PhaseOriginalLedger.Dual (fun j:D=>j.val) F v lam (alpha ∘ (equiv_dual D).symm) := by
  classical
  have hh : PhaseOriginalLedger.Dual (enum D ∘ (equiv_dual D).symm) F v lam
      (alpha ∘ (equiv_dual D).symm) := by
    let indexEquiv := (equiv_dual D).symm
    refine ⟨fun point=>h.1 (indexEquiv point),?_,?_⟩
    · intro facility facility_mem
      have sum_reindex := Equiv.sum_comp indexEquiv
        (fun index=>max (alpha index-2*dist facility (enum D index)) 0)
      simpa only [Function.comp_apply] using sum_reindex.trans_le (h.2.1 facility facility_mem)
    · intro clients clients_nonempty facility facility_mem price price_pos distances_pos price_bound gap_bound
      have distances_eq : (∑ index∈clients.image indexEquiv,dist facility (enum D index))=
          ∑ point∈clients,dist facility ((enum D ∘ indexEquiv) point) := by
        rw [Finset.sum_image]
        · rfl
        · exact fun _ _ _ _ equality=>indexEquiv.injective equality
      have alpha_eq : (∑ index∈clients.image indexEquiv,alpha index)=
          ∑ point∈clients,(alpha ∘ indexEquiv) point := by
        rw [Finset.sum_image]
        · rfl
        · exact fun _ _ _ _ equality=>indexEquiv.injective equality
      simpa only [distances_eq,alpha_eq] using h.2.2 (clients.image indexEquiv)
        (clients_nonempty.image indexEquiv) facility facility_mem price price_pos
        (distances_eq ▸ distances_pos) (distances_eq ▸ price_bound) gap_bound
  have he : enum D ∘ (equiv_dual D).symm = (fun j:D=>j.val) := by
    funext j
    exact enum_symm D j
  rw [he] at hh
  exact hh
omit [PseudoMetricSpace V] in
lemma sum_budget (D : Finset V) (alpha : Fin D.card→ℝ) :
    (∑ j:D,(alpha ∘ (equiv_dual D).symm) j)=∑ j,alpha j := Equiv.sum_comp (equiv_dual D).symm alpha
end MetricKMedianRecovery.SortedIndex

end OAI
