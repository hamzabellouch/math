import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalSplitting

namespace OAI


                                                
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset RationalIntervals
variable {f j : ℕ}

theorem sum_fiber_nonneg (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hy : ∀ i, 0≤y i) (hx : ∀ c i, x c i≤y i) (i : Fin f) :
    (∑ q : ↥(cuts y x i), length (cuts y x i) q.val)=y i := by
  by_cases h : 0<y i
  · rw [sum_coe_sort,sum_lengths _ (cuts_pos y x i)]
    exact height_eq _ (y i) (mem_filter.mpr ⟨mem_insert_self _ _,h⟩) h.le (cuts_le y x hx i)
  · have hz : y i=0 := le_antisymm (le_of_not_gt h) (hy i)
    have he : cuts y x i=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hle := cuts_le y x hx i q hq
      have hp := cuts_pos y x i q hq
      linarith only [hle,hp,hz]
    rw [sum_coe_sort,he,sum_empty,hz]

theorem sum_weight_nonneg (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hy : ∀ i, 0≤y i) (hx : ∀ c i, x c i≤y i) :
    (∑ a, weight y x a)=∑ i, y i := by
  rw [Fintype.sum_sigma]
  exact sum_congr rfl (fun i _ => sum_fiber_nonneg y x hy hx i)

def count (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) := ∑ i, (cuts y x i).card

def index (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    Fin (count y x) ≃ Piece y x :=
  finSigmaFinEquiv.symm.trans (Equiv.sigmaCongrRight (fun i => (cuts y x i).orderIsoOfFin rfl |>.toEquiv))

def weights (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (a : Fin (count y x)) : ℚ :=
  weight y x (index y x a)

def original (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (a : Fin (count y x)) : Fin f :=
  (index y x a).1

def assigned (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (c : Fin j) : Finset (Fin (count y x)) :=
  (assignment y x c).map (index y x).symm.toEmbedding

theorem count_le (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) : count y x ≤ f*(j+1) := by
  have he : count y x=Fintype.card (Piece y x) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe,count]
  rw [he]
  simpa only [Fintype.card_fin] using card_pieces y x

theorem mem_assigned (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (c : Fin j) (a : Fin (count y x)) : a∈assigned y x c ↔ index y x a∈assignment y x c := by
  simp only [assigned,mem_map,Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨b,hb,hba⟩
    rw [← hba,(index y x).apply_symm_apply]
    exact hb
  · intro ha
    exact ⟨index y x a,ha,(index y x).symm_apply_apply a⟩

theorem assigned_sum {K : Type} [AddCommMonoid K]
    (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (c : Fin j) (v : Piece y x → K) :
    (∑ a ∈ assigned y x c, v (index y x a))=∑ a ∈ assignment y x c, v a := by
  rw [assigned,sum_map]
  simp only [Equiv.toEmbedding_apply,Equiv.apply_symm_apply]

theorem weights_sum (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hy : ∀ i, 0≤y i) (hx : ∀ c i, x c i≤y i) :
    (∑ a, weights y x a)=∑ i, y i :=
  ((index y x).sum_comp (weight y x)).trans (sum_weight_nonneg y x hy hx)

end MetricKMedian.Preparation.RationalSplitting
end

end OAI
