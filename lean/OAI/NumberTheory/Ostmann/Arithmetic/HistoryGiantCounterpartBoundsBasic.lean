import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinatesBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedSample

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCounterpartBounds
open Construction HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairGiantCoordinates HistoryActiveCoordinates HistoryPairSmoothXi
open scoped Classical
variable {l : ℕ}

theorem role_endpoint (h g : History l) (pred : SmallSlot→Bool) (t : ℝ) :
    keyLogEndpoint (giantCoordinates h g) (pairBackground h g) (fun _ => t)
      ((diagonalRoleKeys g pred).map (rightMap h g)) =
    ((diagonalRoleKeys g pred).map (fun i => Real.log (integerSample g i:ℝ))).sum := by
  unfold keyLogEndpoint diagonalRoleKeys
  simp only [List.map_map,Function.comp_def]
  congr 1

theorem H_endpoint (h g : History l) (j : ℕ) (t : ℝ) :
    keyLogEndpoint (giantCoordinates h g) (pairBackground h g) (fun _ => t)
      (pairedDiagonalHKeys h g j) = t+
    ((diagonalRoleKeys g (fun q => decide (q.role≠.compensation j))).map
      (fun i => Real.log (integerSample g i:ℝ))).sum := by
  simp only [pairedDiagonalHKeys,diagonalHKeys,List.map_cons,keyLogEndpoint,List.sum_cons]
  change logInsert (giantCoordinates h g) (pairBackground h g) (fun _ => t)
    (rightMap h g (.inl true)) +
    keyLogEndpoint (giantCoordinates h g) (pairBackground h g) (fun _ => t)
      ((diagonalRoleKeys g _).map (rightMap h g)) = _
  rw [role_endpoint,← shared_giant h g true]
  simp only [logInsert,dite_eq_left (giant_mem h g true)]

theorem U_endpoint (h g : History l) (j : ℕ) (t : ℝ) :
    keyLogEndpoint (giantCoordinates h g) (pairBackground h g) (fun _ => t)
      (pairedDiagonalUKeys h g j) =
    ((diagonalUKeys g j).map (fun i => Real.log (integerSample g i:ℝ))).sum :=
  role_endpoint h g _ t

lemma root_small_positive (g : History l) (hg : g.root.Positive) (q : SmallSlot)
    (hq : q∈g.root.small) : 0 < q.value :=
  hg q.value (by simp only [State.values,List.mem_cons]; exact Or.inr (Or.inr (List.mem_map.mpr ⟨q,hq,rfl⟩)))

lemma roleKeys_sample_ne_zero (g : History l) (hg : g.root.Positive) (pred : SmallSlot→Bool)
    (i : Key g) (hi : i∈diagonalRoleKeys g pred) : (integerSample g i:ℝ)≠0 := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
  have hpos := root_small_positive g hg (g.root.small.get a) (List.get_mem _ _)
  change ((g.root.small.get a).value:ℝ)≠0
  exact_mod_cast hpos.ne'

theorem H_endpoint_log_product (h g : History l) (hg : g.root.Positive) (j : ℕ) (t : ℝ) :
    keyLogEndpoint (giantCoordinates h g) (pairBackground h g) (fun _ => t)
      (pairedDiagonalHKeys h g j) =
      Real.log (((diagonalHKeys g j).map (fun i => (integerSample g i:ℝ))).prod)+
        t-Real.log (g.root.giantMinus:ℝ) := by
  have hm : (g.root.giantMinus:ℝ)≠0 := by
    have hh := hg g.root.giantMinus (by simp [State.values])
    exact_mod_cast hh.ne'
  rw [H_endpoint]
  simp only [diagonalHKeys,List.map_cons,List.prod_cons,integerSample,Int.cast_natCast]
  rw [Real.log_mul hm]
  · rw [Real.log_list_prod]
    · simp only [List.map_map,Function.comp_def]
      ring
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact roleKeys_sample_ne_zero g hg _ i hi
  · apply List.prod_ne_zero
    intro hx
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hx
    exact roleKeys_sample_ne_zero g hg _ i hi he

theorem U_endpoint_log_product (h g : History l) (hg : g.root.Positive) (j : ℕ) (t : ℝ) :
    keyLogEndpoint (giantCoordinates h g) (pairBackground h g) (fun _ => t)
      (pairedDiagonalUKeys h g j) =
      Real.log (((diagonalUKeys g j).map (fun i => (integerSample g i:ℝ))).prod) := by
  rw [U_endpoint,Real.log_list_prod]
  · simp only [List.map_map,Function.comp_def]
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact roleKeys_sample_ne_zero g hg _ i hi

end Ostmann.Arithmetic.HistoryGiantCounterpartBounds

end

end OAI
