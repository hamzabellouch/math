import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannFermions

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannCounts_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

open CoulombAtom
variable {N : ℕ} {C : Type*} [DecidableEq C]

lemma sum_cellCount (c : Fin N → C) :
    ∑ a ∈ Finset.univ.image c, cellCount c a = N := by
  classical
  have hc (a : C) : cellCount c a = ∑ i ∈ Finset.univ.filter (fun i => c i=a), (1:ℕ) := by simp [cellCount]
  simp_rw [hc]
  rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i))]
  simp

lemma cellCount_le (c : Fin N → C) (a : C) : cellCount c a ≤ N := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin N)

lemma sum_cell_boundary (c : Fin N → C) :
    ∑ a ∈ Finset.univ.image c, ((cellCount c a:ℝ)^(4/3:ℝ)+(cellCount c a:ℝ)) ≤
      (N:ℝ)^(4/3:ℝ)+(N:ℝ) := by
  have hp (x : ℝ) (hx : 0 ≤ x) : x^(4/3:ℝ) = x*x^(1/3:ℝ) := by
    rw [show (4/3:ℝ) = 1+(1/3:ℝ) by norm_num,Real.rpow_add' hx (by norm_num)]
    rw [Real.rpow_one]
  have hn : (∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)) = N := by
    exact_mod_cast sum_cellCount c
  calc
    _ ≤ ∑ a ∈ Finset.univ.image c, ((cellCount c a:ℝ)*(N:ℝ)^(1/3:ℝ)+(cellCount c a:ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [hp _ (Nat.cast_nonneg _)]
      have hle : (cellCount c a:ℝ) ≤ (N:ℝ) := by exact_mod_cast cellCount_le c a
      have hr := Real.rpow_le_rpow (Nat.cast_nonneg (cellCount c a)) hle (by norm_num : 0 ≤ (1/3:ℝ))
      have hm := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (cellCount c a))
      linarith
    _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,hn,hp _ (Nat.cast_nonneg N)]

lemma cellLowerEnergy_bound (c : Fin N → C) :
    tfKinetic*(∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)^(5/3:ℝ)) -
      neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) ≤ cellLowerEnergy c := by
  unfold cellLowerEnergy neumannLowerEnergy
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left (sum_cell_boundary c)
    neumannRemainderConstant_pos.le) _

lemma selected_cell_pressure_le (c : Fin N → C) (S : Finset (Fin N)) :
    (∑ a ∈ Finset.univ.image c,
      ((S.filter (fun i => c i=a)).card:ℝ)^(5/3:ℝ)) ≤
      ∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)^(5/3:ℝ) := by
  apply Finset.sum_le_sum
  intro a _
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter (fun i => c i=a) (Finset.subset_univ S))
  · norm_num

theorem neumann_cells_pressure_lower (c : Fin N → C)
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hanti : CellAntisymmetric c (fun s => finiteCubeFunction (hf s)))
    (s : Fin N → Fin 2) :
    tfKinetic*(∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)^(5/3:ℝ)) *
        (∫ x, ‖finiteCubeFunction (hf s) x‖^2) ≤
      (1/2:ℝ)*(∑ i, ∫ x, ‖finiteCubeGradient (hf s) i x‖^2) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) *
          (∫ x, ‖finiteCubeFunction (hf s) x‖^2) := by
  have hb := mul_le_mul_of_nonneg_right (cellLowerEnergy_bound c)
    (integral_nonneg (μ := volume) (fun x => sq_nonneg ‖finiteCubeFunction (hf s) x‖))
  have hl := neumann_cell_component_lower c hf hanti s
  nlinarith

end Work_NeumannCounts_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

open CoulombAtom
variable {N : ℕ} {C : Type*} [DecidableEq C]

def cellPressure (c : Fin N → C) : ℝ := ∑ i, (cellCount c (c i):ℝ)^(2/3:ℝ)

lemma cellPressure_eq (c : Fin N → C) :
    cellPressure c = ∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)^(5/3:ℝ) := by
  classical
  unfold cellPressure
  rw [←Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.univ.image c)
    (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i))]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => c i=a), (cellCount c a:ℝ)^(2/3:ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = (cellCount c a:ℝ)*(cellCount c a:ℝ)^(2/3:ℝ) := by simp [cellCount]
    _ = _ := by
      rw [show (5/3:ℝ)=1+(2/3:ℝ) by norm_num,
        Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),Real.rpow_one]

lemma cellPressure_nonneg (c : Fin N → C) : 0 ≤ cellPressure c :=
  Finset.sum_nonneg (fun _i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma cellPressure_le (c : Fin N → C) : cellPressure c ≤ (N:ℝ)^(5/3:ℝ) := by
  calc
    _ ≤ ∑ i : Fin N, (N:ℝ)^(2/3:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast cellCount_le c (c i)) (by norm_num)
    _ = (N:ℝ)*(N:ℝ)^(2/3:ℝ) := by simp
    _ = _ := by
      rw [show (5/3:ℝ)=1+(2/3:ℝ) by norm_num,
        Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),Real.rpow_one]

def pointCell (x : (Fin N × Fin 3) → ℝ) (i : Fin N) : Fin 3 → ℤ := fun a => ⌊x (i,a)⌋
def indexCell (z : (Fin N × Fin 3) → ℤ) (i : Fin N) : Fin 3 → ℤ := fun a => z (i,a)

lemma pointCell_measurable : Measurable (pointCell (N := N)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro a
  exact Int.measurable_floor.comp (measurable_pi_apply (i,a))

lemma flatPressure_measurable : Measurable (fun x : (Fin N × Fin 3) → ℝ => cellPressure (pointCell x)) :=
  (measurable_of_countable (fun c : Fin N → Fin 3 → ℤ => cellPressure c)).comp pointCell_measurable

lemma pointCell_of_mem_floorCube {z : (Fin N × Fin 3) → ℤ} {x : (Fin N × Fin 3) → ℝ}
    (hx : x ∈ floorCube z) : pointCell x = indexCell z := by
  ext i a
  exact hx (i,a)

lemma flatPressure_integrable {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : MemLp f 2) :
    Integrable (fun x => cellPressure (pointCell x)*‖f x‖^2) := by
  apply hf.norm.integrable_sq.bdd_mul flatPressure_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (cellPressure_nonneg _)]
    exact cellPressure_le _)

lemma integral_floorCube_pressure (z : (Fin N × Fin 3) → ℤ)
    (f : ((Fin N × Fin 3) → ℝ) → ℂ) :
    (∫ x in floorCube z, cellPressure (pointCell x)*‖f x‖^2) =
      cellPressure (indexCell z)*(∫ x in floorCube z, ‖f x‖^2) := by
  rw [←integral_const_mul]
  apply setIntegral_congr_fun (floorCube_measurable z)
  intro x hx
  simp only [pointCell_of_mem_floorCube hx]

end CoulombNeumann

end

end OAI
