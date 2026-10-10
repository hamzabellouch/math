import OAI.MeasureTheory.Falconer.Shells.FiniteWeightedShell
import Mathlib.Data.List.OfFn

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem list_weighted_shell_square {ι : Type*} (L : List ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ L, 0 ≤ w i)
    (hi : ∀ i ∈ L, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ L, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ L, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖(L.map (fun i => F i r)).sum‖^2 ∂μ) ≤ (L.map w).sum^2*B := by
  have hh := finite_weighted_shell_square (Finset.univ : Finset (Fin L.length)) μ
    (fun i => F L[i]) (fun i => w L[i])
    (fun i _ => hw _ (List.getElem_mem i.isLt))
    (fun i _ => hi _ (List.getElem_mem i.isLt))
    (fun i _ => hm _ (List.getElem_mem i.isLt))
    (fun i _ => hB _ (List.getElem_mem i.isLt))
  have he (f : ι → ℂ) : (∑ i : Fin L.length, f L[i]) = (L.map f).sum := by
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map L f
  have hw' : (∑ i : Fin L.length, w L[i]) = (L.map w).sum := by
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map L w
  simp_rw [show ∀ r, (∑ i : Fin L.length, F L[i] r) =
    (L.map (fun i => F i r)).sum from fun r => he (fun i => F i r),hw'] at hh
  exact hh

end PlanarFalconer

end OAI
