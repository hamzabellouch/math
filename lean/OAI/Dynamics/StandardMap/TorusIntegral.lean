import OAI.Dynamics.StandardMap.ActualBackwardCarry

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def liftProjection (z : ℝ × ℝ) : Torus := ((z.1 : Circle),(z.2 : Circle))

lemma unit_cell_integral (g : Torus → ℝ≥0∞) (hg : Measurable g) (a b : ℝ) :
    (∫⁻ z in Ioc a (a+1) ×ˢ Ioc b (b+1), g (liftProjection z)) = ∫⁻ z, g z ∂area := by
  have h := (AddCircle.measurePreserving_mk (1:ℝ) a).prod (AddCircle.measurePreserving_mk (1:ℝ) b)
  rw [Measure.prod_restrict] at h
  exact h.lintegral_comp hg

lemma interval_four_cell_cover (x : ℝ) (hx : x ∈ Ioc (-2:ℝ) 2) :
    ∃ j : Fin 4, x ∈ Ioc ((j:ℝ)-2) ((j:ℝ)-2+1) := by
  by_cases h1 : x ≤ -1
  · exact ⟨0,by norm_num at *; exact ⟨hx.1,h1⟩⟩
  by_cases h2 : x ≤ 0
  · exact ⟨1,by norm_num at *; exact ⟨by linarith,h2⟩⟩
  by_cases h3 : x ≤ 1
  · exact ⟨2,by norm_num at *; exact ⟨by linarith,h3⟩⟩
  · exact ⟨3,by norm_num at *; exact ⟨by linarith,hx.2⟩⟩

lemma bounded_lift_integral (g : Torus → ℝ≥0∞) (hg : Measurable g)
    (S : Set (ℝ × ℝ)) (hS : S ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2) :
    (∫⁻ z in S, g (liftProjection z)) ≤ 16*(∫⁻ z, g z ∂area) := by
  let cell : (Fin 4 × Fin 4) → Set (ℝ × ℝ) := fun j =>
    Ioc ((j.1:ℝ)-2) ((j.1:ℝ)-2+1) ×ˢ Ioc ((j.2:ℝ)-2) ((j.2:ℝ)-2+1)
  have hcover : S ⊆ ⋃ j, cell j := by
    intro z hz
    obtain ⟨i,hi⟩ := interval_four_cell_cover z.1 (hS hz).1
    obtain ⟨j,hj⟩ := interval_four_cell_cover z.2 (hS hz).2
    exact mem_iUnion.mpr ⟨(i,j),hi,hj⟩
  calc
    _ ≤ ∫⁻ z in ⋃ j, cell j, g (liftProjection z) := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ z in cell j, g (liftProjection z) := lintegral_iUnion_le _ _
    _ = _ := by simp only [cell,unit_cell_integral g hg,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]; norm_num
end StandardMapEntropy

end OAI
