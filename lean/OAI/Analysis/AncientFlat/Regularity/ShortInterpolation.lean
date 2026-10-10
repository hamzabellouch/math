import OAI.Analysis.AncientFlat.Evolution.ShortWithin
import OAI.Analysis.AncientFlat.Spectral.ShortPowers
import OAI.Analysis.AncientFlat.Regularity.ShortHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicShort
open ParabolicInterior ParabolicInitial
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
theorem lower_small (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ C : ℝ, 0<C ∧ ∀ h M : ℝ, 0<h → h≤1 → 0≤M → ∀ (u ut : ℝ → V → E),
      (∀ t∈Icc 0 h, ContDiff ℝ 4 (u t)) →
      (∀ p∈slab 2 h, HasDerivWithinAt (fun t => u t p.1) (ut p.2 p.1) (Icc 0 h) p.2) →
      (∀ x : V, ‖x‖<2 → u 0 x=0) →
      (∀ p∈slab 2 h, ‖ut p.2 p.1‖≤M) →
      (∀ p∈slab 2 h, ‖iteratedFDeriv ℝ 4 (u p.2) p.1‖≤M) →
      ∀ j : ℕ, j≤3 → HolderBound α (slab 1 h)
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (C*h^((4-(j:ℝ)-α)/4)*M) := by
  refine ⟨110*(24^4+1),by norm_num,?_⟩
  intro h M hh hh1 hM u ut hs hd hu0 hut hD j hj
  let d := h^((1:ℝ)/4)
  let q := d/24
  have hd0 : 0<d := Real.rpow_pos_of_pos hh _
  have hd1 : d≤1 := Real.rpow_le_one hh.le hh1 (by norm_num)
  have hq : 0<q := by dsimp [q]; positivity
  have hq1 : q≤1 := by dsimp [q]; linarith
  have hgap : 1+12*q≤2 := by dsimp [q]; linarith
  exact (short_explicit j hj h q M α hh hq hq1 hgap hM hα.le hα1.le u ut hs hd hu0 hut hD).mono
    (short_scale_bound j hj h M α hh hM hα1)
end ParabolicShort

end

end OAI
