import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.FiniteBallChartUnion

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem finiteBallChartUnionConstant_mono (d : ℕ) {N K : ℕ} (hNK : N ≤ K)
    {M L : ℝ≥0} (hML : M ≤ L) :
    finiteBallChartUnionConstant d N M ≤ finiteBallChartUnionConstant d K L := by
  have hNK' : (N : ℝ≥0) ≤ (K : ℝ≥0) := by exact_mod_cast hNK
  unfold finiteBallChartUnionConstant separatedPatchGluingConstant finiteChartPackingFactor
  gcongr

theorem exists_ball_lipschitz_cover_of_bounded_finite_family {n d : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (N : ℕ) (hN : Fintype.card ι ≤ N)
    (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (f : ι → ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i))
    (himage : ∀ i, Set.range (f i) ⊆ closedBall z (3 * r)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N M) g ∧
      (⋃ i : ι, Set.range (f i)) ⊆ Set.range g := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_cover_of_finite_ball_charts hn
    (Fintype.card ι) r hr z (fun j => f (e j)) M (fun j => hLip (e j)) (fun j => himage (e j))
  refine ⟨g, hg.weaken (finiteBallChartUnionConstant_mono d hN le_rfl), ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  apply hcover
  apply mem_iUnion.mpr
  exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using! hi⟩

end

end RieszRectifiability

end OAI
