import OAI.Analysis.LipschitzHilbert.Estimates.ColoredPlanarEnergy

namespace OAI

/-! Finite Hilbert-valued version of the residue-coloring energy bound.
The number of coordinates contributes no factor. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

theorem planar_colored_vector_energy {ι κ : Type*} [Fintype ι] [Fintype κ] {q : ℕ}
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (color : ι → Fin q) (slope : ℝ)
    (hdisjoint : ∀ k y ξ i j, i ≠ j → color i = color j →
      𝓕 (planarSchwartzSlice (f i k) y slope) ξ = 0 ∨
        𝓕 (planarSchwartzSlice (f j k) y slope) ξ = 0) :
    (∫ z, ‖∑ i, (WithLp.toLp 2 (fun k => f i k z) : EuclideanSpace ℂ κ)‖^2
      ∂volume.prod volume) ≤
      (q:ℝ)*∑ i, ∫ z, ‖(WithLp.toLp 2 (fun k => f i k z) : EuclideanSpace ℂ κ)‖^2
        ∂volume.prod volume := by
  simp only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_sum,Finset.sum_apply]
  have hs (k : κ) : Integrable (fun z => ‖∑ i, f i k z‖^2) (volume.prod volume) := by
    let F : SchwartzMap (ℝ×ℝ) ℂ := ∑ i, f i k
    have heq (z : ℝ×ℝ) : F z = ∑ i, f i k z := by simp [F]
    simpa only [heq] using (F.memLp 2 (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0)
  rw [integral_finsetSum _ (fun k _ => hs k)]
  calc
    _ ≤ ∑ k, (q:ℝ)*∑ i, ∫ z, ‖f i k z‖^2 ∂volume.prod volume :=
      Finset.sum_le_sum (fun k _ => planar_colored_energy (fun i => f i k) color slope (hdisjoint k))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun k _ =>
        ((f i k).memLp 2 (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0))).symm

end LipschitzHilbert

end

end OAI
