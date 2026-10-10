import OAI.Geometry.HeilbronnTriangle.FixedDetLattice
import OAI.Geometry.HeilbronnTriangle.IntegralAmbientLattice

namespace OAI


noncomputable section
namespace Problem355.FullIntegralLattice
open IntegralPlaneLattice

theorem fixed_det_count
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (X : ℝ) (hX : 1 ≤ X) (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 := by
  let := realLattice_isZLattice L m hm hL
  have h := FixedDetLattice.integer_fixed_det_count a ha hanis (realLattice L)
    (one_le_norm_of_mem_realLattice L) X hX S
    (fun A hA i => ⟨A i, hrows A hA i, rfl⟩) hnorm t ht hdet
  rw [realLattice_covolume L m hm hL] at h
  exact h

end Problem355.FullIntegralLattice

end

end OAI
