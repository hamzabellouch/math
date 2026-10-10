import Mathlib
import OAI.Analysis.HardSphere.FormDomain.Energy

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

lemma energy_parallelogram (u v : H × (J → H)) :
    energy (u + v) + energy (u - v) = 2 * (energy u + energy v) := by
  change (∑ i, ‖u.2 i + v.2 i‖ ^ 2) + (∑ i, ‖u.2 i - v.2 i‖ ^ 2) = _
  rw [← Finset.sum_add_distrib]
  simp_rw [parallelogram_law_with_norm ℂ]
  simp only [energy, Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem minimizer_eq_of_scalar_eq (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) (hscalar : v.1 = u.1)
    (henergy : energy v ≤ energy u) : v = u := by
  have hnormsum : ‖(u + v).1‖ ^ 2 = 4 := by
    have he : (u + v).1 = (2 : ℂ) • u.1 := by simp [hscalar, two_smul]
    rw [he, norm_smul, hnorm]
    norm_num
  have hr := rayleigh M u hmin (u + v) (M.add_mem hu hv)
  rw [hnormsum] at hr
  have hd : energy (u - v) = 0 := by
    have hp := energy_parallelogram u v
    have hn := energy_nonneg (u - v)
    linarith
  apply Prod.ext hscalar
  funext i
  have hi : ‖u.2 i - v.2 i‖ ^ 2 ≤ energy (u - v) :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖u.2 j - v.2 j‖) (Finset.mem_univ i)
  rw [hd] at hi
  have hz : ‖u.2 i - v.2 i‖ = 0 := by nlinarith [norm_nonneg (u.2 i - v.2 i)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end HardSphere.Variational

end
end
end
end

end OAI
