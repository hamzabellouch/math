import OAI.Analysis.Pureness.Divisibility.Hereditary
import OAI.Analysis.Pureness.Cuntz.CStarCuntz

namespace OAI
namespace CuntzPureness
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem hereditary_cuntzSubequiv (h c : A) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (hcm : c ∈ hereditaryCarrier h) : CuntzSubequiv c h := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hereditary_sqrt_mem hh hc hcm)
  have hs := (hlim.star.mul hlim)
  rw [(CFC.sqrt_nonneg c).star_eq, CFC.sqrt_mul_sqrt_self c hc] at hs
  apply cuntzSubequiv_of_tendsto (a := fun j => star (u j) * u j) _ hs
  intro j
  obtain ⟨w, hw⟩ := hu j
  rw [← hw]
  have hsquare : CFC.sqrt h * h * CFC.sqrt h = h * h := by
    calc
      _ = CFC.sqrt h * (CFC.sqrt h * CFC.sqrt h) * CFC.sqrt h := by
        rw [CFC.sqrt_mul_sqrt_self h hh]
      _ = (CFC.sqrt h * CFC.sqrt h) * (CFC.sqrt h * CFC.sqrt h) := by
        noncomm_ring
      _ = h * h := by rw [CFC.sqrt_mul_sqrt_self h hh]
  have heq : star (h * w * h) * (h * w * h) =
      star (CFC.sqrt h * w * h) * h * (CFC.sqrt h * w * h) := by
    simp only [star_mul, hh.star_eq, (CFC.sqrt_nonneg h).star_eq]
    calc
      _ = h * star w * (h * h) * w * h := by simp only [mul_assoc]
      _ = h * star w * (CFC.sqrt h * h * CFC.sqrt h) * w * h := by rw [hsquare]
      _ = _ := by simp only [mul_assoc]
  rw [heq]
  exact cuntzSubequiv_conjugate _ _
end CuntzPureness

end OAI
