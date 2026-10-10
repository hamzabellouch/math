import OAI.Geometry.CylinderCovering.Footprints.Footprints
import OAI.Geometry.CylinderCovering.Footprints.Area

namespace OAI

namespace CylinderCovering.Footprints

theorem absoluteFootprint_eq_radial (m M d A B : ℝ) :
    absoluteFootprint m M d A B = RadialFootprints.absoluteFootprint A B M d m := by
  ext p
  simp only [absoluteFootprint, RadialFootprints.absoluteFootprint,
    Set.mem_ofPred_eq, Set.mem_Icc]
  tauto

theorem affineFootprint_eq_radial (c M d A B : ℝ) :
    affineFootprint c M d A B = RadialFootprints.affineFootprint A B M d c := by
  ext p
  simp only [affineFootprint, RadialFootprints.affineFootprint,
    Set.mem_ofPred_eq, Set.mem_Icc]
  tauto

end CylinderCovering.Footprints

namespace RadialFootprints
open CylinderCovering.Footprints

theorem quadratic_mem_absolute {ε x q c ρ m M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d) (hqm : |q - m| ≤ d / 2)
    (hρ : 0 ≤ ρ) (hρM : ρ ≤ M) (hA : 2 * ε ≤ A) (hB : ε ≤ B) :
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint A B M d m := by
  rw [← CylinderCovering.Footprints.absoluteFootprint_eq_radial]
  exact CylinderCovering.Footprints.quadratic_mem_absolute hε hd hx hqc hqm hρ hρM hA hB

theorem quadratic_mem_affine_midpoint {ε x q c ρ M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d / 2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hA : ε ≤ A) (hB : 3 * ε / 4 ≤ B) :
    quadraticIntercept ε x q c ρ ∈ affineFootprint A B M d c := by
  rw [← CylinderCovering.Footprints.affineFootprint_eq_radial]
  exact CylinderCovering.Footprints.quadratic_mem_affine_midpoint hε hd hx hqc hρ hρM hA hB

end RadialFootprints

end OAI
