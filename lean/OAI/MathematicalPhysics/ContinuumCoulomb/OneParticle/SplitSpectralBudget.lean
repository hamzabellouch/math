import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitProjectionBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalCappedGap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellLocalization

namespace OAI

/-! Combining the actual planar and transverse form estimates. The
projection budget removes the planar penalty from transverse excitations. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def splitPlanarForm {m : ℕ} (u : Fin m → PlanarPosition) (f : SplitPosition → ℝ) : ℝ :=
  ∫ z, planarTestForm (planarWellSum u) (fun r => f (r,z))

def splitVerticalForm (freq S : ℝ) (f : SplitPosition → ℝ) : ℝ :=
  ∫ r : PlanarPosition, verticalCappedForm freq S (fun z => f (r,z))

theorem split_form_projection_lower {freq D S Ep Ev a b : ℝ}
    (hfreq : 0 < freq) (ha : 0 ≤ a)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hdominate : a*(1+m*localizedOverlapBound D) ≤ b)
    (f : SplitPosition → ℝ) (hf : MemLp f 2)
    (hp : Ep*(∫ p, f p^2)-a*(∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤
      splitPlanarForm u f)
    (hv : Ev*(∫ p, f p^2)-b*(∫ r, (verticalCoefficient freq f r)^2) ≤
      splitVerticalForm freq S f) :
    (Ep+Ev-b)*(∫ p, f p^2)-a*(∑ i, (∫ p, f p*localizedMode freq (u i) p)^2) ≤
      splitPlanarForm u f+splitVerticalForm freq S f := by
  let M := ∫ p, f p^2
  let Z := ∫ r, (verticalCoefficient freq f r)^2
  let P := ∫ z, ∑ i, (planarCoefficient (u i) f z)^2
  let T := ∑ i, (∫ p, f p*localizedMode freq (u i) p)^2
  let C := 1+m*localizedOverlapBound D
  have hZ : Z ≤ M := (verticalCoefficient_contraction hfreq f hf).2
  have hP : P ≤ C*(M-Z)+T := split_projection_budget hfreq u hsep f hf
  have hpen : a*P+b*Z ≤ b*M+a*T := by
    calc
      a*P+b*Z ≤ a*(C*(M-Z)+T)+b*Z :=
        add_le_add (mul_le_mul_of_nonneg_left hP ha) le_rfl
      _ = a*C*M+(b-a*C)*Z+a*T := by ring
      _ ≤ a*C*M+(b-a*C)*M+a*T :=
        add_le_add (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hZ (sub_nonneg.mpr hdominate))) le_rfl
      _ = b*M+a*T := by ring
  change (Ep+Ev-b)*M-a*T ≤ _
  change Ep*M-a*P ≤ _ at hp
  change Ev*M-b*Z ≤ _ at hv
  nlinarith

end ContinuumCoulomb

end

end OAI
