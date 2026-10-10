import OAI.Geometry.NodalSets.Elliptic.CompactWeightedDivergenceIntegral
import OAI.Geometry.NodalSets.Elliptic.RealCoordinateEllipticLemmas

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem compact_weighted_integration_by_parts (gamma phi : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*pairing phi V x) = -(∫ x, gamma x*phi x*weightedDiv gamma V x) := by
  have hp : HasCompactSupport (pairing phi V) := by
    unfold pairing
    have h := HasCompactSupport.finset_sum
      (s := Finset.univ) (fun i _ ↦ (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right
        (f' := fun x ↦ V x i))
    convert h using 1; first | rfl | (ext x; simp [coordPartial])
  have hiP : Integrable (fun x ↦ gamma x*pairing phi V x) :=
    (hg.mul (pairing_smooth hphi hV)).continuous.integrable_of_hasCompactSupport hp.mul_left
  have hiD : Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) :=
    ((hg.mul hphi).mul (weightedDiv_smooth hg hgn hV)).continuous.integrable_of_hasCompactSupport
      hc.mul_left.mul_right
  obtain ⟨_,hz⟩ := integral_weightedDiv_compact_zero gamma hg hgn
    (fun x i ↦ phi x*V x i) (fun i ↦ hphi.mul (hV i)) (fun _ ↦ hc.mul_right)
  have he : (fun x ↦ gamma x*weightedDiv gamma (fun y i ↦ phi y*V y i) x) =
      (fun x ↦ gamma x*phi x*weightedDiv gamma V x + gamma x*pairing phi V x) := by
    funext x
    rw [weightedDiv_mul (hg.differentiable (by simp) x) (hgn x)
      (hphi.differentiable (by simp) x) (fun i ↦ (hV i).differentiable (by simp) x)]
    ring
  rw [he,integral_add hiD hiP] at hz
  exact ⟨hiP,hiD,by linarith⟩

theorem compact_weighted_weak_equation (gamma phi f : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (he : ∀ x, weightedDiv gamma V x + f x = 0) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*f x) ∧
    (∫ x, gamma x*pairing phi V x) = ∫ x, gamma x*phi x*f x := by
  obtain ⟨hiP,hiD,hid⟩ := compact_weighted_integration_by_parts gamma phi hg hgn hphi hc V hV
  have heq : (fun x ↦ gamma x*phi x*f x) =
      -(fun x ↦ gamma x*phi x*weightedDiv gamma V x) := by
    funext x
    have hx := he x
    simp only [Pi.neg_apply]
    rw [show f x = -weightedDiv gamma V x by linarith]
    ring
  rw [heq]
  refine ⟨hiP,hiD.neg,?_⟩
  change (∫ x, gamma x*pairing phi V x) = ∫ x, -(gamma x*phi x*weightedDiv gamma V x)
  rw [integral_neg]
  exact hid

end
end Yau

end OAI
