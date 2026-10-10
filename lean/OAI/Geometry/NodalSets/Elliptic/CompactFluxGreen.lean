import OAI.Geometry.NodalSets.Elliptic.CompactWeightedWeakEquation

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem weightedDiv_hasCompactSupport (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i)) :
    HasCompactSupport (weightedDiv gamma V) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun i _ ↦ ((hc i).mul_left (f := gamma)).fderiv_apply ℝ (Pi.single i 1))
  convert h.mul_left (f := fun x ↦ (gamma x)⁻¹) using 1
  first | rfl | (ext x; simp only [weightedDiv,coordDiv,coordPartial,Pi.mul_apply,Finset.sum_apply]; rfl)

theorem compact_flux_weighted_integration_by_parts (gamma phi : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*pairing phi V x) = -(∫ x, gamma x*phi x*weightedDiv gamma V x) := by
  have hp : HasCompactSupport (pairing phi V) := by
    unfold pairing
    have h := HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ ↦ (hc i).mul_left (f := fun x ↦ coordPartial phi x i))
    convert h using 1
    first | rfl | (ext x; simp only [Finset.sum_apply,Pi.mul_apply])
  have hiP : Integrable (fun x ↦ gamma x*pairing phi V x) :=
    (hg.mul (pairing_smooth hphi hV)).continuous.integrable_of_hasCompactSupport hp.mul_left
  have hiD : Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) :=
    ((hg.mul hphi).mul (weightedDiv_smooth hg hgn hV)).continuous.integrable_of_hasCompactSupport
      (weightedDiv_hasCompactSupport gamma V hc).mul_left
  obtain ⟨_,hz⟩ := integral_weightedDiv_compact_zero gamma hg hgn
    (fun x i ↦ phi x*V x i) (fun i ↦ hphi.mul (hV i)) (fun i ↦ (hc i).mul_left)
  have he : (fun x ↦ gamma x*weightedDiv gamma (fun y i ↦ phi y*V y i) x) =
      (fun x ↦ gamma x*phi x*weightedDiv gamma V x + gamma x*pairing phi V x) := by
    funext x
    rw [weightedDiv_mul (hg.differentiable (by simp) x) (hgn x)
      (hphi.differentiable (by simp) x) (fun i ↦ (hV i).differentiable (by simp) x)]
    ring
  rw [he,integral_add hiD hiP] at hz
  exact ⟨hiP,hiD,by linarith⟩

end
end Yau

end OAI
