import OAI.MeasureTheory.Falconer.Angular.MixedCapBounds
import OAI.MeasureTheory.Falconer.Angular.CapDenominator

namespace OAI

/-! # Full ambient derivative bounds for the cap denominator

At a point of the sphere, only the bounded number of nearby centers can
contribute. The estimate applies to the full multilinear derivative.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capDenominator_ambient_derivatives (d k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ w : Sphere d,
      ‖iteratedFDeriv ℝ k (capDenominator δ hδ S) w‖ ≤ B*(δ⁻¹)^k := by
  classical
  obtain ⟨C,hC,hCb⟩ := capBump_ambient_derivatives d k
  refine ⟨5^d*C, by positivity, ?_⟩
  intro δ hδ S hsep w
  let T := S.filter (fun c => dist w c ≤ δ)
  let f := fun c : Sphere d => iteratedFDeriv ℝ k (capBump δ hδ c) (w : Space d)
  have hzero (c : Sphere d) (hc : c ∈ S) (hct : c ∉ T) : f c = 0 := by
    have hd : δ < dist w c :=
      lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact capBump_ambient_derivative_zero hδ c w (by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hd) k
  have hsum : (∑ c ∈ S, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change ‖iteratedFDeriv ℝ k (fun x => ∑ c ∈ S, capBump δ hδ c x) w‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply (n := k)
    (fun c _ => ((capBump δ hδ c).contDiff (n := (k : ℕ∞))).contDiffAt)]
  change ‖∑ c ∈ S, f c‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, ‖f c‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^k := Finset.sum_le_sum (fun c _ => hCb δ hδ c w)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^k) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^d*(C*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right
      (separated_sphere_overlap S hδ hsep w) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
