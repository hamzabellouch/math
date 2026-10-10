import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadPrefixBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanIteration

namespace OAI

/-! Polynomial local jet profiles obtained from the fixed atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_plane_read_profiles (P : ℕ → ℝ → ℝ)
    (hP : ∀ m, HasPolynomialBound (P m)) :
    ∃ J : ℕ → ℝ → ℝ, (∀ m, HasPolynomialBound (J m)) ∧
      (∀ m x, 1 ≤ x → 1 ≤ J m x) ∧
    ∀ x : ℝ, 1 ≤ x → ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ s : ℝ, 0 < s → s ≤ 1 → (∀ m, A.ShiftedBound 2 m s (P m x) G) →
    ∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
      (J m x/s^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i G) := by
  classical
  choose D hD hd using fun (i : A.centers) m =>
    A.vectorPlaneRead_prefix_bounds (V := Space) i 2 (m+1)
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  let J := fun m x => 1+∑ i : A.centers, L*D i m*P (m+1) x
  have hterms (m : ℕ) (x : ℝ) (hx : 1 ≤ x) (i : A.centers) :
      0 ≤ L*D i m*P (m+1) x := mul_nonneg (mul_nonneg hL (hD i m)) ((hP _).nonneg hx)
  refine ⟨J,?_,?_,?_⟩
  · intro m
    exact (polynomialBound_const zero_le_one).add
      (HasPolynomialBound.sum Finset.univ (fun i x => L*D i m*P (m+1) x)
        (fun i _ => (polynomialBound_const (mul_nonneg hL (hD i m))).mul (hP _)))
  · intro m x hx
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hterms m x hx i)
    change 1 ≤ 1+∑ i : A.centers, L*D i m*P (m+1) x
    linarith
  · intro x hx G hG s hs hs1 hb i m l hl
    have hread := hd i m G s (P (m+1) x) hs hs1 ((hP _).nonneg hx) hG (hb (m+1)) l (by omega)
    have hr := hread.linear uniqueDiffOn_univ zero_le_one
      (A.vectorPlaneRead_smooth i hG).contDiffOn spaceCoordinates.toContinuousLinearMap
    change WeightedEstimates.WeightedBound univ 1 l
      (L*(D i m*P (m+1) x/s^(l-2))) (spaceCoordinates ∘ A.vectorPlaneRead i G) at hr
    apply hr.mono_const
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => hterms m x hx i) (Finset.mem_univ i)
    change L*(D i m*P (m+1) x) ≤ 1+∑ i : A.centers, L*D i m*P (m+1) x
    nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
