import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGroundTransform

namespace OAI

/-! IMS localization for the actual planar kinetic and potential integrals.
The partition functions need not have compact support; the test function
does. In particular the exterior member of a multiwell partition is allowed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → PlanarPosition → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ 1 (f i))
    (e x : PlanarPosition) :
    planarPartial (fun y => ∑ i ∈ s, f i y) e x = ∑ i ∈ s, planarPartial (f i) e x := by
  unfold planarPartial
  rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by norm_num) x)]
  simp only [sum_apply]

theorem planar_partition_cross {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1) (e x : PlanarPosition) :
    ∑ i, θ i x * planarPartial (θ i) e x = 0 := by
  have he : (fun y => ∑ i, θ i y * θ i y) = (fun _ : PlanarPosition => (1 : ℝ)) := by
    funext y
    simpa only [← sq] using hpart y
  have hd := congrArg (fun f : PlanarPosition → ℝ => planarPartial f e x) he
  rw [planarPartial_finsetSum _ _ (fun i _ => (hθ i).mul (hθ i))] at hd
  simp_rw [planarPartial_mul _ _ (hθ _) (hθ _)] at hd
  have hz : planarPartial (fun _ : PlanarPosition => (1 : ℝ)) e x = 0 := by
    simp [planarPartial]
  rw [hz, Finset.sum_add_distrib] at hd
  linarith

theorem planar_partition_gradient_identity {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (u : PlanarPosition → ℝ) (hu : ContDiff ℝ 1 u) (e x : PlanarPosition) :
    (∑ i, planarPartial (fun y => θ i y * u y) e x ^ 2) =
      planarPartial u e x ^ 2 + (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2 := by
  simp_rw [planarPartial_mul _ _ (hθ _) hu]
  calc
    (∑ i, (θ i x * planarPartial u e x + u x * planarPartial (θ i) e x) ^ 2) =
        (∑ i, θ i x ^ 2) * planarPartial u e x ^ 2 +
          (2 * u x * planarPartial u e x) * (∑ i, θ i x * planarPartial (θ i) e x) +
          (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2 := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hpart x, planar_partition_cross θ hθ hpart e x]; ring

theorem planar_partition_potential_identity {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (W u : PlanarPosition → ℝ) (x : PlanarPosition) :
    (∑ i, W x * (θ i x * u x) ^ 2) = W x * u x ^ 2 := by
  calc
    (∑ i, W x * (θ i x * u x) ^ 2) = (W x * u x ^ 2) * ∑ i, θ i x ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hpart x, mul_one]

theorem planar_partition_direction_integral {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (u : PlanarPosition → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (e : PlanarPosition) :
    (∑ i, ∫ x, planarPartial (fun y => θ i y * u y) e x ^ 2) =
      (∫ x, planarPartial u e x ^ 2) +
        ∫ x, (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2 := by
  have hi (i : ι) : Integrable (fun x => planarPartial (fun y => θ i y * u y) e x ^ 2) :=
    planar_partial_square_integrable _ ((hθ i).mul hu) hc.mul_left e
  have he : Integrable (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) := by
    have hs : HasCompactSupport (fun x => u x ^ 2) :=
      hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    have hm : HasCompactSupport (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) :=
      hs.mul_left
    have hd : Continuous (fun x => ∑ i, planarPartial (θ i) e x ^ 2) :=
      continuous_finsetSum _ (fun i _ => (planarPartial_continuous (hθ i) e).pow 2)
    exact (hd.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport hm
  rw [← integral_finsetSum _ (fun i _ => hi i),
    ← integral_add (planar_partial_square_integrable u hu hc e) he]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (planar_partition_gradient_identity θ hθ hpart u hu e))

theorem planar_potential_test_integrable (W u : PlanarPosition → ℝ) (hW : Continuous W)
    (hu : Continuous u) (hc : HasCompactSupport u) : Integrable (fun x => W x * u x ^ 2) := by
  have hs : HasCompactSupport (fun x => u x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hm : HasCompactSupport (fun x => W x * u x ^ 2) := hs.mul_left
  exact (hW.mul (hu.pow 2)).integrable_of_hasCompactSupport hm

/-- Exact IMS formula, with the localization cost expressed through the
actual classical directional derivatives of the partition. -/
theorem planar_IMS {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (W u : PlanarPosition → ℝ) (hW : Continuous W)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∑ i, planarTestForm W (fun x => θ i x * u x)) =
      planarTestForm W u + (1/2 : ℝ) *
        ∑ a : Fin 2, ∫ x, (∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) * u x ^ 2 := by
  have hi (i : ι) : Integrable (fun x => W x * (θ i x * u x) ^ 2) := by
    have hm : HasCompactSupport (fun x => θ i x * u x) := hc.mul_left
    exact planar_potential_test_integrable W _ hW ((hθ i).continuous.mul hu.continuous) hm
  have hp : (∑ i, ∫ x, W x * (θ i x * u x) ^ 2) = ∫ x, W x * u x ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (planar_partition_potential_identity θ hpart W u))
  unfold planarTestForm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [planar_partition_direction_integral θ hθ hpart u hu hc]
  rw [Finset.sum_add_distrib, hp]
  ring

end ContinuumCoulomb

end

end OAI
