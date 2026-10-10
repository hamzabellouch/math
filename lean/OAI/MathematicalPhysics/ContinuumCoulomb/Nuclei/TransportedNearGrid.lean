import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserIntegrability
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeIntegral
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedGrid

namespace OAI

/-! Near cells have uniformly bounded continuous Coulomb mass after the
actual Moser transport. The bound is independent of the enclosing box. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem transported_near_cube_distance {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    {y b x : Position} (hnear : ‖y-G b‖ ≤ 4*(L:ℝ)*h) (hx : x ∈ positionCube b h) :
    ‖y-G x‖ < 6*(L:ℝ)*h := by
  have hn : ‖G x-G b‖ ≤ (L:ℝ)*h :=
    (hG.norm_sub_le x b).trans (mul_le_mul_of_nonneg_left
      (positionCube_norm_sub_le hh.le hx) L.coe_nonneg)
  have ht := norm_sub_le_norm_sub_add_norm_sub y (G b) (G x)
  rw [norm_sub_rev (G b) (G x)] at ht
  have hp : 0 < (L:ℝ)*h := mul_pos (by exact_mod_cast hL) hh
  linarith

theorem transported_near_kernel_eq {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    {y b x : Position} (hnear : ‖y-G b‖ ≤ 4*(L:ℝ)*h) (hx : x ∈ positionCube b h) :
    Coulomb.coulombKernel (y-G x) = Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G x) := by
  have hm : y-G x ∈ Metric.ball (0:Position) (6*(L:ℝ)*h) := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      transported_near_cube_distance hh G hL hG hnear hx
  exact (Set.indicator_of_mem hm _).symm

theorem moser_near_grid_integral_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    {L : ℝ≥0} (hL : 0 < L) (hLip : LipschitzWith L (fun x => G x 1))
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h)
    (hsub : ∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S)
    (y : Position) (hnear : ∀ i, ‖y-G (gaussCellCenter h (index i)) 1‖ ≤ 4*(L:ℝ)*h) :
    (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) ≤ 108*Real.pi*(L:ℝ)^2*h^2 := by
  have hi := moser_coulomb_integrableOn hpublished hrho hH hS V hV hbound hsupport G hG hbij hfix y
  have ht := moser_truncatedCoulomb_integrable hpublished hrho V hV hbound hsupport
    G hG hbij hfix y (6*(L:ℝ)*h)
  calc
    _ = ∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h,
        Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G x 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [positionCellIntegral_eq_setIntegral _ hh.le _ (hi.mono_set (hsub i))]
      apply setIntegral_congr_fun (positionCube_isClosed _ _).measurableSet
      intro x hx
      exact transported_near_kernel_eq hh (fun x => G x 1) hL hLip (hnear i) hx
    _ ≤ ∫ x in slabDomain H S, Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G x 1) :=
      grid_cell_integral_sum_le_on index hindex hh hsub _ ht
        (fun x => Coulomb.truncatedCoulomb_nonneg _ _)
    _ ≤ 3*Real.pi*(6*(L:ℝ)*h)^2 :=
      moser_truncatedCoulomb_bound hpublished hrho V hV hbound hsupport G hG hbij hfix y (by positivity)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
