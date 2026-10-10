import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakComplexLaplacian
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.BoundedFormCross
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorTotalReplacement

namespace OAI

/-! An actual differential residual controls the mixed bounded-potential
form against every weak-H1 state, without restricting its smoothness. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem h1Coordinates_complex_inner {n : ℕ} (u v : Coulomb.H1Vector n) (a : H1Index n) :
    inner ℂ (h1Coordinates u a) (h1Coordinates v a) =
      ∫ x, star (h1CoordinateFunction u a x)*h1CoordinateFunction v a x :=
  h1_inner_complex_coordinate v a _ (h1Coordinate_memLp u a)

theorem h1Coordinates_complex_mass_inner {n : ℕ} (u v : Coulomb.H1Vector n) :
    (∑ s, inner ℂ (h1Coordinates u (Sum.inl s)) (h1Coordinates v (Sum.inl s))) =
      inner ℂ u.toHilbert v.toHilbert := by
  rw [PiLp.inner_apply]
  rfl

theorem boundedPotential_complex_pairing {n : ℕ} (u v : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (s : SpinConfiguration n) :
    inner ℂ (h1Coordinates u (Sum.inl s))
      (BoundedPotential.operator V hV B hB (h1Coordinates v (Sum.inl s))) =
      ∫ x, star (u.value s x)*((V x:ℂ)*v.value s x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp,
    (h1Coordinate_memLp v (Sum.inl s)).coeFn_toLp,
    BoundedPotential.operator_ae V hV B hB (h1Coordinates v (Sum.inl s))] with x hu hv hA
  change h1Coordinates u (Sum.inl s) x = u.value s x at hu
  change h1Coordinates v (Sum.inl s) x = v.value s x at hv
  rw [hA,hu,hv,RCLike.inner_apply]
  exact mul_comm _ _

theorem classical_residual_pairing (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (u v : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B E : ℝ) (hB : ∀ x, |V x| ≤ B)
    (R : SpinConfiguration n → Configuration n → ℂ)
    (hR : ∀ s, MemLp (R s) 2)
    (hu : ∀ s, ContDiff ℝ 2 (u.value s))
    (hdu : ∀ s a x, u.gradient s a x = configurationComplexPartial (u.value s) a x)
    (heq : ∀ s x, R s x = (-1/2:ℂ)*configurationComplexLaplacian (u.value s) x+
      (V x:ℂ)*u.value s x-(E:ℂ)*u.value s x) :
    graphComplexCross (BoundedPotential.operator V hV B hB) (h1Coordinates u) (h1Coordinates v)-
      (E:ℂ)*inner ℂ u.toHilbert v.toHilbert =
      ∑ s, ∫ x, star (R s x)*v.value s x := by
  have hm (s : SpinConfiguration n) : MemLp (fun x => (V x:ℂ)*u.value s x) 2 := by
    apply (u.value_L2 s).of_le_mul (c := B)
      ((Complex.continuous_ofReal.comp hV).aestronglyMeasurable.mul (u.value_L2 s).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(V x:ℂ)*u.value s x‖ ≤ B*‖u.value s x‖
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hLap (s : SpinConfiguration n) : MemLp (configurationComplexLaplacian (u.value s)) 2 := by
    have hfun : configurationComplexLaplacian (u.value s) =
        (fun x => (2:ℂ)*((V x:ℂ)*u.value s x-(E:ℂ)*u.value s x-R s x)) := by
      funext x
      linear_combination 2*(heq s x)
    rw [hfun]
    exact ((hm s).sub ((u.value_L2 s).const_mul (E:ℂ)) |>.sub (hR s)).const_mul 2
  have hp (s : SpinConfiguration n) (a : Fin n × Fin 3) :
      MemLp (configurationComplexPartial (u.value s) a) 2 :=
    (memLp_congr_ae (Filter.Eventually.of_forall (hdu s a))).mp (u.partial_L2 s a)
  have hkin (s : SpinConfiguration n) := weakH1_complex_laplacian_pairing hdensity
    (u.value s) (hu s) (hp s) (hLap s) v s
  have hpoint (s : SpinConfiguration n) :
      (1/2:ℂ)*(∑ a, ∫ x, star (u.gradient s a x)*v.gradient s a x)+
        (∫ x, star (u.value s x)*((V x:ℂ)*v.value s x))-
        (E:ℂ)*(∫ x, star (u.value s x)*v.value s x) =
        ∫ x, star (R s x)*v.value s x := by
    have hLI := (hLap s).star.integrable_mul (v.value_L2 s)
    have hVI := (hm s).star.integrable_mul (v.value_L2 s)
    have hUI := (u.value_L2 s).star.integrable_mul (v.value_L2 s)
    have hhalf : star (-1/2:ℂ) = (-1/2:ℂ) := by
      change (starRingEnd ℂ) (-1/2) = (-1/2:ℂ)
      simp only [map_div₀,map_neg,map_one,map_ofNat]
    have hE : star (E:ℂ) = (E:ℂ) := Complex.conj_ofReal E
    have hprod (x : Configuration n) : star (R s x)*v.value s x =
        (-1/2:ℂ)*(star (configurationComplexLaplacian (u.value s) x)*v.value s x)+
          star ((V x:ℂ)*u.value s x)*v.value s x-
          (E:ℂ)*(star (u.value s x)*v.value s x) := by
      rw [heq]
      simp only [star_sub,star_add,star_mul,hhalf,hE]
      ring
    simp_rw [hprod]
    have hsub := integral_sub ((hLI.const_mul (-1/2:ℂ)).add hVI) (hUI.const_mul (E:ℂ))
    have hadd := integral_add (hLI.const_mul (-1/2:ℂ)) hVI
    simp only [Pi.add_apply,Pi.mul_apply,Pi.star_apply] at hsub hadd
    rw [hsub,hadd,integral_const_mul,integral_const_mul]
    simp_rw [← hdu] at hkin
    rw [hkin]
    have hvprod : (∫ x, star ((V x:ℂ)*u.value s x)*v.value s x) =
        ∫ x, star (u.value s x)*((V x:ℂ)*v.value s x) := by
      congr 1
      funext x
      simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
      ring
    rw [hvprod]
    ring
  rw [← h1Coordinates_complex_mass_inner]
  simp only [graphComplexCross,h1Coordinates_complex_inner,boundedPotential_complex_pairing,
    h1CoordinateFunction]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun s _ => by simpa only [Finset.mul_sum] using hpoint s)

theorem residual_integral_square_bound {n : ℕ} (v : Coulomb.H1Vector n)
    (R : SpinConfiguration n → Configuration n → ℂ) (hR : ∀ s, MemLp (R s) 2) :
    ‖∑ s, ∫ x, star (R s x)*v.value s x‖^2 ≤
      (∑ s, ∫ x, ‖R s x‖^2)*Coulomb.mass v := by
  let r (s : SpinConfiguration n) : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    (hR s).toLp (R s)
  have he (s : SpinConfiguration n) : (∫ x, star (R s x)*v.value s x) =
      inner ℂ (r s) (h1Coordinates v (Sum.inl s)) :=
    (h1_inner_complex_coordinate v (Sum.inl s) _ (hR s)).symm
  simp only [he]
  have ht : ‖∑ s, inner ℂ (r s) (h1Coordinates v (Sum.inl s))‖ ≤
      ∑ s, ‖r s‖*‖h1Coordinates v (Sum.inl s)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => norm_inner_le_norm _ _))
  have hb := (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _)
  simpa only [r,Coulomb.norm_toLp_sq_complex,h1Coordinates_norm_sq,h1CoordinateFunction,
    Coulomb.mass] using hb

end ContinuumCoulomb

end

end OAI
