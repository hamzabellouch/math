import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.ScalarRegularity07

namespace OAI


section

/-! Actual smooth closed and coclosed two-forms. Their inclusion in the
finite weak Hodge kernel proves finite-dimensionality without an index input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormExterior : smoothTwoForms o →ₗ[ℝ]
    (FrameBundle g → Fin 4 → Fin 4 → Fin 4 → ℝ) where
  toFun u e i j k := twoFormExteriorComponent
    (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) i j k
  map_add' u v := by
    funext e i j k
    simp only [twoFormExteriorComponent, twoFormFramedCovariantDerivative_add, Pi.add_apply]
    ring
  map_smul' r u := by
    funext e i j k
    change twoFormExteriorComponent (fun p q s =>
      twoFormFramedCovariantDerivative o (r • u.val) e ![p,q,s]) i j k = _
    simp only [twoFormExteriorComponent, twoFormFramedCovariantDerivative_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def smoothTwoFormCodifferential : smoothTwoForms o →ₗ[ℝ] (FrameBundle g → Fin 4 → ℝ) where
  toFun u e k := twoFormCodiffComponent
    (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) k
  map_add' u v := by
    funext e k
    simp only [twoFormCodiffComponent, twoFormFramedCovariantDerivative_add, Pi.add_apply,
      Finset.sum_add_distrib, neg_add]
  map_smul' r u := by
    funext e k
    change -(∑ i, twoFormFramedCovariantDerivative o (r • u.val) e ![i,i,k]) = _
    simp only [twoFormFramedCovariantDerivative_smul, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, RingHom.id_apply]
    simp only [twoFormCodiffComponent, mul_neg]

def smoothHarmonicTwoForms : Submodule ℝ (smoothTwoForms o) :=
  smoothTwoFormExterior.ker ⊓ smoothTwoFormCodifferential.ker

theorem mem_smoothHarmonicTwoForms (u : smoothTwoForms o) :
    u ∈ smoothHarmonicTwoForms ↔
      (∀ e i j k, smoothTwoFormExterior u e i j k = 0) ∧
      ∀ e k, smoothTwoFormCodifferential u e k = 0 := by
  simp only [smoothHarmonicTwoForms, Submodule.mem_inf, LinearMap.mem_ker,
    funext_iff, Pi.zero_apply]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothHarmonicTwoForm_energy_zero (u : smoothTwoForms o)
    (hu : u ∈ smoothHarmonicTwoForms) : smoothTwoFormDeRhamEnergy u = 0 := by
  obtain ⟨hd, hc⟩ := (mem_smoothHarmonicTwoForms u).mp hu
  have he (e : FrameBundle g) : twoFormDeRhamQuadratic (fun i j k =>
      twoFormFramedCovariantDerivative o u.val e ![i,j,k]) = 0 := by
    change (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) +
      (∑ k, smoothTwoFormCodifferential u e k ^ 2) = 0
    simp only [hd, hc, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
      mul_zero, add_zero]
  unfold smoothTwoFormDeRhamEnergy
  simp only [he, integral_zero]

def smoothHarmonicToWeak (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] twoFormWeitzenbockKernel (o := o) where
  toFun u := ⟨smoothTwoFormToH1 (show SmoothH1TwoForm o from u.val), by
    apply (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mpr
    rw [twoFormHodgeForm_smooth hRic]
    exact smoothHarmonicTwoForm_energy_zero u.val u.property⟩
  map_add' u v := Subtype.ext (map_add smoothTwoFormToH1
    (show SmoothH1TwoForm o from u.val) (show SmoothH1TwoForm o from v.val))
  map_smul' r u := Subtype.ext (map_smul smoothTwoFormToH1 r
    (show SmoothH1TwoForm o from u.val))

theorem smoothHarmonicToWeak_injective (hRic : RicciThree g) :
    Function.Injective (smoothHarmonicToWeak (o := o) hRic) := by
  intro u v h
  apply Subtype.ext
  have he : smoothTwoFormToH1 (show SmoothH1TwoForm o from u.val) =
      smoothTwoFormToH1 (show SmoothH1TwoForm o from v.val) := congrArg Subtype.val h
  have hv : (show SmoothH1TwoForm o from u.val) = (show SmoothH1TwoForm o from v.val) :=
    (smoothTwoFormToH1 (o := o)).injective he
  exact hv

theorem smoothHarmonicTwoForms_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicTwoForms (o := o)) :=
  FiniteDimensional.of_injective (smoothHarmonicToWeak hRic) (smoothHarmonicToWeak_injective hRic)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth Hodge Laplacian in the normalization Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothHodgeLaplacian (hRic : RicciThree g) (u : smoothTwoForms o) : smoothTwoForms o :=
  (6 : ℝ) • u - (2 : ℝ) • smoothTwoFormCurvature u - smoothTwoFormRoughTrace hRic u

theorem smoothTwoFormL2Inner_sub (u v w : smoothTwoForms o) :
    smoothTwoFormL2Inner (u - v) w = smoothTwoFormL2Inner u w - smoothTwoFormL2Inner v w := by
  exact @inner_sub_left ℝ (SmoothL2TwoForm o) _ _ _ (u : SmoothL2TwoForm o)
    (v : SmoothL2TwoForm o) (w : SmoothL2TwoForm o)

theorem twoFormHodgeForm_smooth_pairing (u v : SmoothH1TwoForm o) :
    twoFormHodgeForm (smoothTwoFormToH1 u) (smoothTwoFormToH1 v) =
      smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v +
        6 * smoothTwoFormL2Inner (u : smoothTwoForms o) v -
        2 * smoothTwoFormL2Inner (smoothTwoFormCurvature (u : smoothTwoForms o)) v := by
  unfold twoFormHodgeForm
  rw [twoFormH1ToL2_smooth, twoFormH1ToL2_smooth, smoothTwoFormToH1.inner_map_map]
  simp only [twoFormWeitzenbockPotential, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left]
  rw [twoFormL2Curvature_smooth, smoothTwoFormToL2.inner_map_map,
    smoothTwoFormToL2.inner_map_map]
  change (smoothTwoFormL2Inner (u : smoothTwoForms o) v +
      smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v) -
      (2 * smoothTwoFormL2Inner (smoothTwoFormCurvature (u : smoothTwoForms o)) v -
        5 * smoothTwoFormL2Inner (u : smoothTwoForms o) v) = _
  ring

theorem smoothHodgeLaplacian_pairing (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v =
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o))
        (smoothTwoFormToH1 (v : SmoothH1TwoForm o)) := by
  apply Eq.trans ?_ (twoFormHodgeForm_smooth_pairing
    (u : SmoothH1TwoForm o) (v : SmoothH1TwoForm o)).symm
  rw [smoothHodgeLaplacian, smoothTwoFormL2Inner_sub, smoothTwoFormL2Inner_sub,
    smoothTwoFormL2Inner_smul, smoothTwoFormL2Inner_smul,
    smoothTwoForm_roughTrace_green_left hRic]
  ring

theorem smoothHodgeLaplacian_selfAdjoint (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v =
      smoothTwoFormL2Inner u (smoothHodgeLaplacian hRic v) := by
  rw [smoothTwoFormL2Inner_comm u, smoothHodgeLaplacian_pairing,
    smoothHodgeLaplacian_pairing, twoFormHodgeForm_comm]

end
end PositiveEinsteinFour.Geometry
end

end OAI
