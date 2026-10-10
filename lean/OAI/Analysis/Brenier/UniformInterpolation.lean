import OAI.Analysis.Brenier.AffineCertificate
import OAI.Analysis.Brenier.Basic
import OAI.Analysis.Brenier.BoundaryStrip
import OAI.Analysis.Brenier.SupportingInterpolation

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.SupportingMapInterpolation

/-- Finite-affine maximizing selections furnish global supporting maps directly. -/
theorem supports_of_finite_affine_maximizers
    {I F : Type*} [Fintype I] [Nonempty I]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (y : I → F) (c : I → ℝ) {T : F → F}
    (hactive : ∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    Supports (FiniteAffine.potential y c) T := by
  intro x z
  obtain ⟨i, hi, hmax⟩ := hactive x
  rw [hi]
  exact FiniteAffine.supporting_inequality y c x z i hmax

/-- Full quantitative interpolation for bounded supporting maps over an arbitrary
compact convex body. Its geometric constant is independent of the potentials,
maps, atom counts, masses, and slope separation. -/
theorem exists_integral_interpolation_constant
    {ι : Type*} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [Measure.IsAddHaarMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (L : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (u v : EuclideanSpace ℝ ι → ℝ)
        (T S : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι),
      Continuous u → Continuous v → Supports u T → Supports v S →
      Measurable T → Measurable S → (∀ x, ‖T x‖ ≤ L) → (∀ x, ‖S x‖ ≤ L) →
      ∀ h : ℝ, 0 < h →
      (∫ x in K, ‖T x - S x‖ ^ 2 ∂μ) ≤
        (12 * (Fintype.card ι : ℝ) / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
        B * h := by
  obtain ⟨C, hC, hstrip⟩ := exists_convex_boundary_strip_constant μ hKc hK hKi
  refine ⟨28 * (Fintype.card ι : ℝ) * L ^ 2 * C, by positivity, ?_⟩
  intro u v T S huc hvc hu hv hT hS hTL hSL h hh
  have hf : IntegrableOn (fun x => (u x - v x) ^ 2) K μ :=
    ContinuousOn.integrableOn_compact hKc ((huc.sub hvc).pow 2).continuousOn
  exact integral_norm_sub_sq_le_of_boundary_strip hu hv hT hS hKc.measurableSet
    hKc.measure_lt_top.ne hTL hSL hh (huc.sub hvc).measurable hf
    (fun e he => hstrip e he h hh.le)

end Problem358.SupportingMapInterpolation

end

noncomputable section

namespace Problem358

/-- The real one-third power is a nonnegative cube root. -/
lemma one_third_rpow_cube {w : ℝ} (hw : 0 ≤ w) :
    (Real.rpow w (1 / 3 : ℝ)) ^ 3 = w := by
  calc
    (Real.rpow w (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow w (1 / 3 : ℝ)) (3 : ℝ) := by
          exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow w ((1 / 3 : ℝ) * 3) := (Real.rpow_mul hw _ _).symm
    _ = w := by norm_num

/-- The scalar optimization in the gradient-interpolation argument.
The hypothesis is the squared slice estimate, valid at every positive scale.
This formulation includes zero Wasserstein distance without a limiting argument. -/
theorem stability_of_slice_bound {D w A B : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ h : ℝ, 0 < h → D ^ 2 ≤ A * w ^ 2 / h ^ 2 + B * h) :
    D ≤ Real.sqrt (A + B) * Real.rpow w (1 / 3 : ℝ) := by
  by_cases hw0 : w = 0
  · subst w
    have hDz : D = 0 := by
      by_contra hne
      have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
      have hB1 : 0 < B + 1 := by linarith
      have hD2 : 0 < D ^ 2 := sq_pos_of_pos hDp
      have hh := hbound (D ^ 2 / (B + 1)) (div_pos hD2 hB1)
      simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, zero_div, zero_add] at hh
      rw [← mul_div_assoc] at hh
      have hh' := (le_div_iff₀ hB1).mp hh
      nlinarith
    simp [hDz]
  · have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    let t := Real.rpow w (1 / 3 : ℝ)
    have ht : 0 < t := Real.rpow_pos_of_pos hwp _
    have ht3 : t ^ 3 = w := one_third_rpow_cube hw
    have hh := hbound (t ^ 2) (sq_pos_of_pos ht)
    have hquot : A * w ^ 2 / (t ^ 2) ^ 2 = A * t ^ 2 := by
      rw [← ht3]
      field_simp
    rw [hquot] at hh
    have hsum : 0 ≤ A + B := add_nonneg hA hB
    have hright : 0 ≤ Real.sqrt (A + B) * t :=
      mul_nonneg (Real.sqrt_nonneg _) ht.le
    apply (sq_le_sq₀ hD hright).mp
    calc
      D ^ 2 ≤ (A + B) * t ^ 2 := by nlinarith [hh]
      _ = (Real.sqrt (A + B) * t) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hsum]

/-- A cubic stability estimate implies a one-third Hölder estimate. -/
theorem stability_of_cubic_bound {D w A : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hA : 0 ≤ A)
    (hbound : D ^ 3 ≤ A * w) :
    D ≤ Real.rpow A (1 / 3 : ℝ) * Real.rpow w (1 / 3 : ℝ) := by
  have hr : 0 ≤ Real.rpow A (1 / 3 : ℝ) * Real.rpow w (1 / 3 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hw _)
  apply (pow_le_pow_iff_left₀ hD hr (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow, one_third_rpow_cube hA, one_third_rpow_cube hw]
  exact hbound

/-- Combine a Lipschitz bound on potentials with the squared slice estimate. -/
theorem stability_of_potential_slice_bound {D F w A B P : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hw : 0 ≤ w)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hpotential : F ≤ P * w)
    (hbound : ∀ h : ℝ, 0 < h → D ^ 2 ≤ A * F ^ 2 / h ^ 2 + B * h) :
    D ≤ Real.sqrt (A * P ^ 2 + B) * Real.rpow w (1 / 3 : ℝ) := by
  apply stability_of_slice_bound hD hw (mul_nonneg hA (sq_nonneg P)) hB
  intro h hh
  calc
    D ^ 2 ≤ A * F ^ 2 / h ^ 2 + B * h := hbound h hh
    _ ≤ A * (P * w) ^ 2 / h ^ 2 + B * h := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (sq_nonneg h)
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hF (mul_nonneg hP hw)).mpr hpotential) hA
    _ = A * P ^ 2 * w ^ 2 / h ^ 2 + B * h := by ring

/-- Small-scale interpolation estimates suffice when a uniform map bound is available.
The extra coefficient absorbs all scales larger than `H`; this is useful when the
boundary-strip estimate is obtained by contracting the source inside an interior ball. -/
theorem stability_of_local_slice_bound {D w A B M H : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : D ≤ M) (hH : 0 < H)
    (hbound : ∀ h : ℝ, 0 < h → h ≤ H →
      D ^ 2 ≤ A * w ^ 2 / h ^ 2 + B * h) :
    D ≤ Real.sqrt (A + (B + M ^ 2 / H)) * Real.rpow w (1 / 3 : ℝ) := by
  have hMH : 0 ≤ M ^ 2 / H := div_nonneg (sq_nonneg M) hH.le
  apply stability_of_slice_bound hD hw hA (add_nonneg hB hMH)
  intro h hh
  by_cases hsmall : h ≤ H
  · calc
      D ^ 2 ≤ A * w ^ 2 / h ^ 2 + B * h := hbound h hh hsmall
      _ ≤ A * w ^ 2 / h ^ 2 + (B + M ^ 2 / H) * h := by
        gcongr
        exact le_add_of_nonneg_right hMH
  · have hlarge : H ≤ h := (lt_of_not_ge hsmall).le
    calc
      D ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hD hM 2
      _ = M ^ 2 / H * H := by field_simp
      _ ≤ M ^ 2 / H * h := mul_le_mul_of_nonneg_left hlarge hMH
      _ ≤ (B + M ^ 2 / H) * h := by
        gcongr
        exact le_add_of_nonneg_left hB
      _ ≤ A * w ^ 2 / h ^ 2 + (B + M ^ 2 / H) * h := by
        exact le_add_of_nonneg_left (div_nonneg (mul_nonneg hA (sq_nonneg w))
          (sq_nonneg h))

end Problem358

open MeasureTheory

namespace Problem358.UniformInterpolation

variable {d : ℕ} (K : Set (E d))

/-- Normalizing the source multiplies every real integral by the same
nonnegative scalar. No finiteness assumptions are needed for this identity. -/
theorem integral_eq (f : E d → ℝ) :
    (∫ x, f x ∂uniformMeasure K) =
      ((volume K)⁻¹).toReal * ∫ x in K, f x := by
  simp only [uniformMeasure, integral_smul_measure, smul_eq_mul]

/-- The squared map distance is the normalized unnormalized-source energy. -/
theorem mapL2Dist_sq_eq (T S : E d → E d) :
    mapL2Dist (uniformMeasure K) T S ^ 2 =
      ((volume K)⁻¹).toReal * ∫ x in K, ‖T x - S x‖ ^ 2 := by
  unfold mapL2Dist
  rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  exact integral_eq K _

/-- Transfer the raw finite-difference estimate to the exact normalized-source
and map-distance conventions of the qualified problem. -/
theorem slice_bound_of_raw
    {T S : E d → E d} {f : E d → ℝ} {A B h : ℝ}
    (hraw : (∫ x in K, ‖T x - S x‖ ^ 2) ≤
      (A / h ^ 2) * (∫ x in K, f x ^ 2) + B * h) :
    mapL2Dist (uniformMeasure K) T S ^ 2 ≤
      (A / h ^ 2) * (∫ x, f x ^ 2 ∂uniformMeasure K) +
        (((volume K)⁻¹).toReal * B) * h := by
  rw [mapL2Dist_sq_eq]
  calc
    _ ≤ ((volume K)⁻¹).toReal *
        ((A / h ^ 2) * (∫ x in K, f x ^ 2) + B * h) :=
      mul_le_mul_of_nonneg_left hraw ENNReal.toReal_nonneg
    _ = _ := by rw [integral_eq]; ring

/-- Raw volume interpolation plus a normalized squared-potential estimate
implies the desired one-third bound, including zero target distance. -/
theorem one_third_bound_of_raw
    {T S : E d → E d} {f : E d → ℝ} {A B P w : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hw : 0 ≤ w)
    (hpotential : (∫ x, f x ^ 2 ∂uniformMeasure K) ≤ P ^ 2 * w ^ 2)
    (hraw : ∀ h : ℝ, 0 < h → (∫ x in K, ‖T x - S x‖ ^ 2) ≤
      (A / h ^ 2) * (∫ x in K, f x ^ 2) + B * h) :
    mapL2Dist (uniformMeasure K) T S ≤
      Real.sqrt (A * P ^ 2 + ((volume K)⁻¹).toReal * B) *
        Real.rpow w (1 / 3 : ℝ) := by
  apply Problem358.stability_of_slice_bound (Real.sqrt_nonneg _) hw
    (mul_nonneg hA (sq_nonneg P)) (mul_nonneg ENNReal.toReal_nonneg hB)
  intro h hh
  calc
    _ ≤ (A / h ^ 2) * (∫ x, f x ^ 2 ∂uniformMeasure K) +
        (((volume K)⁻¹).toReal * B) * h := slice_bound_of_raw K (hraw h hh)
    _ ≤ (A / h ^ 2) * (P ^ 2 * w ^ 2) +
        (((volume K)⁻¹).toReal * B) * h := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpotential
        (div_nonneg hA (sq_nonneg h))) le_rfl
    _ = _ := by ring

/-- Norm-form version matching the manuscript's Lipschitz potential estimate. -/
theorem one_third_bound_of_raw_of_potential
    {T S : E d → E d} {f : E d → ℝ} {A B P w : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ P) (hw : 0 ≤ w)
    (hpotential : Real.sqrt (∫ x, f x ^ 2 ∂uniformMeasure K) ≤ P * w)
    (hraw : ∀ h : ℝ, 0 < h → (∫ x in K, ‖T x - S x‖ ^ 2) ≤
      (A / h ^ 2) * (∫ x in K, f x ^ 2) + B * h) :
    mapL2Dist (uniformMeasure K) T S ≤
      Real.sqrt (A * P ^ 2 + ((volume K)⁻¹).toReal * B) *
        Real.rpow w (1 / 3 : ℝ) := by
  apply one_third_bound_of_raw K hA hB hw ?_ hraw
  calc
    _ = Real.sqrt (∫ x, f x ^ 2 ∂uniformMeasure K) ^ 2 :=
      (Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)).symm
    _ ≤ (P * w) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hP hw)).mpr hpotential
    _ = _ := mul_pow P w 2

end Problem358.UniformInterpolation

end

noncomputable section

open MeasureTheory

namespace Problem358.UniformInterpolation

open SupportingMapInterpolation

/-- Adding a constant to a potential does not change its supporting map. -/
theorem supports_add_const {d : ℕ} {u : E d → ℝ} {T : E d → E d}
    (hu : Supports u T) (c : ℝ) : Supports (fun x => u x + c) T := by
  intro x z
  have h := hu x z
  dsimp
  linarith

/-- The full normalized interpolation theorem, with no residual geometric or
finite-difference hypotheses.  The potential estimate may be supplied modulo
an arbitrary additive constant, as in a variance bound. -/
theorem exists_normalized_one_third_constant
    {d : ℕ} {K : Set (E d)}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (L P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u v : E d → ℝ) (T S : E d → E d),
      Continuous u → Continuous v → Supports u T → Supports v S →
      Measurable T → Measurable S → (∀ x, ‖T x‖ ≤ L) → (∀ x, ‖S x‖ ≤ L) →
      ∀ w : ℝ, 0 ≤ w →
      (∃ c : ℝ, (∫ x, (u x - v x - c) ^ 2 ∂uniformMeasure K) ≤ P ^ 2 * w ^ 2) →
      mapL2Dist (uniformMeasure K) T S ≤ C * Real.rpow w (1 / 3 : ℝ) := by
  obtain ⟨B, hB, hraw⟩ := exists_integral_interpolation_constant
    (volume : Measure (E d)) hKc hK hKi L
  refine ⟨Real.sqrt (12 * (d : ℝ) * P ^ 2 + ((volume K)⁻¹).toReal * B),
    Real.sqrt_nonneg _, ?_⟩
  intro u v T S huc hvc hu hv hT hS hTL hSL w hw hpotential
  obtain ⟨c, hc⟩ := hpotential
  apply one_third_bound_of_raw K (by positivity : 0 ≤ 12 * (d : ℝ)) hB hw hc
  intro h hh
  have hb := hraw u (fun x => v x + c) T S huc (hvc.add continuous_const)
    hu (supports_add_const hv c) hT hS hTL hSL h hh
  simpa only [Fintype.card_fin, sub_add_eq_sub_sub] using hb

end Problem358.UniformInterpolation

end

end OAI
