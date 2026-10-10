import OAI.Analysis.KadisonSimilarity.FreeProduct.ArcCompression
import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralWordIsometries

namespace OAI

/-! The narrow-arc finite Fourier compression with actual normalized tracial
dihedral word inclusions. Their formulas and orthogonality are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Algebra ℂ R] [StarModule ℂ R] [StarRing R] in
theorem involution_unit_val_mul_self (d : Rˣ) (hd : d⁻¹ = d) :
    (d : R) * (d : R) = 1 := by
  have hu : d * d = 1 := by simpa only [hd] using inv_mul_cancel d
  exact congrArg (fun u : Rˣ => (u : R)) hu

omit [Algebra ℂ R] [StarModule ℂ R] in
theorem involution_unit_val_star (d : Rˣ) (hd : star d = d) : star (d : R) = (d : R) := by
  simpa only [Units.coe_star] using congrArg (fun u : Rˣ => (u : R)) hd

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
theorem dihedral_negative_nat_power (d s : Rˣ) (hd : d⁻¹ = d) (hs : s⁻¹ = s) (n : ℕ) :
    (↑((d * s) ^ (-(n : ℤ))) : R) = ((s : R) * (d : R)) ^ n := by
  rw [zpow_neg, ← inv_zpow, mul_inv_rev, hd, hs, zpow_natCast,
    Units.val_pow_eq_pow_val, Units.val_mul]

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
theorem dihedral_reflection_relation (d s : Rˣ) (hd : d⁻¹ = d) (hs : s⁻¹ = s) :
    d * (d * s) = (d * s)⁻¹ * d := by
  have hdd : d * d = 1 := by simpa only [hd] using inv_mul_cancel d
  rw [← mul_assoc, hdd, one_mul, mul_inv_rev, hd, hs, mul_assoc, hdd, mul_one]

theorem dihedralNormalization_sq {t : ℝ} (ht : 0 < t) :
    star (dihedralNormalization t) * dihedralNormalization t = (t : ℂ)⁻¹ := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have h := congrArg (fun z : ℂ => z * (t : ℂ)⁻¹) (dihedralNormalization_identity ht)
  simpa only [mul_assoc, mul_inv_cancel₀ htc, mul_one, one_mul] using h

omit [CompleteSpace H] [CompleteSpace K] in
/-- The tracial inner-product formula on the base space follows from
its unital compression representation. -/
theorem tracial_base_inner_of_compression (A : StarSubalgebra ℂ R)
    (τ : R →ₗ[ℂ] ℂ) (VA : A →ₗ[ℂ] K) (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x,
      inner ℂ (VA a) (ρ x (VA b)) = τ (star (a : R) * x * (b : R)))
    (hρone : ρ 1 = ContinuousLinearMap.id ℂ K) (a b : A) :
    inner ℂ (VA a) (VA b) = τ (star (a : R) * (b : R)) := by
  simpa only [hρone, ContinuousLinearMap.id_apply, mul_one] using hρ a b 1

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (V : R →ₗ[ℂ] H) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (D A : StarSubalgebra ℂ R) (hf : ScalarFree τ D A)
  (d s : Rˣ) (e : R) (hd : (d : R) ∈ D) (hs : (s : R) ∈ A) (he : e ∈ D)
  (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
  (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (hdstar : star d = d) (hsstar : star s = s)
  (hestar : star e = e) (hee : e * e = e)
  (VA : A →ₗ[ℂ] K)
  (hA : ∀ a b : A, inner ℂ (VA a) (VA b) = τ (star (a : R) * (b : R)))
  (hv : DenseRange VA) (t : ℝ) (ht : 0 < t) (hte : τ e = (t : ℂ))

/-- Actual normalized word inclusion for the unit convention of the Fourier
calculation. -/
def actualDihedralInclusion (k : ℕ) : K →ₗᵢ[ℂ] H :=
  dihedralWordIsometry τ hτ htr V hinner D A hf (d : R) (s : R) e hd hs he hd0 hs0
    (involution_unit_val_mul_self d hdinv) (involution_unit_val_mul_self s hsinv)
    (involution_unit_val_star d hdstar) (involution_unit_val_star s hsstar)
    hestar hee VA hA t ht hte hv k

omit [CompleteSpace K] in
@[simp] theorem actualDihedralInclusion_apply (k : ℕ) (a : A) :
    actualDihedralInclusion τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0 hdinv hsinv
      hdstar hsstar hestar hee VA hA hv t ht hte k (VA a) =
      dihedralNormalization t • V (e * (↑((d * s) ^ (-(k : ℤ))) : R) * (a : R)) := by
  rw [actualDihedralInclusion, dihedralWordIsometry_apply,
    dihedral_negative_nat_power d s hdinv hsinv]

omit [CompleteSpace K] in
theorem inner_actualDihedralInclusion (k j : ℕ) (x y : K) :
    inner ℂ
      (actualDihedralInclusion τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0 hdinv hsinv
        hdstar hsstar hestar hee VA hA hv t ht hte k x)
      (actualDihedralInclusion τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0 hdinv hsinv
        hdstar hsstar hestar hee VA hA hv t ht hte j y) =
      if k = j then inner ℂ x y else 0 :=
  inner_dihedralWordIsometry τ hτ htr V hinner D A hf (d : R) (s : R) e hd hs he hd0 hs0
    (involution_unit_val_mul_self d hdinv) (involution_unit_val_mul_self s hsinv)
    (involution_unit_val_star d hdstar) (involution_unit_val_star s hsstar)
    hestar hee VA hA t ht hte hv k j x y

/-- The finite column of actual word inclusions. -/
def actualDihedralColumns (N : ℕ) : Fin N → K →L[ℂ] H := fun i =>
  (actualDihedralInclusion τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0 hdinv hsinv
    hdstar hsstar hestar hee VA hA hv t ht hte i.val).toContinuousLinearMap

omit [CompleteSpace K] in
theorem norm_actualDihedralColumns_le_one (N : ℕ) :
    ‖sumColumns (actualDihedralColumns τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0
      hdinv hsinv hdstar hsstar hestar hee VA hA hv t ht hte N)‖ ≤ 1 := by
  apply norm_sumColumns_le _ (by norm_num)
  · intro i
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖actualDihedralInclusion τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0 hdinv hsinv
      hdstar hsstar hestar hee VA hA hv t ht hte i.val x‖ ≤ 1 * ‖x‖
    rw [LinearIsometry.norm_map, one_mul]
  · intro i j hij x y
    have hvne : i.val ≠ j.val := by exact fun h => hij (Fin.ext h)
    change inner ℂ (actualDihedralInclusion τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0
      hdinv hsinv hdstar hsstar hestar hee VA hA hv t ht hte i.val x)
      (actualDihedralInclusion τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0
      hdinv hsinv hdstar hsstar hestar hee VA hA hv t ht hte j.val y) = 0
    simp only [inner_actualDihedralInclusion, hvne, ↓reduceIte]

/-- The narrow-arc compression for the constructed normalized word maps.
Neither their word formula nor their orthogonality is an input. -/
theorem narrow_arc_actual_dihedral_compression
    {N : ℕ} (hN : 0 < N)
    (L : R →ₗ[ℂ] (H →L[ℂ] H)) (hleft : ∀ a b, L a (V b) = V (a * b))
    (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x, inner ℂ (VA a) (ρ x (VA b)) = τ (star (a : R) * x * (b : R)))
    (hρone : ρ 1 = ContinuousLinearMap.id ℂ K)
    (E₀ EC : R →ₗ[ℂ] R) (htrace : ∀ x, τ (E₀ x) = τ x)
    (hbase : ∀ (a b : A) x, E₀ ((a : R) * x * (b : R)) = (a : R) * E₀ x * (b : R))
    (f h : R) (heh : e * h = h) (hhe : h * e = h)
    (hEC : EC h = (2 * (t : ℂ)) ^ 2 • (f * dihedralHalfProjection d))
    (hbimod : ∀ j k : ℤ, EC ((↑((d * s) ^ j) : R) * h * (↑((d * s) ^ (-k)) : R)) =
      (↑((d * s) ^ j) : R) * EC h * (↑((d * s) ^ (-k)) : R))
    (htower : ∀ j k : ℤ,
      E₀ (EC ((↑((d * s) ^ j) : R) * h * (↑((d * s) ^ (-k)) : R))) =
        E₀ ((↑((d * s) ^ j) : R) * h * (↑((d * s) ^ (-k)) : R)))
    (hcomm : ∀ j : ℤ, (↑((d * s) ^ j) : R) * f = f * (↑((d * s) ^ j) : R))
    (hrot : ∀ l : ℤ, E₀ (f * (↑((d * s) ^ l) : R)) =
      arcFourierIntegral (arcWidth N) l • (1 : R))
    (href : ∀ l : ℤ, E₀ (f * (↑((d * s) ^ l) : R) * (↑((d * s)⁻¹ * d) : R)) =
      arcFourierIntegral (arcWidth N) l • (↑((d * s)⁻¹ * d) : R)) :
    (sumColumns (actualDihedralColumns τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0
      hdinv hsinv hdstar hsstar hestar hee VA hA hv t ht hte N)).adjoint.comp
      ((L h).comp (sumColumns (actualDihedralColumns τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0
        hdinv hsinv hdstar hsstar hestar hee VA hA hv t ht hte N))) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ K +
        (arcHankelMatrix N i j : ℂ) • ρ (↑((d * s)⁻¹ * d) : R)) := by
  apply narrow_arc_tracial_compression hN A τ V L hinner hleft VA hv ρ hρ hρone E₀ EC
    htrace hbase (d * s) d (free_symmetry_product_star d s hdstar hsstar hdinv hsinv)
    (dihedral_reflection_relation d s hdinv hsinv) e f h hestar heh hhe t ht
    (dihedralNormalization t) (dihedralNormalization_sq ht)
    (actualDihedralColumns τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0
      hdinv hsinv hdstar hsstar hestar hee VA hA hv t ht hte N)
  · intro i a
    exact actualDihedralInclusion_apply τ hτ htr V hinner D A hf d s e hd hs he hd0 hs0
      hdinv hsinv hdstar hsstar hestar hee VA hA hv t ht hte i.val a
  · exact hEC
  · exact hbimod
  · exact htower
  · exact hcomm
  · exact hrot
  · exact href

end KadisonSimilarity

end

end OAI
