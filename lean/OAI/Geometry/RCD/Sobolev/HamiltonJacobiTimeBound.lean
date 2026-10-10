import OAI.Geometry.RCD.Sobolev.SupportedWeakSourceBound
import OAI.Geometry.RCD.Heat.CompactSubsetTimePairing
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Time increments controlled by the local weak equation

The source term is tested only on the support of the compact test. Its
bound uses the actual weak Laplacian and the local slope bound.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

theorem local_hamilton_jacobi_source_bound
    (w φ : SobolevSpace μ Q) (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ Q w q)
    {Ω : Set X} (hΩ : IsCompact Ω) (D : X → ℝ) (ε L : ℝ)
    (hD : D =ᵐ[μ.restrict Ω] fun x => ε/2*q x + localGamma μ Q w w x/2)
    (hφs : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q φ x = 0)
    {B : ℝ} (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ B)
    (hgrad : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q w x ≤ L) :
    |∫ x in Ω, SobolevSpace.toLp μ Q φ x * D x ∂μ| ≤
      |ε|/2 * (L * ∫ x, SobolevSpace.minimalSlope μ Q φ x ∂μ) +
        L^2/2 * ∫ x in Ω, |SobolevSpace.toLp μ Q φ x| ∂μ := by
  let Φ := SobolevSpace.toLp μ Q φ
  have hiΦ : IntegrableOn Φ Ω μ := lp_integrableOn_of_finite μ Φ Ω hΩ.measure_lt_top.ne
  have hiq : Integrable (fun x => Φ x*q x) μ := by
    simpa only [Real.inner_apply] using (L2.integrable_inner (𝕜 := ℝ) Φ q)
  have hig : Integrable (fun x => Φ x*localGamma μ Q w w x) μ :=
    (localGamma_memL1 μ Q w w).bdd_mul (Lp.aestronglyMeasurable Φ)
      (by simpa only [Real.norm_eq_abs] using hB)
  have hg : ∀ᵐ x ∂μ.restrict Ω, |localGamma μ Q w w x| ≤ L^2 := by
    filter_upwards [hgrad,ae_restrict_of_ae (localGamma_self μ Q w),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q w))]
      with x hx he hp
    rw [he,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hp hx 2
  have hgb : |∫ x in Ω, Φ x*localGamma μ Q w w x ∂μ| ≤
      L^2 * ∫ x in Ω, |Φ x| ∂μ := by
    calc
      _ ≤ ∫ x in Ω, |Φ x*localGamma μ Q w w x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x in Ω, L^2 * |Φ x| ∂μ := by
        apply integral_mono_ae hig.integrableOn.abs (hiΦ.abs.const_mul _)
        filter_upwards [hg] with x hx
        rw [abs_mul,mul_comm (L^2)]
        exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  have hqi : (∫ x in Ω, Φ x*q x ∂μ) = inner ℝ q Φ := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (by
      filter_upwards [hφs] with x hx hnot
      rw [hx hnot,zero_mul])]
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [Real.inner_apply]; ring
  have he : (∫ x in Ω, Φ x*D x ∂μ) = ε/2*inner ℝ q Φ +
      1/2*(∫ x in Ω, Φ x*localGamma μ Q w w x ∂μ) := by
    calc
      _ = ∫ x in Ω, ε/2*(Φ x*q x)+1/2*(Φ x*localGamma μ Q w w x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hD] with x hx
        rw [hx]
        ring
      _ = _ := by
        rw [integral_add (hiq.integrableOn.const_mul _) (hig.integrableOn.const_mul _),
          integral_const_mul,integral_const_mul,hqi]
  rw [he]
  calc
    _ ≤ |ε/2*inner ℝ q Φ| + |1/2*(∫ x in Ω, Φ x*localGamma μ Q w w x ∂μ)| := abs_add_le _ _
    _ = |ε|/2 * |inner ℝ q Φ| + 1/2*|∫ x in Ω, Φ x*localGamma μ Q w w x ∂μ| := by
      rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_mul]
      norm_num
    _ ≤ |ε|/2 * (L * ∫ x, SobolevSpace.minimalSlope μ Q φ x ∂μ) +
        1/2*(L^2 * ∫ x in Ω, |Φ x| ∂μ) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (supported_weak_source_test_bound μ Q w φ q hq hΩ.measurableSet hΩ.measure_lt_top.ne hφs hgrad)
        (by positivity)) (mul_le_mul_of_nonneg_left hgb (by norm_num))
    _ = _ := by ring

theorem hamilton_jacobi_pairing_time_bound
    (H D : ℝ → X → ℝ)
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ))
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => H s x) (D t x) t)
    {Ω : Set X} (hΩ : IsCompact Ω) {a b : ℝ} (ha : 0 < a)
    (w : ℝ → SobolevSpace μ Q) (q : ℝ → Lp ℝ 2 μ) (ε L : ℝ)
    (hloc : ∀ t ∈ Icc a b, IsWeakLaplacian μ Q (w t) (q t) ∧
      (D t =ᵐ[μ.restrict Ω] fun x => ε/2*q t x + localGamma μ Q (w t) (w t) x/2) ∧
      ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q (w t) x ≤ L)
    (φ : SobolevSpace μ Q)
    (hφs : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q φ x = 0)
    {B : ℝ} (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ B)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |(∫ x in Ω, SobolevSpace.toLp μ Q φ x * H t x ∂μ) -
      (∫ x in Ω, SobolevSpace.toLp μ Q φ x * H s x ∂μ)| ≤
      (|ε|/2 * (L * ∫ x, SobolevSpace.minimalSlope μ Q φ x ∂μ) +
        L^2/2 * ∫ x in Ω, |SobolevSpace.toLp μ Q φ x| ∂μ) * |t-s| := by
  let Φ := SobolevSpace.toLp μ Q φ
  have hiΦ : IntegrableOn Φ Ω μ := lp_integrableOn_of_finite μ Φ Ω hΩ.measure_lt_top.ne
  have hiΦ' : Integrable (fun x : Ω => Φ x) (μ.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal hΩ.measurableSet).mp hiΦ
  have hder (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => ∫ x in Ω, Φ x*H s x ∂μ) (∫ x in Ω, Φ x*D t x ∂μ) t := by
    have hh := compact_subset_time_pairing_hasDerivAt H D hH hD hd Ω hΩ
      (μ.comap Subtype.val) (fun x => Φ x) hiΦ' (ha.trans_le ht.1)
    have heH (s : ℝ) : (∫ x : Ω, Φ x*H s x ∂μ.comap Subtype.val) =
        ∫ x in Ω, Φ x*H s x ∂μ :=
      integral_subtype_comap hΩ.measurableSet (fun x => Φ x*H s x)
    have heD : (∫ x : Ω, Φ x*D t x ∂μ.comap Subtype.val) =
        ∫ x in Ω, Φ x*D t x ∂μ :=
      integral_subtype_comap hΩ.measurableSet (fun x => Φ x*D t x)
    simpa only [heH,heD] using hh
  have hbnd (t : ℝ) (ht : t ∈ Icc a b) :=
    local_hamilton_jacobi_source_bound μ Q (w t) φ (q t) (hloc t ht).1 hΩ (D t)
      ε L (hloc t ht).2.1 hφs hB (hloc t ht).2.2
  simpa only [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hder t ht).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hbnd t ht) hs ht

end RegularPointCoordinates

end

end OAI
