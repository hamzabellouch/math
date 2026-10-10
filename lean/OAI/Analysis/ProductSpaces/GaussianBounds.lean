import OAI.Analysis.ProductSpaces.AffineBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
namespace FiniteHead

lemma affine_algebraic_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (T : FiniteHead) (x : productSpan μ) (hx : x ∈ T.headSpan μ h₂)
    (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ (ι : Type) [Fintype ι], ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    ∀ y ∈ T.tailAlgebraic μ h₂,
      (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) * ‖y‖ - D * ‖x‖ ≤ midpointGain t x y := by
  classical
  obtain ⟨c, rfl⟩ := T.head_representative μ h₂ x hx
  intro y hy
  obtain ⟨s, hs, a, rfl⟩ := T.tail_representative μ h₂ y hy
  let b : s → T.Boundary := fun k => T.exit k (hs k k.property)
  let ι := Set.range b
  let : Fintype ι := Fintype.ofFinite _
  let e : ι → T.Boundary := Subtype.val
  let j : s → ι := fun k => ⟨b k, ⟨k, rfl⟩⟩
  have he : Function.Injective e := Subtype.val_injective
  have hv : ∀ k : s, (e (j k)).val.val <+: k.val := fun k => T.exit_prefix k (hs k k.property)
  exact T.affine_finite_polynomials μ h₂ hmean e he (fun k : s => k.val) j a hv c
    t A D ht hA hC (hscalar ι)

end FiniteHead

lemma averaged_midpoint_from_scalar (μ : Measure ℝ) (hμ : MultiplierHypotheses μ)
    (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ (ι : Type) [Fintype ι], ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)) - D ≤
      averagedMidpointModulus (productSpan μ) (normSeminorm ℝ (productSpan μ)) t := by
  let := hμ.probability
  apply averagedModulus_of_dense_affine (main_general μ hμ).1 (dense_pathVector_span μ hμ.second_moment)
    _ D t (div_nonneg hA hC.le) hD
  intro u hu
  have hu' : u ∈ Submodule.span ℝ (pathVector μ hμ.second_moment '' (Set.univ : Set Vertex)) := by
    change u ∈ Submodule.span ℝ (Set.range (pathVector μ hμ.second_moment)) at hu
    simpa only [Set.image_univ] using hu
  obtain ⟨s, hs, a, ha⟩ := (Submodule.mem_span_image_iff_exists_fun ℝ).mp hu'
  let T := FiniteHead.containing s
  have hut : u ∈ T.headSpan μ hμ.second_moment := by
    rw [← ha]
    apply Submodule.sum_mem
    intro v hv
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨v.val, FiniteHead.mem_containing s v.property, rfl⟩
  refine ⟨T.tailSpace μ hμ.second_moment, T.tailSpace_cofinite μ hμ.second_moment, ?_⟩
  exact affine_on_closed_tail (T.tailAlgebraic μ hμ.second_moment) u
    (T.affine_algebraic_tail μ hμ.second_moment hμ.mean_one u hut t A D ht hA hC hscalar)

lemma gaussianSquareLaw_memLp : MemLp (fun w : ℝ => w) 2 gaussianSquareLaw := by
  unfold gaussianSquareLaw
  exact (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr gaussian_square_memLp

lemma gaussianSquareLaw_mean : (∫ w : ℝ, w ∂gaussianSquareLaw) = 1 := by
  rw [gaussianSquareLaw, integral_map (by fun_prop) (by fun_prop)]
  exact gaussian_integral_sq

lemma gaussianSquareLaw_second : (∫ w : ℝ, w ^ 2 ∂gaussianSquareLaw) = 3 := by
  rw [gaussianSquareLaw, integral_map (by fun_prop) (by fun_prop)]
  simpa only [← pow_mul, Nat.reduceMul] using gaussian_integral_fourth

lemma gaussianSquareLaw_hypotheses : MultiplierHypotheses gaussianSquareLaw := by
  refine ⟨inferInstance, ?_, ?_, gaussianSquareLaw_mean, gaussianSquareLaw_memLp⟩
  · unfold gaussianSquareLaw
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
    filter_upwards [(gaussianReal 0 1).ae_ne 0] with w hw
    exact sq_pos_of_ne_zero hw
  · intro c hc
    have h1 : (1 : ℝ) = c := by
      calc
        1 = ∫ w : ℝ, w ∂gaussianSquareLaw := gaussianSquareLaw_mean.symm
        _ = ∫ _ : ℝ, c ∂gaussianSquareLaw := integral_congr_ae hc
        _ = c := by simp
    have h2 : (∫ w : ℝ, w ^ 2 ∂gaussianSquareLaw) = c ^ 2 := by
      calc
        _ = ∫ _ : ℝ, c ^ 2 ∂gaussianSquareLaw := integral_congr_ae (hc.mono (fun w hw => congrArg (fun x : ℝ => x ^ 2) hw))
        _ = _ := by simp
    rw [gaussianSquareLaw_second, ← h1] at h2
    norm_num at h2

lemma gaussian_midpoint_parameter (t K : ℝ) (ht : 0 < t) (hK : 0 ≤ K) :
    (gaussianTail (Real.sqrt 2 * K) / 12) * (t * K / (2 * Real.sqrt 3) - 1) ≤
      averagedMidpointModulus (productSpan gaussianSquareLaw)
        (normSeminorm ℝ (productSpan gaussianSquareLaw)) t := by
  let q := gaussianTail (Real.sqrt 2 * K) / 12
  have hq : 0 ≤ q := div_nonneg (gaussianTail_nonneg _) (by norm_num)
  have hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂gaussianSquareLaw) := by
    rw [gaussianSquareLaw_second]
    positivity
  have hb := averaged_midpoint_from_scalar gaussianSquareLaw gaussianSquareLaw_hypotheses
    t (q * (t * K)) q ht.le (mul_nonneg hq (mul_nonneg ht.le hK)) hq hC
    (fun ι _ a b r hr => by
      have h := gaussian_square_scalar_excess a b K t r hK ht.le hr
      change q * (t * K * euclidSize a - r) ≤ _ at h
      nlinarith)
  rw [gaussianSquareLaw_second] at hb
  convert hb using 1
  ring

end IndependentProducts

namespace IndependentProducts

theorem main_gaussian_12 (t : ℝ) (ht : 0 < t) :
    gaussianTail (8 * Real.sqrt 6 / t) / 4 ≤
      averagedMidpointModulus (productSpan gaussianSquareLaw)
        (normSeminorm ℝ (productSpan gaussianSquareLaw)) t ∧
    0 < gaussianTail (8 * Real.sqrt 6 / t) / 4 := by
  constructor
  · have h := gaussian_midpoint_parameter t (8 * Real.sqrt 3 / t) ht (by positivity)
    have he : Real.sqrt 2 * (8 * Real.sqrt 3 / t) = 8 * Real.sqrt 6 / t := by
      rw [mul_div_assoc', ← mul_assoc, mul_comm (Real.sqrt 2) 8, mul_assoc,
        ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hr : t * (8 * Real.sqrt 3 / t) / (2 * Real.sqrt 3) - 1 = 3 := by
      field_simp
      ring
    rw [he, hr] at h
    convert h using 1
    ring
  · exact div_pos (gaussianTail_pos _) (by norm_num)

theorem main_gaussian_24 (t : ℝ) (ht : 0 < t) :
    gaussianTail (4 * Real.sqrt 2 * (2 + Real.sqrt 2) / t) / 8 ≤
      averagedMidpointModulus (productSpan gaussianSquareLaw)
        (normSeminorm ℝ (productSpan gaussianSquareLaw)) t ∧
    0 < gaussianTail (4 * Real.sqrt 2 * (2 + Real.sqrt 2) / t) / 8 := by
  constructor
  · have h := gaussian_midpoint_parameter t (4 * (2 + Real.sqrt 2) / t) ht (by positivity)
    have he : Real.sqrt 2 * (4 * (2 + Real.sqrt 2) / t) =
        4 * Real.sqrt 2 * (2 + Real.sqrt 2) / t := by ring
    rw [he] at h
    apply le_trans _ h
    have hr : t * (4 * (2 + Real.sqrt 2) / t) / (2 * Real.sqrt 3) - 1 ≥ 3 / 2 := by
      have hs2 : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have hs3 : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
      have ht' : t * (4 * (2 + Real.sqrt 2) / t) = 4 * (2 + Real.sqrt 2) := by field_simp
      rw [ht']
      rw [ge_iff_le, le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      nlinarith
    have hq := gaussianTail_nonneg (4 * Real.sqrt 2 * (2 + Real.sqrt 2) / t)
    nlinarith
  · exact div_pos (gaussianTail_pos _) (by norm_num)

end IndependentProducts

end

end OAI
