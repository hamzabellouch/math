import Mathlib

namespace OAI

noncomputable section
open scoped RealInnerProductSpace Topology

namespace Problem358
namespace MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A finite maximum of affine functions, with slopes `y` and intercepts `c`. -/
def potential (y : ι → V) (c : ι → ℝ) (x : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪x, y i⟫ + c i)

theorem affine_le_potential (y : ι → V) (c : ι → ℝ) (x : V) (i : ι) :
    ⟪x, y i⟫ + c i ≤ potential y c x := by
  exact Finset.le_sup' (fun i => ⟪x, y i⟫ + c i) (Finset.mem_univ i)

theorem potential_le (y : ι → V) (c : ι → ℝ) (x : V) (a : ℝ)
    (h : ∀ i, ⟪x, y i⟫ + c i ≤ a) : potential y c x ≤ a := by
  exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => h i)

theorem affine_eq_potential (y : ι → V) (c : ι → ℝ) (x : V) (i : ι)
    (h : ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i) :
    potential y c x = ⟪x, y i⟫ + c i := by
  exact le_antisymm (potential_le y c x _ h) (affine_le_potential y c x i)

theorem supporting_inequality (y : ι → V) (c : ι → ℝ) (x z : V) (i : ι)
    (h : ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i) :
    potential y c x + ⟪z - x, y i⟫ ≤ potential y c z := by
  rw [affine_eq_potential y c x i h, inner_sub_left]
  linarith [affine_le_potential y c z i]

theorem convexOn_potential (y : ι → V) (c : ι → ℝ) :
    ConvexOn ℝ Set.univ (potential y c) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  apply potential_le
  intro i
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  have hx' := affine_le_potential y c x i
  have hz' := affine_le_potential y c z i
  have hc : a * c i + b * c i = c i := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hz' hb]

theorem potential_sub_le (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (x z : V) :
    potential y c x - potential y c z ≤ (L : ℝ) * ‖x - z‖ := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => ⟪x, y i⟫ + c i)
  change potential y c x = _ at hmax
  have hz := affine_le_potential y c z i
  have hinner : ⟪x - z, y i⟫ ≤ ‖x - z‖ * (L : ℝ) := by
    calc
      ⟪x - z, y i⟫ ≤ |⟪x - z, y i⟫| := le_abs_self _
      _ = ‖⟪x - z, y i⟫‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x - z‖ * ‖y i‖ := norm_inner_le_norm _ _
      _ ≤ ‖x - z‖ * (L : ℝ) := mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)
  rw [inner_sub_left] at hinner
  rw [hmax]
  nlinarith

theorem lipschitzWith_potential (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) : LipschitzWith L (potential y c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := potential_sub_le y c L hy z x
    rw [norm_sub_rev] at h
    linarith
  · exact potential_sub_le y c L hy x z

theorem continuous_potential (y : ι → V) (c : ι → ℝ) :
    Continuous (potential y c) := by
  have h := Continuous.finset_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun i _ => (continuous_id.inner continuous_const).add continuous_const
      : ∀ i ∈ (Finset.univ : Finset ι), Continuous (fun x : V => ⟪x, y i⟫ + c i))
  convert h using 1
  ext x
  simp [potential, Finset.sup'_apply]

/-- A strict active affine piece remains active in a neighborhood. -/
theorem eventuallyEq_affine_of_strict (y : ι → V) (c : ι → ℝ) (x : V) (i : ι)
    (h : ∀ j, j ≠ i → ⟪x, y j⟫ + c j < ⟪x, y i⟫ + c i) :
    potential y c =ᶠ[𝓝 x] (fun z => ⟪z, y i⟫ + c i) := by
  have hevent : ∀ᶠ z in 𝓝 x, ∀ j, ⟪z, y j⟫ + c j ≤ ⟪z, y i⟫ + c i := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall (fun _ => le_rfl)
    · have hj : Continuous (fun z : V => ⟪z, y j⟫ + c j) :=
        (continuous_id.inner continuous_const).add continuous_const
      have hi : Continuous (fun z : V => ⟪z, y i⟫ + c i) :=
        (continuous_id.inner continuous_const).add continuous_const
      exact (hj.continuousAt.eventually_lt hi.continuousAt (h j hji)).mono
        (fun _ hz => hz.le)
  exact hevent.mono (fun z hz => affine_eq_potential y c z i hz)

/-- At a strict active cell the derivative is its site's inner-product functional. -/
theorem hasFDerivAt_of_strict (y : ι → V) (c : ι → ℝ) (x : V) (i : ι)
    (h : ∀ j, j ≠ i → ⟪x, y j⟫ + c j < ⟪x, y i⟫ + c i) :
    HasFDerivAt (potential y c) (innerSL ℝ (y i)) x := by
  have haff : HasFDerivAt (fun z : V => ⟪z, y i⟫ + c i) (innerSL ℝ (y i)) x := by
    simpa only [innerSL_apply_apply, real_inner_comm] using
      (innerSL ℝ (y i)).hasFDerivAt.add_const (c i)
  exact haff.congr_of_eventuallyEq (eventuallyEq_affine_of_strict y c x i h)

end MaxPotential
end Problem358

end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace Topology

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem potential_intercept_sub_le (y : ι → V) (c b : ι → ℝ) (x : V) :
    potential y c x - potential y b x ≤ ‖c - b‖ := by
  have h : potential y c x ≤ potential y b x + ‖c - b‖ := by
    apply potential_le
    intro i
    have hi : c i - b i ≤ ‖c - b‖ := by
      calc
        c i - b i ≤ |c i - b i| := le_abs_self _
        _ = ‖(c - b) i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖c - b‖ := norm_le_pi_norm _ _
    linarith [affine_le_potential y b x i]
  linarith

theorem norm_potential_intercept_sub_le (y : ι → V) (c b : ι → ℝ) (x : V) :
    ‖potential y c x - potential y b x‖ ≤ ‖c - b‖ := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have h := potential_intercept_sub_le y b c x
    rw [norm_sub_rev] at h
    linarith
  · exact potential_intercept_sub_le y c b x

theorem lipschitzWith_intercepts (y : ι → V) (x : V) :
    LipschitzWith 1 (fun c : ι → ℝ => potential y c x) := by
  apply LipschitzWith.of_dist_le_mul
  intro c b
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    norm_potential_intercept_sub_le y c b x

theorem norm_potential_le (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (x : V) :
    ‖potential y c x‖ ≤ (L : ℝ) * ‖x‖ + ‖c‖ := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => ⟪x, y i⟫ + c i)
  change potential y c x = _ at hmax
  rw [hmax]
  calc
    ‖⟪x, y i⟫ + c i‖ ≤ ‖⟪x, y i⟫‖ + ‖c i‖ := norm_add_le _ _
    _ ≤ ‖x‖ * ‖y i‖ + ‖c i‖ := add_le_add (norm_inner_le_norm _ _) le_rfl
    _ ≤ ‖x‖ * (L : ℝ) + ‖c‖ := add_le_add
      (mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)) (norm_le_pi_norm _ _)
    _ = (L : ℝ) * ‖x‖ + ‖c‖ := by ring

variable [MeasurableSpace V] [OpensMeasurableSpace V]
variable (ρ : Measure V) [IsFiniteMeasure ρ]

theorem integrable_potential (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) :
    Integrable (potential y c) ρ := by
  apply ((hρ.const_mul (L : ℝ)).add (integrable_const ‖c‖)).mono'
    (continuous_potential y c).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_potential_le y c L hy)

omit [OpensMeasurableSpace V] in
/-- Integrating the potential preserves its uniform intercept continuity. -/
theorem norm_integral_potential_sub_le (y : ι → V) (c b : ι → ℝ)
    (hc : Integrable (potential y c) ρ) (hb : Integrable (potential y b) ρ) :
    ‖(∫ x, potential y c x ∂ρ) - ∫ x, potential y b x ∂ρ‖ ≤
      ‖c - b‖ * ρ.real Set.univ := by
  rw [← integral_sub hc hb]
  apply norm_integral_le_of_norm_le_const
  exact Filter.Eventually.of_forall (norm_potential_intercept_sub_le y c b)

variable [IsProbabilityMeasure ρ]

omit [OpensMeasurableSpace V] in
theorem lipschitzWith_integral_potential (y : ι → V)
    (hρ : ∀ c, Integrable (potential y c) ρ) :
    LipschitzWith 1 (fun c : ι → ℝ => ∫ x, potential y c x ∂ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro c b
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, probReal_univ,
    mul_one] using norm_integral_potential_sub_le ρ y c b (hρ c) (hρ b)

/-- The elementary coercivity estimate for each intercept coordinate. -/
theorem intercept_le_integral_potential (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) (i : ι) :
    c i ≤ (∫ x, potential y c x ∂ρ) + (L : ℝ) * ∫ x, ‖x‖ ∂ρ := by
  have hpoint : ∀ x : V, c i - (L : ℝ) * ‖x‖ ≤ potential y c x := by
    intro x
    have hi : -((L : ℝ) * ‖x‖) ≤ ⟪x, y i⟫ := by
      have hbound : ‖⟪x, y i⟫‖ ≤ (L : ℝ) * ‖x‖ := by
        calc
          ‖⟪x, y i⟫‖ ≤ ‖x‖ * ‖y i‖ := norm_inner_le_norm _ _
          _ ≤ ‖x‖ * (L : ℝ) := mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)
          _ = (L : ℝ) * ‖x‖ := mul_comm _ _
      rw [Real.norm_eq_abs] at hbound
      exact (abs_le.mp hbound).1
    linarith [affine_le_potential y c x i]
  have hint := integral_mono_ae
    ((integrable_const (c i)).sub (hρ.const_mul (L : ℝ)))
    (integrable_potential ρ y c L hy hρ) (Filter.Eventually.of_forall hpoint)
  change (∫ x, c i - (L : ℝ) * ‖x‖ ∂ρ) ≤ ∫ x, potential y c x ∂ρ at hint
  rw [integral_sub (integrable_const (c i)) (hρ.const_mul (L : ℝ)),
    integral_const, probReal_univ, one_smul, integral_const_mul] at hint
  linarith

end Problem358.MaxPotential

end

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Convexity in the intercept vector, as distinct from convexity in the source variable. -/
theorem convexOn_intercepts (y : ι → V) (x : V) :
    ConvexOn ℝ Set.univ (fun c => potential y c x) := by
  refine ⟨convex_univ, ?_⟩
  intro c hc d hd a b ha hb hab
  apply potential_le
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    ⟪x, y i⟫ + (a * c i + b * d i) =
        a * (⟪x, y i⟫ + c i) + b * (⟪x, y i⟫ + d i) := by
      have hinner : (a + b) * ⟪x, y i⟫ = ⟪x, y i⟫ := by rw [hab, one_mul]
      nlinarith [hinner]
    _ ≤ a * potential y c x + b * potential y d x :=
      add_le_add
        (mul_le_mul_of_nonneg_left (affine_le_potential y c x i) ha)
        (mul_le_mul_of_nonneg_left (affine_le_potential y d x i) hb)

variable [MeasurableSpace V]

theorem convexOn_integral_potential (ρ : Measure V) (y : ι → V)
    (hint : ∀ c, Integrable (potential y c) ρ) :
    ConvexOn ℝ Set.univ (fun c => ∫ x, potential y c x ∂ρ) := by
  refine ⟨convex_univ, ?_⟩
  intro c hc d hd a b ha hb hab
  have hpoint (x : V) := (convexOn_intercepts y x).2 hc hd ha hb hab
  have hle := integral_mono (hint (a • c + b • d))
    (((hint c).const_mul a).add ((hint d).const_mul b)) hpoint
  simpa only [Pi.add_apply, integral_add ((hint c).const_mul a)
    ((hint d).const_mul b), integral_const_mul, smul_eq_mul] using hle

/-- The complete normalized-cell variational objective is convex. -/
theorem convexOn_integral_potential_sub_weighted_sum
    (ρ : Measure V) (y : ι → V) (m : ι → ℝ)
    (hint : ∀ c, Integrable (potential y c) ρ) :
    ConvexOn ℝ Set.univ
      (fun c => (∫ x, potential y c x ∂ρ) - ∑ i, m i * c i) := by
  refine ⟨convex_univ, ?_⟩
  intro c hc d hd a b ha hb hab
  have hconv := (convexOn_integral_potential ρ y hint).2 hc hd ha hb hab
  have hlin : (∑ i, m i * (a • c + b • d) i) =
      a * (∑ i, m i * c i) + b * (∑ i, m i * d i) := by
    calc
      (∑ i, m i * (a • c + b • d) i) =
          ∑ i, (a * (m i * c i) + b * (m i * d i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = a * (∑ i, m i * c i) + b * (∑ i, m i * d i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  simp only [smul_eq_mul] at hconv ⊢
  rw [hlin]
  linarith

end Problem358.MaxPotential

end

/-! Uniqueness of finite affine intercepts from connected full-support sources.
This route uses finite-range continuity, not differentiability of moving cells. -/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators Topology

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V]

omit [InnerProductSpace ℝ V] in
/-- A continuous function with finite essential range is constant on every
connected subset of the measure's support. -/
theorem eqOn_of_finite_ae_range (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    {f : V → ℝ} (hf : Continuous f) {A : Set ℝ} (hA : A.Finite)
    (hae : ∀ᵐ x ∂ρ, f x ∈ A) {x z : V} (hx : x ∈ K) (hz : z ∈ K) :
    f x = f z := by
  have hs : ρ.support ⊆ f ⁻¹' A :=
    Measure.support_subset_of_isClosed (hA.isClosed.preimage hf) hae
  have hi : (f '' K).Finite := hA.subset (by
    rintro _ ⟨w, hw, rfl⟩
    exact hs (hKs hw))
  have hc := hK.image f hf.continuousOn
  have hh : (f '' K).Subsingleton := by
    by_contra h
    exact hi.not_infinite (hc.infinite_of_nontrivial (not_subsingleton_iff.mp h))
  exact hh (mem_image_of_mem f hx) (mem_image_of_mem f hz)

/-- If the same positive-mass selector is active for two finite affine potentials,
then their intercept difference is constant on the index set. -/
theorem intercept_sub_eq_of_common_selector (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    (hKae : ∀ᵐ x ∂ρ, x ∈ K) (y : ι → V) (c b : ι → ℝ) (k : V → ι)
    (hc : ∀ᵐ x ∂ρ, potential y c x = ⟪x, y (k x)⟫ + c (k x))
    (hb : ∀ᵐ x ∂ρ, potential y b x = ⟪x, y (k x)⟫ + b (k x))
    (hpos : ∀ i, ρ {x | k x = i} ≠ 0) (i j : ι) :
    c i - b i = c j - b j := by
  have heq : ∀ᵐ x ∂ρ, potential y c x - potential y b x = c (k x) - b (k x) := by
    filter_upwards [hc, hb] with x hcx hbx
    rw [hcx, hbx]
    ring
  have hdata : ∀ᵐ x ∂ρ, x ∈ K ∧
      potential y c x - potential y b x = c (k x) - b (k x) := hKae.and heq
  obtain ⟨x, hxi, hxK, hxeq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hpos i)
    (ae_restrict_of_ae hdata)
  obtain ⟨z, hzj, hzK, hzeq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hpos j)
    (ae_restrict_of_ae hdata)
  change k x = i at hxi
  change k z = j at hzj
  have hrange : ∀ᵐ x ∂ρ, potential y c x - potential y b x ∈
      Set.range (fun i => c i - b i) := heq.mono (fun x hx => ⟨k x, hx.symm⟩)
  have hconst := eqOn_of_finite_ae_range ρ hK hKs
    ((continuous_potential y c).sub (continuous_potential y b))
    (Set.finite_range (fun i => c i - b i)) hrange hxK hzK
  simpa only [Pi.sub_apply, hxeq, hzeq, hxi, hzj] using hconst

/-- Weighted normalization removes the common additive intercept constant. -/
theorem intercept_eq_of_common_selector (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    (hKae : ∀ᵐ x ∂ρ, x ∈ K) (y : ι → V) (c b m : ι → ℝ) (k : V → ι)
    (hsum : ∑ i, m i = 1) (hc0 : ∑ i, m i * c i = 0)
    (hb0 : ∑ i, m i * b i = 0)
    (hc : ∀ᵐ x ∂ρ, potential y c x = ⟪x, y (k x)⟫ + c (k x))
    (hb : ∀ᵐ x ∂ρ, potential y b x = ⟪x, y (k x)⟫ + b (k x))
    (hpos : ∀ i, ρ {x | k x = i} ≠ 0) : c = b := by
  funext i
  have hconst := intercept_sub_eq_of_common_selector ρ hK hKs hKae y c b k hc hb hpos
  have hz : (∑ j, m j * (c j - b j)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, hc0, hb0, sub_self]
  have hi : (∑ j, m j * (c j - b j)) = c i - b i := by
    calc
      (∑ j, m j * (c j - b j)) = ∑ j, m j * (c i - b i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hconst j i]
      _ = c i - b i := by rw [← Finset.sum_mul, hsum, one_mul]
  exact sub_eq_zero.mp (hi.symm.trans hz)

omit [MeasurableSpace V] in
/-- Convexity of the maximum in its intercepts, at the midpoint. -/
theorem potential_midpoint_le (y : ι → V) (c b : ι → ℝ) (x : V) :
    potential y (fun i => (c i + b i) / 2) x ≤
      (potential y c x + potential y b x) / 2 := by
  apply potential_le
  intro i
  linarith [affine_le_potential y c x i, affine_le_potential y b x i]

omit [MeasurableSpace V] in
/-- Equality in midpoint convexity forces a strict active index at one endpoint
also to be active at the other endpoint. -/
theorem active_of_midpoint_eq (y : ι → V) (c b : ι → ℝ) (x : V) (k : ι)
    (hstrict : ∀ j, j ≠ k → ⟪x, y j⟫ + c j < ⟪x, y k⟫ + c k)
    (heq : potential y (fun i => (c i + b i) / 2) x =
      (potential y c x + potential y b x) / 2) :
    potential y b x = ⟪x, y k⟫ + b k := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j => ⟪x, y j⟫ + (c j + b j) / 2)
  change potential y (fun i => (c i + b i) / 2) x = _ at hj
  have hc := affine_le_potential y c x j
  have hb := affine_le_potential y b x j
  have hcj : potential y c x = ⟪x, y j⟫ + c j := by linarith
  have hbj : potential y b x = ⟪x, y j⟫ + b j := by linarith
  have hjk : j = k := by
    by_contra h
    have hlt := hstrict j h
    have hk := affine_le_potential y c x k
    linarith
  simpa only [hjk] using hbj

/-- Integrated midpoint equality upgrades a strict selector at the first endpoint
to a common almost-everywhere selector. -/
theorem ae_common_selector_of_integral_midpoint_eq (ρ : Measure V)
    (y : ι → V) (c b : ι → ℝ) (k : V → ι)
    (hc : Integrable (potential y c) ρ) (hb : Integrable (potential y b) ρ)
    (hm : Integrable (potential y (fun i => (c i + b i) / 2)) ρ)
    (hstrict : ∀ᵐ x ∂ρ, ∀ j, j ≠ k x →
      ⟪x, y j⟫ + c j < ⟪x, y (k x)⟫ + c (k x))
    (heq : (∫ x, potential y (fun i => (c i + b i) / 2) x ∂ρ) =
      ((∫ x, potential y c x ∂ρ) + ∫ x, potential y b x ∂ρ) / 2) :
    ∀ᵐ x ∂ρ, potential y b x = ⟪x, y (k x)⟫ + b (k x) := by
  have hae : (fun x => potential y (fun i => (c i + b i) / 2) x) =ᵐ[ρ]
      (fun x => (potential y c x + potential y b x) / 2) := by
    apply (integral_eq_iff_of_ae_le hm ((hc.add hb).div_const 2)
      (Filter.Eventually.of_forall (potential_midpoint_le y c b))).mp
    simpa only [integral_div, Pi.add_apply, integral_add hc hb] using heq
  filter_upwards [hstrict, hae] with x hx he
  exact active_of_midpoint_eq y c b x (k x) hx he

/-- Two normalized minimizers have equality in integrated midpoint convexity. -/
theorem integral_midpoint_eq_of_minimizers (ρ : Measure V)
    (y : ι → V) (c b m : ι → ℝ)
    (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ)
    (hcmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y a x ∂ρ)
    (hbmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y b x ∂ρ) ≤ ∫ x, potential y a x ∂ρ) :
    (∫ x, potential y (fun i => (c i + b i) / 2) x ∂ρ) =
      ((∫ x, potential y c x ∂ρ) + ∫ x, potential y b x ∂ρ) / 2 := by
  have hm0 : (∑ i, m i * ((c i + b i) / 2)) = 0 := by
    calc
      (∑ i, m i * ((c i + b i) / 2)) =
          ((∑ i, m i * c i) + ∑ i, m i * b i) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hc0, hb0]; norm_num
  have hlo := hcmin (fun i => (c i + b i) / 2) hm0
  have hcb := hcmin b hb0
  have hbc := hbmin c hc0
  have hup := integral_mono (hint (fun i => (c i + b i) / 2))
    (((hint c).add (hint b)).div_const 2) (potential_midpoint_le y c b)
  simp only [integral_div, Pi.add_apply, integral_add (hint c) (hint b)] at hup
  linarith

/-- Uniqueness of normalized intercept minimizers.  The only geometric inputs are
connected full support and almost-everywhere strictness of the chosen cells.
No cell boundary differentiability or implicit-function theorem is required. -/
theorem normalized_minimizer_unique (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    (hKae : ∀ᵐ x ∂ρ, x ∈ K) (y : ι → V) (c b m : ι → ℝ) (k : V → ι)
    (hsum : ∑ i, m i = 1) (hc0 : ∑ i, m i * c i = 0)
    (hb0 : ∑ i, m i * b i = 0)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ)
    (hcmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y a x ∂ρ)
    (hbmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y b x ∂ρ) ≤ ∫ x, potential y a x ∂ρ)
    (hstrict : ∀ᵐ x ∂ρ, ∀ j, j ≠ k x →
      ⟪x, y j⟫ + c j < ⟪x, y (k x)⟫ + c (k x))
    (hpos : ∀ i, ρ {x | k x = i} ≠ 0) : c = b := by
  have hc : ∀ᵐ x ∂ρ, potential y c x = ⟪x, y (k x)⟫ + c (k x) := by
    filter_upwards [hstrict] with x hx
    apply affine_eq_potential
    intro j
    by_cases hj : j = k x
    · simp only [hj, le_refl]
    · exact (hx j hj).le
  have hb := ae_common_selector_of_integral_midpoint_eq ρ y c b k
    (hint c) (hint b) (hint _) hstrict
    (integral_midpoint_eq_of_minimizers ρ y c b m hc0 hb0 hint hcmin hbmin)
  exact intercept_eq_of_common_selector ρ hK hKs hKae y c b m k hsum hc0 hb0 hc hb hpos

end Problem358.MaxPotential

end

end OAI
