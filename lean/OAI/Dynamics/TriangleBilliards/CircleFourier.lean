import OAI.Dynamics.TriangleBilliards.SmoothingGenerators

namespace OAI

universe uA uH

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

/-! Strongly continuous unitary circle actions and their genuine Fourier
projections. This supplies the angular Hilbert-space calculus, not a new
assumption on a billiard-invariant field. -/
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {T : ℝ} [Fact (0 < T)]

structure CircleAction (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : ℝ) where
  act : AddCircle T → H →ₗᵢ[ℂ] H
  zero : ∀ u, act 0 u = u
  add : ∀ θ φ u, act (θ + φ) u = act θ (act φ u)
  continuous : ∀ u, Continuous (fun θ => act θ u)

namespace CircleAction
variable (V : CircleAction H T)

omit [Fact (0 < T)] in
lemma act_neg (θ : AddCircle T) (u : H) : V.act (-θ) (V.act θ u) = u := by
  rw [← V.add, neg_add_cancel, V.zero]

omit [Fact (0 < T)] in
lemma adjoint (θ : AddCircle T) (u v : H) :
    inner ℂ (V.act θ u) v = inner ℂ u (V.act (-θ) v) := by
  rw [← (V.act θ).inner_map_map u (V.act (-θ) v), ← V.add, add_neg_cancel, V.zero]

omit [Fact (0 < T)] in
lemma weighted_continuous (j : ℤ) (u : H) :
    Continuous (fun θ : AddCircle T => fourier (-j) θ • V.act θ u) :=
  (fourier (-j)).continuous.smul (V.continuous u)

lemma weighted_integrable (j : ℤ) (u : H) :
    Integrable (fun θ : AddCircle T => fourier (-j) θ • V.act θ u) AddCircle.haarAddCircle :=
  (V.weighted_continuous j u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [Fact (0 < T)] in
lemma fourier_norm_apply (j : ℤ) (θ : AddCircle T) : ‖fourier j θ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

lemma coeff_norm_bound (j : ℤ) (u : H) :
    ‖fourierCoeff (fun θ => V.act θ u) j‖ ≤ ‖u‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (f := fun θ : AddCircle T => fourier (-j) θ • V.act θ u)
    (Eventually.of_forall fun θ => by
      rw [norm_smul, fourier_norm_apply, (V.act θ).norm_map, one_mul])
  simpa [Measure.real, fourierCoeff] using h

variable [CompleteSpace H]

def projection (j : ℤ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun u => fourierCoeff (fun θ => V.act θ u) j
      map_add' := fun u v => by
        change (∫ θ, fourier (-j) θ • V.act θ (u+v) ∂AddCircle.haarAddCircle) = _
        simp_rw [map_add, smul_add]
        exact integral_add (V.weighted_integrable j u) (V.weighted_integrable j v)
      map_smul' := fun c u => by
        change (∫ θ, fourier (-j) θ • V.act θ (c • u) ∂AddCircle.haarAddCircle) = _
        simp_rw [map_smul, smul_comm (fourier (-j) _) c]
        exact integral_smul c _ }
    1 (fun u => by simpa using V.coeff_norm_bound j u)

omit [CompleteSpace H] in
lemma projection_apply (j : ℤ) (u : H) :
    V.projection j u = ∫ θ : AddCircle T, fourier (-j) θ • V.act θ u ∂AddCircle.haarAddCircle := rfl

omit [CompleteSpace H] in
lemma projection_norm_le (j : ℤ) (u : H) : ‖V.projection j u‖ ≤ ‖u‖ :=
  V.coeff_norm_bound j u

omit [Fact (0 < T)] in
lemma fourier_arg_add (j : ℤ) (θ φ : AddCircle T) :
    fourier j (θ + φ) = fourier j θ * fourier j φ := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

omit [Fact (0 < T)] in
lemma fourier_arg_neg (j : ℤ) (θ : AddCircle T) :
    fourier j (-θ) = conj (fourier j θ) := by
  simp only [fourier_apply, smul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

omit [Fact (0 < T)] in
lemma fourier_neg_mul_self (j : ℤ) (θ : AddCircle T) :
    fourier (-j) θ * fourier j θ = 1 := by
  rw [← fourier_add, neg_add_cancel, fourier_zero]

lemma projection_eigen (j : ℤ) (u : H) (φ : AddCircle T) :
    V.act φ (V.projection j u) = fourier j φ • V.projection j u := by
  rw [projection_apply]
  change (V.act φ).toContinuousLinearMap (∫ θ : AddCircle T, fourier (-j) θ • V.act θ u ∂AddCircle.haarAddCircle) = _
  rw [← (V.act φ).toContinuousLinearMap.integral_comp_comm (V.weighted_integrable j u)]
  change (∫ θ, V.act φ (fourier (-j) θ • V.act θ u) ∂AddCircle.haarAddCircle) = _
  simp_rw [map_smul, ← V.add]
  rw [← integral_add_left_eq_self (μ := AddCircle.haarAddCircle)
    (fun θ => fourier (-j) θ • V.act θ u) φ, ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    change fourier (-j) θ • V.act (φ+θ) u = fourier j φ • (fourier (-j) (φ+θ) • V.act (φ+θ) u)
    rw [fourier_arg_add, smul_smul, ← mul_assoc, mul_comm (fourier j φ),
      fourier_neg_mul_self, one_mul]

lemma integral_inner_left {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f : A → H} (hf : Integrable f μ) (v : H) :
    (∫ x, inner ℂ (f x) v ∂μ) = inner ℂ (∫ x, f x ∂μ) v := by
  simp_rw [← inner_conj_symm (𝕜 := ℂ) (f _) v]
  rw [integral_conj, integral_inner hf, inner_conj_symm]

lemma projection_adjoint (j : ℤ) (u v : H) :
    inner ℂ (V.projection j u) v = inner ℂ u (V.projection j v) := by
  rw [projection_apply, projection_apply, ← integral_inner_left (V.weighted_integrable j u),
    ← integral_inner (V.weighted_integrable j v)]
  rw [← integral_neg_eq_self (fun θ : AddCircle T =>
    inner ℂ u (fourier (-j) θ • V.act θ v)) AddCircle.haarAddCircle]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    change inner ℂ ((fourier (-j) θ : ℂ) • V.act θ u) v =
      inner ℂ u ((fourier (-j) (-θ) : ℂ) • V.act (-θ) v)
    rw [inner_smul_left, inner_smul_right, V.adjoint, fourier_arg_neg]

lemma projection_of_eigen {u : H} {k : ℤ}
    (hu : ∀ θ : AddCircle T, V.act θ u = fourier k θ • u) (j : ℤ) :
    V.projection j u = if j = k then u else 0 := by
  rw [projection_apply]
  simp_rw [hu, smul_smul]
  rw [integral_smul_const]
  have he : (∫ θ : AddCircle T, fourier (-j) θ * fourier k θ ∂AddCircle.haarAddCircle) =
      if j = k then (1 : ℂ) else 0 := by
    change fourierCoeff (fourier k) j = _
    rw [fourierCoeff_fourier]
    simp [Pi.single_apply, eq_comm]
  rw [he]
  split_ifs <;> simp

lemma projection_mul (j k : ℤ) (u : H) :
    V.projection j (V.projection k u) = if j = k then V.projection k u else 0 :=
  V.projection_of_eigen (V.projection_eigen k u) j

lemma projection_idem (j : ℤ) (u : H) :
    V.projection j (V.projection j u) = V.projection j u := by
  rw [projection_mul, ite_eq_left rfl]

lemma projection_orthogonal {j k : ℤ} (hjk : j ≠ k) (u v : H) :
    inner ℂ (V.projection j u) (V.projection k v) = 0 := by
  rw [V.projection_adjoint, V.projection_mul, ite_eq_right hjk, inner_zero_right]

/-- The closed Fourier eigenspace, presented as the fixed space of the
proved bounded projection rather than an assumed orthogonal decomposition. -/
def mode (j : ℤ) : Submodule ℂ H :=
  ((V.projection j).toLinearMap - LinearMap.id).ker

omit [CompleteSpace H] in
lemma mem_mode (j : ℤ) (u : H) : u ∈ V.mode j ↔ V.projection j u = u := by
  change V.projection j u - u = 0 ↔ _
  exact sub_eq_zero

lemma projection_mem_mode (j : ℤ) (u : H) : V.projection j u ∈ V.mode j :=
  (V.mem_mode j _).mpr (V.projection_idem j u)

lemma mode_orthogonal : OrthogonalFamily ℂ (fun j => V.mode j)
    (fun j => (V.mode j).subtypeₗᵢ) := by
  intro j k hjk u v
  change inner ℂ (u : H) (v : H) = 0
  rw [← (V.mem_mode j u).mp u.property, ← (V.mem_mode k v).mp v.property]
  exact V.projection_orthogonal hjk u v

lemma projection_norm_sum (u : H) (s : Finset ℤ) :
    ‖∑ j ∈ s, V.projection j u‖ ^ 2 = ∑ j ∈ s, ‖V.projection j u‖ ^ 2 := by
  exact V.mode_orthogonal.norm_sum (fun j => ⟨V.projection j u, V.projection_mem_mode j u⟩) s

lemma projection_inner_self (j : ℤ) (u : H) :
    inner ℂ u (V.projection j u) = (‖V.projection j u‖ ^ 2 : ℝ) := by
  rw [← V.projection_idem j u, ← V.projection_adjoint j u]
  rw [V.projection_idem]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]

lemma bessel (u : H) (s : Finset ℤ) :
    ∑ j ∈ s, ‖V.projection j u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hs := norm_sub_sq (𝕜 := ℂ) u (∑ j ∈ s, V.projection j u)
  rw [V.projection_norm_sum] at hs
  have hi : (inner ℂ u (∑ j ∈ s, V.projection j u)).re =
      ∑ j ∈ s, ‖V.projection j u‖ ^ 2 := by
    rw [inner_sum]
    simp_rw [V.projection_inner_self]
    simp only [Complex.re_sum, Complex.ofReal_re]
  change ‖u - ∑ j ∈ s, V.projection j u‖ ^ 2 =
    ‖u‖ ^ 2 - 2 * (inner ℂ u (∑ j ∈ s, V.projection j u)).re + _ at hs
  rw [hi] at hs
  nlinarith [sq_nonneg ‖u - ∑ j ∈ s, V.projection j u‖]

lemma summable_norm_projection (u : H) : Summable (fun j : ℤ => ‖V.projection j u‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (V.bessel u)

lemma summable_projection (u : H) : Summable (fun j : ℤ => V.projection j u) :=
  (V.mode_orthogonal.summable_iff_norm_sq_summable
    (fun j => ⟨V.projection j u, V.projection_mem_mode j u⟩)).mpr (V.summable_norm_projection u)

lemma scalar_coeff (u v : H) (j : ℤ) :
    fourierCoeff (fun θ : AddCircle T => inner ℂ v (V.act θ u)) j =
      inner ℂ v (V.projection j u) := by
  rw [projection_apply, ← integral_inner (V.weighted_integrable j u)]
  unfold fourierCoeff
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by simp only [inner_smul_right, smul_eq_mul]

lemma eq_zero_of_projections_zero {u : H} (hu : ∀ j, V.projection j u = 0) : u = 0 := by
  let f : AddCircle T → ℂ := fun θ => inner ℂ u (V.act θ u)
  have hc : Continuous f := continuous_const.inner (V.continuous u)
  have hm : MemLp f 2 AddCircle.haarAddCircle := hc.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hz : hm.toLp f = 0 := by
    apply fourierBasis.repr.injective
    ext j
    rw [fourierBasis_repr, congrFun (fourierCoeff_congr_ae hm.coeFn_toLp) j,
      V.scalar_coeff, hu]
    simp
  have hae : f =ᵐ[AddCircle.haarAddCircle] 0 := hm.coeFn_toLp.symm.trans (by rw [hz]; exact Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle)
  have he : f = 0 := (hc.ae_eq_iff_eq AddCircle.haarAddCircle continuous_const).mp hae
  have hzero := congrFun he 0
  change inner ℂ u (V.act 0 u) = 0 at hzero
  rw [V.zero] at hzero
  exact inner_self_eq_zero.mp hzero

lemma projections_ext {u v : H} (h : ∀ j, V.projection j u = V.projection j v) : u = v := by
  apply sub_eq_zero.mp
  apply V.eq_zero_of_projections_zero
  intro j
  rw [map_sub, h j, sub_self]

lemma tsum_projection (u : H) : ∑' j : ℤ, V.projection j u = u := by
  apply V.projections_ext
  intro j
  rw [(V.projection j).map_tsum (V.summable_projection u)]
  rw [tsum_eq_single j]
  · exact V.projection_idem j u
  · intro k hk
    rw [V.projection_mul, ite_eq_right (Ne.symm hk)]

lemma hasSum_projection (u : H) : HasSum (fun j : ℤ => V.projection j u) u := by
  convert (V.summable_projection u).hasSum using 1
  exact (V.tsum_projection u).symm

/-- An injective sequence of modes escapes every fixed vector strongly. -/
lemma projection_escape {φ : ℕ → ℤ} (hφ : Function.Injective φ) (u : H) :
    Tendsto (fun n => V.projection (φ n) u) atTop (𝓝 0) := by
  exact ((V.summable_projection u).tendsto_cofinite_zero.comp
    hφ.tendsto_cofinite).mono_left atTop_le_cofinite

/-- Uniformly bounded remainder fields of escaping modes converge weakly
in the scalar inner-product sense. No norm convergence of the remainders
is claimed or needed in the endpoint equation. -/
lemma bounded_modes_escape {φ : ℕ → ℤ} (hφ : Function.Injective φ)
    (r : ℕ → H) {C : ℝ} (hC : ∀ n, ‖r n‖ ≤ C)
    (hr : ∀ n, V.projection (φ n) (r n) = r n) (u : H) :
    Tendsto (fun n => inner ℂ u (r n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => ‖V.projection (φ n) u‖ * C) atTop (𝓝 0) := by
    simpa using ((V.projection_escape hφ u).norm.mul_const C)
  apply squeeze_zero_norm _ hn
  intro n
  rw [← hr n, ← V.projection_adjoint]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))

lemma parity_index_injective (m : ℤ) : Function.Injective (fun n : ℕ => m + 2 * (n : ℤ)) := by
  intro a b h
  change m + 2 * (a : ℤ) = m + 2 * (b : ℤ) at h
  omega

lemma parity_summable (m : ℤ) (u : H) :
    Summable (fun n : ℕ => V.projection (m + 2 * (n : ℤ)) u) :=
  (V.summable_projection u).comp_injective (parity_index_injective m)

/-- The genuine one-sided parity tail of the angular decomposition. -/
def parityTail (m : ℤ) (u : H) : H := ∑' n : ℕ, V.projection (m + 2 * (n : ℤ)) u

lemma parityTail_convergence (m : ℤ) (u : H) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, V.projection (m + 2 * (n : ℤ)) u)
      atTop (𝓝 (V.parityTail m u)) :=
  (V.parity_summable m u).hasSum.tendsto_sum_nat

lemma parityTail_projection_inside (m : ℤ) (u : H) (n : ℕ) :
    V.projection (m + 2 * (n : ℤ)) (V.parityTail m u) =
      V.projection (m + 2 * (n : ℤ)) u := by
  unfold parityTail
  rw [(V.projection _).map_tsum (V.parity_summable m u), tsum_eq_single n]
  · exact V.projection_idem _ u
  · intro k hk
    rw [V.projection_mul, ite_eq_right]
    exact fun h => hk ((parity_index_injective m) h.symm)

lemma parityTail_projection_outside (m : ℤ) (u : H) (j : ℤ)
    (hj : ∀ n : ℕ, j ≠ m + 2 * (n : ℤ)) : V.projection j (V.parityTail m u) = 0 := by
  unfold parityTail
  rw [(V.projection j).map_tsum (V.parity_summable m u)]
  simp only [V.projection_mul, ite_eq_right (hj _), tsum_zero]

end CircleAction
end TriangularBilliards.Analysis

end
end
end
end
end
end
end

end OAI
