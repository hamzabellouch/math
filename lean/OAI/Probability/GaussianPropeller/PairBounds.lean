import OAI.Probability.GaussianPropeller.PairIntegral

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma orthonormal_triple_of_gram_pos (e u v : E) (he : ‖e‖ = 1)
    (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2) :
    ∃ (f : Fin 3 → E) (a b c : ℝ), Orthonormal ℝ f ∧
      f 0 = e ∧ 0 < a ∧ 0 < c ∧ u = a • f 1 ∧ v = b • f 1 + c • f 2 ∧
      (a*c)^2 = ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have hu : u ≠ 0 := by
    intro h
    simp [h] at hd
  have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let p : E := ‖u‖⁻¹ • u
  have hp : ‖p‖ = 1 := by simp [p, norm_smul, ha.ne']
  have hu' : u = ‖u‖ • p := by simp [p, smul_smul, ha.ne']
  have hep : ⟪e,p⟫ = 0 := by simp [p, inner_smul_right, heu]
  let b : ℝ := ⟪p,v⟫
  let w : E := v-b • p
  have hpw : ⟪p,w⟫ = 0 := by
    simp [w, b, inner_sub_right, inner_smul_right, hp]
  have hew : ⟪e,w⟫ = 0 := by simp [w, inner_sub_right, inner_smul_right, hev, hep]
  have hd' : ‖u‖^2*‖w‖^2 = ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
    have h : ‖w‖^2 = ‖v‖^2-b^2 := by
      rw [show w = v-b • p from rfl, norm_sub_sq_real, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs, hp, one_pow, mul_one, inner_smul_right,
        real_inner_comm p v]
      dsimp [b]
      ring
    rw [h, hu', inner_smul_left, starRingEnd_apply, star_trivial]
    change _ = ‖‖u‖ • p‖^2 * ‖v‖^2 - (‖u‖ * b)^2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hp, mul_one]
    ring
  have hw : w ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero] at hd'
    linarith only [hd, hd']
  have hc : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let q : E := ‖w‖⁻¹ • w
  have hq : ‖q‖ = 1 := by simp [q, norm_smul, hc.ne']
  have hw' : w = ‖w‖ • q := by simp [q, smul_smul, hc.ne']
  have hpq : ⟪p,q⟫ = 0 := by simp [q, inner_smul_right, hpw]
  have heq : ⟪e,q⟫ = 0 := by simp [q, inner_smul_right, hew]
  refine ⟨![e,p,q], ‖u‖, b, ‖w‖, ?_, rfl, ha, hc, hu', ?_, ?_⟩
  · constructor
    · intro i
      fin_cases i <;> simpa using (by assumption : ‖_‖ = 1)
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | exact (hij rfl).elim
        | exact hep
        | exact heq
        | exact hpq
        | exact (real_inner_comm e p).trans hep
        | exact (real_inner_comm e q).trans heq
        | exact (real_inner_comm p q).trans hpq
  · change v = b • p + ‖w‖ • q
    rw [← hw']
    dsimp [w]
    module
  · rw [mul_pow]
    exact hd'

end GaussianPropeller.PairGeometry

namespace GaussianPropeller.Pair

open GaussianPropeller.Analytic GaussianPropeller.PairIntegral GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma triangle_inner_bound (e u v : E) (he : ‖e‖ = 1)
    (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2) :
    ∫⁻ x, triangle ⟪e,x⟫ ⟪u,x⟫ ⟪v,x⟫ ∂stdGaussian E ≤
      ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*
        Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2))) := by
  obtain ⟨f,a,b,c,hf,he',ha,hc,hu,hv,hd'⟩ := orthonormal_triple_of_gram_pos e u v he heu hev hd
  have hm : Measurable (fun p : ℝ × ℝ × ℝ => triangle p.1 (a*p.2.1) (b*p.2.1+c*p.2.2)) :=
    measurable_triangle.comp (show Measurable (fun p : ℝ × ℝ × ℝ =>
      (p.1, a*p.2.1, b*p.2.1+c*p.2.2)) from by fun_prop)
  have hs : Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) = a*c := by
    rw [← hd', Real.sqrt_sq (mul_nonneg ha.le hc.le)]
  have hfun (x : E) : triangle ⟪e,x⟫ ⟪u,x⟫ ⟪v,x⟫ =
      triangle ⟪f 0,x⟫ (a*⟪f 1,x⟫) (b*⟪f 1,x⟫+c*⟪f 2,x⟫) := by
    rw [← he', hu, hv]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  calc
    _ = ∫⁻ t : ℝ, (∫⁻ w : ℝ, (∫⁻ y : ℝ, triangle t (a*w) (b*w+c*y)
        ∂gaussianReal 0 1) ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
      simp_rw [hfun]
      exact lintegral_orthonormal_triple f hf _ hm
    _ ≤ ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*a*c)) :=
      lintegral_triangle_gaussian b ha hc
    _ = _ := by
      rw [hs]
      congr 1
      congr 1
      ring

lemma setIntegral_inner_le_triangle (K : Set E) (hK : MeasurableSet K)
    (e u v : E) (he : ‖e‖ = 1) (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2)
    (huK : ∀ x ∈ K, ⟪u,x⟫ ≤ ⟪e,x⟫) (hvK : ∀ x ∈ K, ⟪v,x⟫ ≤ ⟪e,x⟫)
    (hu0 : ∫ x in K, ⟪u,x⟫ ∂stdGaussian E = 0)
    (hv0 : ∫ x in K, ⟪v,x⟫ ∂stdGaussian E = 0) :
    ∫ x in K, ⟪e,x⟫ ∂stdGaussian E ≤
      9/(2*Real.pi*Real.sqrt (2*Real.pi)*Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2)) := by
  let f : E → ℝ := K.indicator (fun x => ⟪e,x⟫+⟪u,x⟫+⟪v,x⟫)
  have hi (w : E) : Integrable (fun x => ⟪w,x⟫) (stdGaussian E) :=
    IsGaussian.integrable_dual _ (InnerProductSpace.toDual ℝ E w)
  have hfi : Integrable f (stdGaussian E) := ((hi e).add (hi u) |>.add (hi v)).indicator hK
  have hfint : ∫ x, f x ∂stdGaussian E = ∫ x in K, ⟪e,x⟫ ∂stdGaussian E := by
    rw [show f = K.indicator (fun x => ⟪e,x⟫+⟪u,x⟫+⟪v,x⟫) from rfl,
      integral_indicator hK, integral_add (f := fun x => ⟪e,x⟫+⟪u,x⟫)
        ((hi e).integrableOn.add (hi u).integrableOn) (hi v).integrableOn,
      integral_add (hi e).integrableOn (hi u).integrableOn, hu0, hv0]
    ring
  rw [← hfint]
  apply integral_le_of_lintegral_ofReal_le hfi (by positivity)
  apply le_trans _ (triangle_inner_bound e u v he heu hev hd)
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ K
  · simp only [f, Set.indicator_of_mem hx, triangle, ite_eq_left (huK x hx), ite_eq_left (hvK x hx)]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · simp only [f, Set.indicator_of_notMem hx, ENNReal.ofReal_zero, zero_le]

end GaussianPropeller.Pair

namespace GaussianPropeller.Pair

open GaussianPropeller.Analytic GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_inner_eq_inner_integral (K : Set E) (w : E) :
    ∫ x in K, ⟪w,x⟫ ∂stdGaussian E = ⟪w, ∫ x in K, x ∂stdGaussian E⟫ := by
  exact (InnerProductSpace.toDual ℝ E w).integral_comp_comm
    IsGaussian.integrable_id.integrableOn

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sqrt_gram_smul {u v : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (‖a • u‖^2*‖b • v‖^2-⟪a • u,b • v⟫^2) =
      a*b*Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [show (a*‖u‖)^2*(b*‖v‖)^2-(b*(a*⟪u,v⟫))^2 =
    (a*b)^2*(‖u‖^2*‖v‖^2-⟪u,v⟫^2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg ha hb)]

lemma centroid_residual_pair (K : Set E) (hK : MeasurableSet K)
    (z r s : E) (hz : z ≠ 0) (hzK : ∫ x in K, x ∂stdGaussian E = z)
    (hzr : ⟪z,r⟫ = 0) (hzs : ⟪z,s⟫ = 0)
    {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hrK : ∀ x ∈ K, ⟪r,x⟫ ≤ L*⟪z,x⟫)
    (hsK : ∀ x ∈ K, ⟪s,x⟫ ≤ M*⟪z,x⟫)
    (hd : 0 < ‖r‖^2*‖s‖^2-⟪r,s⟫^2) :
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      9*‖z‖*L*M/(2*Real.pi*Real.sqrt (2*Real.pi)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let e := ‖z‖⁻¹ • z
  let u := (L*‖z‖)⁻¹ • r
  let v := (M*‖z‖)⁻¹ • s
  have he : ‖e‖ = 1 := by simp [e, norm_smul, hn.ne']
  have heu : ⟪e,u⟫ = 0 := by simp [e,u,inner_smul_left,inner_smul_right,hzr]
  have hev : ⟪e,v⟫ = 0 := by simp [e,v,inner_smul_left,inner_smul_right,hzs]
  have huv : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
    dsimp [u,v]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hL hn)),
      abs_of_pos (inv_pos.mpr (mul_pos hM hn)), inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    nlinarith only [mul_pos (sq_pos_of_pos (inv_pos.mpr (mul_pos hL hn)))
      (mul_pos (sq_pos_of_pos (inv_pos.mpr (mul_pos hM hn))) hd)]
  have huK (x : E) (hx : x ∈ K) : ⟪u,x⟫ ≤ ⟪e,x⟫ := by
    simp only [u,e,inner_smul_left,starRingEnd_apply,star_trivial]
    have hh := mul_le_mul_of_nonneg_left (hrK x hx) (inv_nonneg.mpr (mul_pos hL hn).le)
    calc
      _ ≤ (L*‖z‖)⁻¹*(L*⟪z,x⟫) := hh
      _ = _ := by field_simp
  have hvK (x : E) (hx : x ∈ K) : ⟪v,x⟫ ≤ ⟪e,x⟫ := by
    simp only [v,e,inner_smul_left,starRingEnd_apply,star_trivial]
    have hh := mul_le_mul_of_nonneg_left (hsK x hx) (inv_nonneg.mpr (mul_pos hM hn).le)
    calc
      _ ≤ (M*‖z‖)⁻¹*(M*⟪z,x⟫) := hh
      _ = _ := by field_simp
  have hu0 : ∫ x in K, ⟪u,x⟫ ∂stdGaussian E = 0 := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [u, inner_smul_left, starRingEnd_apply, star_trivial,
      real_inner_comm z r, hzr, mul_zero]
  have hv0 : ∫ x in K, ⟪v,x⟫ ∂stdGaussian E = 0 := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [v, inner_smul_left, starRingEnd_apply, star_trivial,
      real_inner_comm z s, hzs, mul_zero]
  have heK : ∫ x in K, ⟪e,x⟫ ∂stdGaussian E = ‖z‖ := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [e,inner_smul_left,starRingEnd_apply,star_trivial,real_inner_self_eq_norm_sq]
    field_simp
  have hh := setIntegral_inner_le_triangle K hK e u v he heu hev huv huK hvK hu0 hv0
  rw [heK] at hh
  have hsqrt : Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) =
      (L*‖z‖)⁻¹*(M*‖z‖)⁻¹*Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) :=
    sqrt_gram_smul (by positivity) (by positivity)
  rw [hsqrt] at hh
  have hp : 0 < Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) := Real.sqrt_pos.mpr hd
  have hc : 0 < 2*Real.pi*Real.sqrt (2*Real.pi) := by positivity
  have hh' := (le_div_iff₀ (show 0 < 2*Real.pi*Real.sqrt (2*Real.pi)*
      ((L*‖z‖)⁻¹*(M*‖z‖)⁻¹*Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2)) by positivity)).mp hh
  apply (le_div_iff₀ hc).mpr
  have := mul_le_mul_of_nonneg_right hh' (show 0 ≤ ‖z‖*L*M by positivity)
  convert this using 1 <;> field_simp

end GaussianPropeller.Pair

end OAI
