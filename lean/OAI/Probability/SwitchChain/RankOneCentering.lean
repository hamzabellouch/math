import OAI.Probability.SwitchChain.RankOneInteraction

namespace OAI

noncomputable section

namespace Problem315.RankOneInteraction

def constantProjection {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) : E →ₗ[ℝ] E where
  toFun z := inner ℝ z e • e
  map_add' z w := by simp [inner_add_left, add_smul]
  map_smul' c z := by simp [real_inner_smul_left, smul_smul]

@[simp] theorem constantProjection_apply
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e z : E) : constantProjection e z = inner ℝ z e • e := rfl

theorem inner_constant_left
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e z w : E) : inner ℝ (constantProjection e z) w = inner ℝ z e * inner ℝ w e := by
  simp only [constantProjection_apply, real_inner_smul_left]
  rw [real_inner_comm w e]

theorem inner_constant_right
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e z w : E) : inner ℝ z (constantProjection e w) = inner ℝ z e * inner ℝ w e := by
  simp only [constantProjection_apply, real_inner_smul_right]
  ring

theorem constantProjection_symmetric
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) : (constantProjection e).IsSymmetric := by
  intro z w
  rw [inner_constant_left, inner_constant_right]

theorem subtract_constant_idempotent
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hPi : ∀ z, P (P z) = P z)
    (e : E) (hee : inner ℝ e e = 1) (hPe : P e = e) (z : E) :
    (P - constantProjection e) ((P - constantProjection e) z) =
      (P - constantProjection e) z := by
  have hPC : P (constantProjection e z) = constantProjection e z := by
    simp only [constantProjection_apply, map_smul, hPe]
  have hCP : constantProjection e (P z) = constantProjection e z := by
    simp only [constantProjection_apply]
    rw [hPs, hPe]
  have hCC : constantProjection e (constantProjection e z) = constantProjection e z := by
    simp only [constantProjection_apply, real_inner_smul_left, hee, mul_one]
  simp only [LinearMap.sub_apply, map_sub, hPi, hPC, hCP, hCC]
  module

theorem disjoint_interaction_with_constants
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (e u v : E) (c : ℝ) (hc : 1 - c ^ 2 ≠ 0)
    (hee : inner ℝ e e = 1) (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1)
    (hue : inner ℝ u e = 0) (hve : inner ℝ v e = 0)
    (hPe : P e = e) (hQe : Q e = e) (hPu : P u = u) (hQv : Q v = v)
    (hcov : ∀ z w, inner ℝ (P z) (Q w) =
      inner ℝ z e * inner ℝ w e + c * inner ℝ z u * inner ℝ w v)
    (hGe : G e = 0) (hRe : R e = 0) (hSe : S e = 0)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRline : R (v - c • u) = v - c • u)
    (hSline : S (u - c • v) = u - c • v)
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * inner ℝ (f - P f) (f - Q f) := by
  let C := constantProjection e
  let P₀ := P - C
  let Q₀ := Q - C
  let f₀ := f - inner ℝ f e • e
  have hCs : C.IsSymmetric := constantProjection_symmetric e
  have hP₀s : P₀.IsSymmetric := hPs.sub hCs
  have hQ₀s : Q₀.IsSymmetric := hQs.sub hCs
  have hP₀i : ∀ z, P₀ (P₀ z) = P₀ z := subtract_constant_idempotent P hPs hPi e hee hPe
  have hQ₀i : ∀ z, Q₀ (Q₀ z) = Q₀ z := subtract_constant_idempotent Q hQs hQi e hee hQe
  have hPmean (z : E) : inner ℝ (P z) e = inner ℝ z e := by rw [hPs, hPe]
  have hQmean (z : E) : inner ℝ (Q z) e = inner ℝ z e := by rw [hQs, hQe]
  have hCmean (z : E) : inner ℝ (C z) e = inner ℝ z e := by
    simp only [C, constantProjection_apply, real_inner_smul_left, hee, mul_one]
  have hcov₀ : ∀ z w, inner ℝ (P₀ z) (Q₀ w) = c * inner ℝ z u * inner ℝ w v := by
    intro z w
    change inner ℝ (P z - C z) (Q w - C w) = _
    simp only [inner_sub_left, inner_sub_right]
    rw [hcov, show inner ℝ (P z) (C w) = inner ℝ (P z) e * inner ℝ w e from
      inner_constant_right e (P z) w,
      show inner ℝ (C z) (Q w) = inner ℝ z e * inner ℝ (Q w) e from
      inner_constant_left e z (Q w),
      show inner ℝ (C z) (C w) = inner ℝ z e * inner ℝ (C w) e from
      inner_constant_left e z (C w), hPmean, hQmean, hCmean]
    ring
  have hP₀u : P₀ u = u := by
    simp only [P₀, C, LinearMap.sub_apply, constantProjection_apply, hPu, hue, zero_smul, sub_zero]
  have hQ₀v : Q₀ v = v := by
    simp only [Q₀, C, LinearMap.sub_apply, constantProjection_apply, hQv, hve, zero_smul, sub_zero]
  have hGP₀ : ∀ z, G (P₀ z) = 0 := by
    intro z
    simp only [P₀, C, LinearMap.sub_apply, constantProjection_apply,
      map_sub, map_smul, hGP, hGe, smul_zero, sub_zero]
  have hGQ₀ : ∀ z, G (Q₀ z) = 0 := by
    intro z
    simp only [Q₀, C, LinearMap.sub_apply, constantProjection_apply,
      map_sub, map_smul, hGQ, hGe, smul_zero, sub_zero]
  have hGf : G f₀ = G f := by simp only [f₀, map_sub, map_smul, hGe, smul_zero, sub_zero]
  have hRf : R f₀ = R f := by simp only [f₀, map_sub, map_smul, hRe, smul_zero, sub_zero]
  have hSf : S f₀ = S f := by simp only [f₀, map_sub, map_smul, hSe, smul_zero, sub_zero]
  have hCf : C f₀ = 0 := by
    simp only [C, f₀, constantProjection_apply, inner_sub_left, real_inner_smul_left,
      hee, mul_one, sub_self, zero_smul]
  have hPf : f₀ - P₀ f₀ = f - P f := by
    change f₀ - (P f₀ - C f₀) = _
    rw [hCf]
    simp only [f₀, map_sub, map_smul, hPe, sub_zero]
    module
  have hQf : f₀ - Q₀ f₀ = f - Q f := by
    change f₀ - (Q f₀ - C f₀) = _
    rw [hCf]
    simp only [f₀, map_sub, map_smul, hQe, sub_zero]
    module
  have h := rank_one_disjoint_interaction_of_covariance P₀ Q₀ G R S
    hP₀s hQ₀s hGs hRs hSs hP₀i hQ₀i hGi u v c hc huu hvv hP₀u hQ₀v hcov₀
    hGP₀ hGQ₀ hRline hSline f₀
  simpa only [hGf, hRf, hSf, hPf, hQf] using h

theorem independent_interaction_with_constants
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (e : E) (hee : inner ℝ e e = 1) (hPe : P e = e) (hQe : Q e = e)
    (hcov : ∀ z w, inner ℝ (P z) (Q w) = inner ℝ z e * inner ℝ w e)
    (hGe : G e = 0) (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (f : E) : ‖G f‖ ^ 2 ≤ inner ℝ (f - P f) (f - Q f) := by
  let C := constantProjection e
  let P₀ := P - C
  let Q₀ := Q - C
  let f₀ := f - inner ℝ f e • e
  have hCs : C.IsSymmetric := constantProjection_symmetric e
  have hPQ (z : E) : P (Q z) = C z := by
    apply ext_inner_left ℝ
    intro w
    rw [← hPs, hcov]
    exact (inner_constant_right e w z).symm
  have hPC (z : E) : P (C z) = C z := by
    simp only [C, constantProjection_apply, map_smul, hPe]
  have hCQ (z : E) : C (Q z) = C z := by
    simp only [C, constantProjection_apply]
    rw [hQs, hQe]
  have hCC (z : E) : C (C z) = C z := by
    simp only [C, constantProjection_apply, real_inner_smul_left, hee, mul_one]
  have hPQ₀ (z : E) : P₀ (Q₀ z) = 0 := by
    simp only [P₀, Q₀, LinearMap.sub_apply, map_sub, hPQ, hPC, hCQ, hCC,
      sub_self]
  have hGP₀ (z : E) : G (P₀ z) = 0 := by
    simp only [P₀, C, LinearMap.sub_apply, constantProjection_apply,
      map_sub, map_smul, hGP, hGe, smul_zero, sub_zero]
  have hGQ₀ (z : E) : G (Q₀ z) = 0 := by
    simp only [Q₀, C, LinearMap.sub_apply, constantProjection_apply,
      map_sub, map_smul, hGQ, hGe, smul_zero, sub_zero]
  have hGf : G f₀ = G f := by simp only [f₀, map_sub, map_smul, hGe, smul_zero, sub_zero]
  have hCf : C f₀ = 0 := by
    simp only [C, f₀, constantProjection_apply, inner_sub_left, real_inner_smul_left,
      hee, mul_one, sub_self, zero_smul]
  have hPf : f₀ - P₀ f₀ = f - P f := by
    change f₀ - (P f₀ - C f₀) = _
    rw [hCf]
    simp only [f₀, map_sub, map_smul, hPe, sub_zero]
    module
  have hQf : f₀ - Q₀ f₀ = f - Q f := by
    change f₀ - (Q f₀ - C f₀) = _
    rw [hCf]
    simp only [f₀, map_sub, map_smul, hQe, sub_zero]
    module
  have h := independent_disjoint_interaction P₀ Q₀ G (hPs.sub hCs) (hQs.sub hCs) hGs
    (subtract_constant_idempotent P hPs hPi e hee hPe)
    (subtract_constant_idempotent Q hQs hQi e hee hQe)
    hGi hPQ₀ hGP₀ hGQ₀ f₀
  simpa only [hGf, hPf, hQf] using h

end Problem315.RankOneInteraction

end

end OAI
