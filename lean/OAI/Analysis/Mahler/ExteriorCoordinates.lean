import OAI.Analysis.Mahler.BasisContinuousWedge

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def continuousReindex (e : ι ≃ κ) :
    (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] (E [⋀^κ]→L[ℝ] ℂ) :=
  AlternatingMap.mkContinuousLinear
    ((AlternatingMap.domDomCongrₗ ℝ e).comp
      (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ))) 1 (by
    intro A v
    change ‖A (v ∘ e)‖ ≤ 1 * ‖A‖ * ∏ i, ‖v i‖
    simp only [one_mul]
    have h := A.le_opNorm (v ∘ e)
    simpa only [Function.comp_def, e.prod_comp (fun i => ‖v i‖)] using h)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma continuousReindex_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : E [⋀^ι]→L[ℝ] ℂ) (v : κ → E) :
    continuousReindex e A v = A (v ∘ e) := rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma continuousReindex_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : E [⋀^ι]→L[ℝ] ℂ) :
    (continuousReindex e A).toAlternatingMap = A.toAlternatingMap.domDomCongr e := rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma continuous_basis_expansion [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (basis : Module.Basis J ℝ E) (A : E [⋀^ι]→L[ℝ] ℂ) :
    A = ∑ q : ι → J, (A (basis ∘ q) / (Fintype.card ι).factorial) •
      continuousCovectorVolume (complexCoord basis ∘ q) := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [alternating_basis_expansion_normalized basis A.toAlternatingMap]
  ext v
  simp only [alternating_sum_eval, ContinuousAlternatingMap.coe_toAlternatingMap,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    AlternatingMap.smul_apply]
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma extDeriv_sum [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {Q : Type*} (s : Finset Q) {n : ℕ}
    (F : Q → E → E [⋀^Fin n]→L[ℝ] ℂ) {x : E}
    (hF : ∀ q ∈ s, DifferentiableAt ℝ (F q) x) :
    extDeriv (fun y => ∑ q ∈ s, F q y) x = ∑ q ∈ s, extDeriv (F q) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, extDeriv, fderiv_fun_const]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
  | @insert q s hq ih =>
    simp only [Finset.sum_insert hq]
    rw [extDeriv_fun_add (hF q (Finset.mem_insert_self _ _))
      (DifferentiableAt.fun_sum (fun r hr => hF r (Finset.mem_insert_of_mem hr))),
      ih (fun r hr => hF r (Finset.mem_insert_of_mem hr))]

/-- Exact coordinate expression for exterior differentiation; the factorial
is the one forced by the actual unnormalized shuffle product. -/
theorem extDeriv_basis_expansion (basis : Module.Basis J ℝ E) {n : ℕ}
    {A : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E} (hA : DifferentiableAt ℝ A x) :
    (extDeriv A x).toAlternatingMap =
      ∑ q : Fin n → J,
        (wedge (covectorVolume (fun _ : Fin 1 =>
          (fderiv ℝ (fun y => A y (basis ∘ q) / (n.factorial : ℂ)) x).toLinearMap))
          (covectorVolume (complexCoord basis ∘ q))).domDomCongr (prependFinEquiv n) := by
  have hc (q : Fin n → J) : DifferentiableAt ℝ
      (fun y => A y (basis ∘ q) / (n.factorial : ℂ)) x := by
    simpa only [div_eq_mul_inv, Function.comp_def, ContinuousAlternatingMap.apply_apply] using
      ((ContinuousAlternatingMap.apply ℝ E ℂ (basis ∘ q)).differentiableAt.comp x hA).mul_const ((n.factorial : ℂ)⁻¹)
  have he : A = fun y => ∑ q : Fin n → J,
      (A y (basis ∘ q) / (n.factorial : ℂ)) •
        continuousCovectorVolume (complexCoord basis ∘ q) := by
    funext y
    simpa only [Fintype.card_fin] using continuous_basis_expansion basis (A y)
  conv_lhs => rw [he]
  rw [extDeriv_sum _ _ (fun q _ => (hc q).smul_const _)]
  change (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ)) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact extDeriv_scalar_const basis _ (hc q)

end Mahler

end OAI
