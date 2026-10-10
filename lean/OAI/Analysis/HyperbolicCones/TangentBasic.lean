import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open scoped RealInnerProductSpace

namespace Paper256

theorem tangentCurve_unit (v h : Vec 4) (hv : ‖v‖ = 1)
    (hh : inner ℝ v h = 0) (s : ℝ) : ‖tangentCurve v h s‖ = 1 := by
  have hp : 0 < 1 + s ^ 2 * ‖h‖ ^ 2 := by positivity
  have hn : ‖v + s • h‖ = Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq hp.le (norm_nonneg _)).2
    symm
    rw [norm_add_sq_real, real_inner_smul_right, hh, hv, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [tangentCurve, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (Real.sqrt_pos.2 hp), hn, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hp))]

theorem tangentCurve_derivative (v h : Vec 4) : HasDerivAt (tangentCurve v h) h 0 := by
  have hg : HasDerivAt (fun s : ℝ => 1 + s ^ 2 * ‖h‖ ^ 2) 0 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖h‖ ^ 2)).const_add 1
  have hs : HasDerivAt (fun s : ℝ => (Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2))⁻¹) 0 0 := by
    simpa using! (hg.sqrt (by norm_num)).inv (by norm_num)
  simpa [tangentCurve] using! hs.smul (((hasDerivAt_id (0 : ℝ)).smul_const h).const_add v)

theorem tangentCurve_wedge (v h : Vec 4) (s : ℝ) :
    wedgeCoordinates v (tangentCurve v h s) =
      (s / Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2)) • wedgeCoordinates v h := by
  funext i
  simp [wedgeCoordinates, tangentCurve, div_eq_mul_inv]
  ring

def tangentCoordinates (v : Vec 4) : tangentSpace v →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun h := wedgeCoordinates v h.val
  map_add' h k := by ext i; simp [wedgeCoordinates]; ring
  map_smul' s h := by ext i; simp [wedgeCoordinates]; ring

theorem tangent_coordinates_isomorphism (v : Vec 4) (hv : ‖v‖ = 1) (hv0 : v 0 ≠ 0) :
    ∃ J : tangentSpace v ≃ₗ[ℝ] (Fin 3 → ℝ),
      ∀ h : tangentSpace v, J h = wedgeCoordinates v h.val := by
  have hf : (innerSL ℝ v).toLinearMap ≠ 0 := by
    intro hf
    have := LinearMap.congr_fun hf v
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      LinearMap.zero_apply, real_inner_self_eq_norm_sq, hv, one_pow] at this
    exact one_ne_zero this
  have hdim : Module.finrank ℝ (tangentSpace v) =
      Module.finrank ℝ (Fin 3 → ℝ) := by
    have ht := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    simp only [finrank_euclideanSpace, Fintype.card_fin] at ht
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    change Module.finrank ℝ (LinearMap.ker (innerSL ℝ v).toLinearMap) = 3
    omega
  have hinj : Function.Injective (tangentCoordinates v) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.2
    intro h hh
    have hw (i : Fin 3) : v 0 * h.val i.succ - h.val 0 * v i.succ = 0 := by
      exact congrFun hh i
    have he : h.val = (h.val 0 / v 0) • v := by
      apply PiLp.ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [div_mul_cancel₀ _ hv0]
      · dsimp
        calc
          h.val i.succ = (h.val 0 * v i.succ) / v 0 :=
            (eq_div_iff hv0).2 (by nlinarith [hw i])
          _ = (h.val 0 / v 0) * v i.succ := by ring
    have hz : h.val 0 / v 0 = 0 := by
      have hm := h.property
      change inner ℝ v h.val = 0 at hm
      rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at hm
      simpa using hm
    apply Subtype.ext
    simpa [hz] using he
  exact ⟨(tangentCoordinates v).linearEquivOfInjective hinj hdim, fun _ => rfl⟩

end Paper256

end

end OAI
