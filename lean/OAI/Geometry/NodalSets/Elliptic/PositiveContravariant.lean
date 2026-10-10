import OAI.Geometry.NodalSets.Coefficients.CoefficientMetricJets

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma positiveContravariant_injective (A : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (A α)) : Function.Injective A := by
  intro α β h
  apply sub_eq_zero.mp
  by_contra hn
  have hz : A (α-β) = 0 := by rw [map_sub,h,sub_self]
  have hh := hp (α-β) hn
  rw [hz,map_zero] at hh
  exact (lt_irrefl 0 hh)

def positiveContravariantEquiv (A : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (A α)) : (E →L[ℝ] ℝ) ≃L[ℝ] E :=
  (A.toLinearMap.linearEquivOfInjective (positiveContravariant_injective A hp)
    dual_continuous_finrank).toContinuousLinearEquiv

lemma coefficientMetric_positive (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α)) (hρ : 0 < c.2) (v : E) (hv : v ≠ 0) :
    0 < coefficientMetricValue c v v := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have he : e.symm v ≠ 0 := by
    intro hz
    have h := congrArg e hz
    exact hv (by simpa using h)
  have hh := hp (e.symm v) he
  change 0 < e.symm v (e (e.symm v)) at hh
  rw [e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using mul_pos hρ hh

lemma coefficientMetric_inverse (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α)) (hρ : 0 < c.2) :
    ContinuousLinearMap.inverse (coefficientMetricValue c) = c.2⁻¹ • c.1 := by
  let e := positiveContravariantEquiv c.1 hp
  let m := positiveMetricEquiv (coefficientMetricValue c) (coefficientMetric_positive c hp hρ)
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have hm : ContinuousLinearMap.inverse (coefficientMetricValue c) = m.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv m
  rw [hm]
  ext α
  apply m.injective
  change m (m.symm α) = coefficientMetricValue c (c.2⁻¹ • c.1 α)
  rw [m.apply_symm_apply]
  change α = c.2 • (ContinuousLinearMap.inverse c.1) (c.2⁻¹ • e α)
  rw [hi,map_smul]
  change α = c.2 • (c.2⁻¹ • e.symm (e α))
  simp [smul_smul,hρ.ne']

lemma coefficientMetric_symmetric (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α))
    (hs : ∀ α β : E →L[ℝ] ℝ, α (c.1 β) = β (c.1 α)) (u v : E) :
    coefficientMetricValue c u v = coefficientMetricValue c v u := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have hh := hs (e.symm u) (e.symm v)
  change e.symm u (e (e.symm v)) = e.symm v (e (e.symm u)) at hh
  rw [e.apply_symm_apply,e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using congrArg (fun z : ℝ ↦ c.2*z) hh

end
end Yau.Geometry

end OAI
