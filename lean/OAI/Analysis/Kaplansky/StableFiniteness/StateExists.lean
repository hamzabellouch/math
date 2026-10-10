import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Quotient.Extraction

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma positiveCone_closed : IsClosed (positiveCone A) :=
  isClosed_le continuous_const continuous_subtype_val

lemma neg_one_not_positiveCone : (-1 : selfAdjoint A) ∉ positiveCone A := by
  intro h
  have h' : (1:A) ≤ 0 := by
    have : -(1:A) ≥ 0 := h
    simpa only [neg_nonneg] using this
  exact one_ne_zero (le_antisymm h' zero_le_one)

lemma normalized_positive_functional_exists : ∃ f : A →ₚ[ℂ] ℂ, f 1=1 := by
  obtain ⟨f,u,hneg,hpos⟩ := geometric_hahn_banach_point_closed
    (positiveCone_convex (A:=A)) (positiveCone_closed (A:=A)) (neg_one_not_positiveCone (A:=A))
  have hu : u<0 := by simpa using hpos 0 (show 0 ∈ positiveCone A from (by change (0:A)≤0; exact le_rfl))
  have hfpos (x : selfAdjoint A) (hx : 0 ≤ (x:A)) : 0 ≤ f x := by
    by_contra hn
    have hn : f x < 0 := lt_of_not_ge hn
    let t : ℝ := (u-1)/(f x)
    have ht : 0 ≤ t := div_nonneg_of_nonpos (by linarith) hn.le
    have htX : t • x ∈ positiveCone A := smul_nonneg ht hx
    have hb := hpos (t • x) htX
    rw [map_smul,smul_eq_mul,show t*f x=u-1 from div_mul_cancel₀ _ hn.ne] at hb
    linarith
  have hf1 : 0<f 1 := by
    rw [map_neg] at hneg
    linarith
  let g : selfAdjoint A →ₗ[ℝ] ℝ := (f 1)⁻¹ • f.toLinearMap
  have hgpos (x : selfAdjoint A) (hx : 0 ≤ (x:A)) : 0 ≤ g x := by
    change 0 ≤ (f 1)⁻¹ * f x
    exact mul_nonneg (inv_nonneg.mpr hf1.le) (hfpos x hx)
  have hg1 : g 1=1 := inv_mul_cancel₀ hf1.ne'
  let φ := complexify g
  have hφpos (x : A) (hx : 0≤x) : 0≤φ x := by
    rw [show φ x = (g ⟨x,IsSelfAdjoint.of_nonneg hx⟩ : ℂ) from
      complexify_apply_selfAdjoint g x (IsSelfAdjoint.of_nonneg hx)]
    exact_mod_cast hgpos ⟨x,IsSelfAdjoint.of_nonneg hx⟩ hx
  refine ⟨PositiveLinearMap.mk₀ φ hφpos,?_⟩
  change φ 1=1
  rw [show φ 1 = (g 1:ℂ) from complexify_apply_selfAdjoint g 1 (IsSelfAdjoint.one A),hg1]
  rfl


end KaplanskyConsequences

end

end OAI
