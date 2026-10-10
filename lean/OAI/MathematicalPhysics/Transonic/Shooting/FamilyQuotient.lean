import OAI.MathematicalPhysics.Transonic.Shooting.FamilyC1

namespace OAI

section
noncomputable section

namespace SepticProfile.FamilyC1
open Set Metric
open scoped NNReal
variable {A : Type*} [TopologicalSpace A] [CompactSpace A]

/-- Uniform differentiability and Lipschitz bounds for the actual rational
sonic remainder family. Compactness is applied to the *constructed* finite
coefficient family, and only the nonzero sonic divisor is needed. -/
theorem exists_uniform_quotient_bounds {n d : A → V → ℂ}
    (N : Data n) (D : Data d) (hn : ∀ a, d a 0 ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0, ∃ M : ℝ, 0 ≤ M ∧
      (∀ a v, v ∈ closedBall 0 R → d a v ≠ 0) ∧
      (∀ a, DifferentiableOn ℂ (fun v => n a v/d a v) (closedBall 0 R)) ∧
      (∀ a, LipschitzOnWith K (fun v => n a v/d a v) (closedBall 0 R)) ∧
      Continuous (fun p : A × ↥(closedBall (0:V) R) => n p.1 p.2/d p.1 p.2) ∧
      ∀ a, ‖n a 0/d a 0‖ ≤ M := by
  obtain ⟨R,hR,hden⟩ := exists_uniform_den_radius D.continuous_h hn
  let S : Set (A × V) := univ ×ˢ closedBall 0 R
  let QD : A → V → V →L[ℂ] ℂ := fun a v =>
    n a v • (-(d a v ^2)⁻¹ • D.D a v)+(d a v)⁻¹ • N.D a v
  have hder (a : A) (v : V) (hv : v ∈ closedBall 0 R) :
      HasFDerivAt (fun w => n a w/d a w) (QD a v) v := by
    have hdv : HasFDerivAt (fun w : V => (d a w)⁻¹) (-(d a v^2)⁻¹ • D.D a v) v :=
      (hasDerivAt_inv (hden a v hv)).comp_hasFDerivAt v (D.hasFD a v)
    simpa only [QD,div_eq_mul_inv,Function.comp_def,Pi.mul_def] using (N.hasFD a v).mul hdv
  have hid : ContinuousOn (fun p : A × V => (d p.1 p.2)⁻¹) S :=
    D.continuous_h.continuousOn.inv₀ (fun p hp => hden p.1 p.2 hp.2)
  have his : ContinuousOn (fun p : A × V => -(d p.1 p.2 ^2)⁻¹) S :=
    ((D.continuous_h.pow 2).continuousOn.inv₀ (fun p hp => pow_ne_zero _ (hden p.1 p.2 hp.2))).neg
  have hcD : ContinuousOn (fun p : A × V => QD p.1 p.2) S :=
    (N.continuous_h.continuousOn.smul (his.smul D.continuous_D.continuousOn)).add
      (hid.smul N.continuous_D.continuousOn)
  have hSc : IsCompact S := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨B,hB⟩ := hSc.exists_bound_of_continuousOn hcD
  let K : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hbound (a : A) (v : V) (hv : v ∈ closedBall 0 R) : ‖QD a v‖₊ ≤ K := by
    change ‖QD a v‖ ≤ max B 0
    exact (hB (a,v) ⟨mem_univ _,hv⟩).trans (le_max_left _ _)
  have hqc : Continuous (fun p : A × ↥(closedBall (0:V) R) => n p.1 p.2/d p.1 p.2) := by
    have hmap : Continuous (fun p : A × ↥(closedBall (0:V) R) => (p.1,(p.2:V))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact (N.continuous_h.comp hmap).div (D.continuous_h.comp hmap)
      (fun p => hden p.1 p.2 p.2.property)
  have hzero : Continuous (fun a => n a 0/d a 0) := by
    exact (N.continuous_h.comp (continuous_id.prodMk continuous_const)).div
      (D.continuous_h.comp (continuous_id.prodMk continuous_const)) hn
  obtain ⟨B0,hB0⟩ := isCompact_univ.exists_bound_of_continuousOn hzero.continuousOn
  refine ⟨R,hR,K,max B0 0,le_max_right _ _,hden,?_,?_,hqc,?_⟩
  · intro a v hv
    exact (hder a v hv).differentiableAt.differentiableWithinAt
  · intro a
    exact Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun v hv => (hder a v hv).hasFDerivWithinAt) (hbound a) (convex_closedBall _ _)
  · intro a
    exact (hB0 a (mem_univ a)).trans (le_max_left _ _)

end SepticProfile.FamilyC1

end
end

end OAI
