import OAI.Geometry.Kahler.BaseMeans

namespace OAI

universe uKahler8786_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def sigma : Measure Sphere :=
  ((volume : Measure Base).toSphere univ)⁻¹ • (volume : Measure Base).toSphere

instance : IsProbabilityMeasure sigma where
  measure_univ := by
    rw [sigma, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (ne_of_gt (Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero volume)))
      (measure_ne_top _ _)

def sphereAction (U : Base ≃ₗᵢ[ℂ] Base) : Sphere ≃ₜ Sphere :=
  U.toHomeomorph.subtype (fun z => by simp [])

@[simp] lemma sphereAction_coe (U : Base ≃ₗᵢ[ℂ] Base) (ξ : Sphere) :
    (sphereAction U ξ : Base) = U (ξ:Base) := rfl

def realIsometry (U : Base ≃ₗᵢ[ℂ] Base) : Base ≃ₗᵢ[ℝ] Base where
  toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ
  norm_map' := U.norm_map

lemma sphereAction_preserves (U : Base ≃ₗᵢ[ℂ] Base) :
    MeasurePreserving (sphereAction U) sigma sigma := by
  have hm : MeasurePreserving (sphereAction U)
      (volume : Measure Base).toSphere (volume : Measure Base).toSphere := by
    refine ⟨(sphereAction U).measurable, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (sphereAction U).measurable hs,
      (volume : Measure Base).toSphere_apply' ((sphereAction U).measurable hs),
      (volume : Measure Base).toSphere_apply' hs]
    congr 1
    have he : Ioo (0:ℝ) 1 • ((↑) '' (sphereAction U ⁻¹' s)) =
        U ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' s)) := by
      ext z
      simp only [mem_preimage, Set.mem_smul, mem_image]
      constructor
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,rfl⟩
        exact ⟨r,hr,U (ξ:Base),⟨sphereAction U ξ,hξ,rfl⟩,(realIsometry U).map_smul r ξ |>.symm⟩
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,hz⟩
        refine ⟨r,hr,U.symm (ξ:Base),⟨(sphereAction U).symm ξ, ?_, rfl⟩,?_⟩
        · simpa using hξ
        · apply U.injective
          rw [← hz]
          calc
            U (r • U.symm (ξ:Base)) = r • U (U.symm (ξ:Base)) := (realIsometry U).map_smul _ _
            _ = _ := by rw [U.apply_symm_apply]
    rw [he]
    exact (realIsometry U).measurePreserving.measure_preimage_emb
      U.toHomeomorph.measurableEmbedding _
  exact hm.smul_measure _

lemma sigma_integral_unitary {E : Type uKahler8786_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Base ≃ₗᵢ[ℂ] Base) (f : Sphere → E) :
    (∫ ξ, f (sphereAction U ξ) ∂sigma) = ∫ ξ, f ξ ∂sigma :=
  (sphereAction_preserves U).integral_comp (sphereAction U).measurableEmbedding f

def phaseIsometry (c : ℂ) (hc : ‖c‖ = 1) : Base ≃ₗᵢ[ℂ] Base where
  toLinearEquiv := LinearEquiv.smulOfUnit (Units.mk0 c (by intro h; simp [h] at hc))
  norm_map' z := by change ‖c • z‖ = ‖z‖; simp [norm_smul,hc]

@[simp] lemma phaseIsometry_apply (c : ℂ) (hc : ‖c‖ = 1) (z : Base) :
    phaseIsometry c hc z = c • z := rfl

lemma exists_unit_pow_neg_one {n : ℕ} (hn : n ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c^n = -1 := by
  refine ⟨Complex.exp (Real.pi/n*Complex.I), ?_, ?_⟩
  · simp [Complex.norm_exp]
  · rw [← Complex.exp_nat_mul]
    have h : (n:ℂ)*(Real.pi/n*Complex.I) = Real.pi*Complex.I := by
      have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
      field_simp
    rw [h,Complex.exp_pi_mul_I]

lemma monomial_sigma_mean (d : Fin 2 →₀ ℕ) (a : ℂ) :
    (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) (MvPolynomial.monomial d a) ∂sigma) =
      MvPolynomial.eval (fun _ => (0:ℂ)) (MvPolynomial.monomial d a) := by
  classical
  by_cases hd : d = 0
  · subst d
    simp
  have hn : d 0 + d 1 ≠ 0 := by
    intro hn
    have h0 : d 0 = 0 := (Nat.add_eq_zero_iff.mp hn).1
    have h1 : d 1 = 0 := (Nat.add_eq_zero_iff.mp hn).2
    apply hd
    ext i
    fin_cases i <;> assumption
  obtain ⟨c,hc,hcn⟩ := exists_unit_pow_neg_one hn
  have hh := sigma_integral_unitary (phaseIsometry c hc)
    (fun ξ => MvPolynomial.eval (fun i => (ξ:Base) i) (MvPolynomial.monomial d a))
  simp only [MvPolynomial.eval_monomial,Finsupp.prod_pow,Fin.prod_univ_two,
    sphereAction_coe,phaseIsometry_apply,PiLp.smul_apply,smul_eq_mul] at hh ⊢
  have he : ∀ ξ : Sphere, a*((c*(ξ:Base) 0)^(d 0)*(c*(ξ:Base) 1)^(d 1)) =
      -(a*((ξ:Base) 0^(d 0)*(ξ:Base) 1^(d 1))) := by
    intro ξ
    simp only [mul_pow]
    calc
      _ = c^(d 0+d 1)*(a*((ξ:Base) 0^(d 0)*(ξ:Base) 1^(d 1))) := by rw [pow_add]; ring
      _ = _ := by rw [hcn]; ring
  simp_rw [he] at hh
  rw [integral_neg] at hh
  have hz : (0:ℂ)^d 0*(0:ℂ)^d 1 = 0 := by
    rw [← pow_add,zero_pow hn]
  rw [hz,mul_zero]
  linear_combination -hh / 2

lemma sigma_represents : Represents sigma := by
  classical
  intro p
  induction p using MvPolynomial.induction_on' with
  | monomial d a => exact monomial_sigma_mean d a
  | add p q hp hq =>
    simp only [map_add]
    rw [integral_add, hp,hq]
    · exact continuous_integrable (p.continuous_eval.comp
        (continuous_pi (fun i => (EuclideanSpace.proj i).continuous.comp continuous_subtype_val)))
    · exact continuous_integrable (q.continuous_eval.comp
        (continuous_pi (fun i => (EuclideanSpace.proj i).continuous.comp continuous_subtype_val)))

end PinchedHartogs.BaseConstruction

end

end OAI
