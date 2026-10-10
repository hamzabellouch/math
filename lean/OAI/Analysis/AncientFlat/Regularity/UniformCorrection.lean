import OAI.Analysis.AncientFlat.Regularity.ActualBoundedJets

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_uniform_homogeneous_correction {α β : ℝ} (hα : 0<α)
    (L B : ℝ) (hL : 0≤L) (hB : 0≤B) :
    ∃ C D : ℝ, 0≤C ∧ 0<D ∧ ∀ (T : ℝ) (hT₀ : 0≤T), T≤1 →
      ∀ (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ)),
      (∀ s, ‖b s‖≤B) →
      (∀ s r : Slab T, ∀ x z : V,
        |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s.val-r.val|)) →
      ∀ d : C₀(V,ℂ), ∃ j : Time T →ᵇ C₀(V,ℂ),
        (∀ t : Time T, IntervalIntegrable
          (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val) ∧
        (∀ t : Time T, unweighted j t.val+∫ r in 0..t.val,
          residualKernel hα A b hT₀ t r (unweighted j r) =
            -actualResidual hα A b t (initial hT₀) d) ∧ ‖j‖≤D*(C*‖d‖) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_fullResidual_bound (V := V) α β hα L B hL hB
  obtain ⟨κ,hκ,hsmall⟩ := exists_damping_small C
  let Q := κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C
  have hden : 0<1-Q := sub_pos.mpr hsmall
  let D := Real.exp κ^2/(1-Q)
  have hD : 0<D := div_pos (sq_pos_of_pos (Real.exp_pos _)) hden
  refine ⟨C,D,hC,hD,fun T hT₀ hT A b hb hLip d => ?_⟩
  have hR : ∀ (t : Time T) (s : Slab T), s.val<t.val →
      ‖actualResidual hα A b t s‖≤C*(t.val-s.val)^(-3/4 : ℝ) := by
    intro t s hst
    have hq : 0<t.val-s.val := sub_pos.mpr hst
    have hq1 : t.val-s.val≤1 := by linarith [t.property.2,s.property.1]
    have he : |(now t).val-s.val|=ParabolicRadius.radius (t.val-s.val)^4 := by
      rw [ParabolicRadius.pow_four hq.le]
      exact abs_of_pos hq
    unfold actualResidual
    rw [←ParabolicRadius.inv_pow_three hq.le]
    apply hbound _ _ _ _ (ParabolicRadius.pos hq) (ParabolicRadius.le_one hq.le hq1) (hb _)
    intro x z
    simpa only [he,BoundedContinuousFunction.coe_toContinuousMap] using hLip (now t) s x z
  have hN : ∀ p : Time T × UnitTime, ‖normalized hα A b p‖≤C := by
    intro p
    let r := ParabolicRadius.radius (elapsed p)
    have hr : 0<r := ParabolicRadius.pos (elapsed_pos p)
    have hRb : ‖actualResidual hα A b p.1 (before p)‖≤C*(r⁻¹)^3 := by
      have hsub : p.1.val-(before p).val=elapsed p := (elapsed_eq_sub p).symm
      have hh := hR p.1 (before p) (sub_pos.mp (hsub.symm ▸ elapsed_pos p))
      rw [hsub,←ParabolicRadius.inv_pow_three (elapsed_pos p).le] at hh
      exact hh
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro f
    change ‖r^3 • actualResidual hα A b p.1 (before p) f‖≤C*‖f‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le _)]
    calc
      _ ≤ r^3*(C*(r⁻¹)^3*‖f‖) := mul_le_mul_of_nonneg_left
        (((actualResidual hα A b p.1 (before p)).le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hRb (norm_nonneg f))) (pow_nonneg hr.le _)
      _ = _ := by field_simp
  have hR₀ : ∀ t : Time T, ‖actualResidual hα A b t (initial hT₀)‖≤C*t.val^(-3/4 : ℝ) := by
    intro t
    simpa only [initial,sub_zero] using hR t (initial hT₀) t.property.1
  let N : Kernel T C₀(V,ℂ) := Kernel.ofStrong (normalized hα A b)
    (continuous_normalized_apply hα A b) C hC hN
  let g := weightedSource hα A b hT₀ hT C hC hR₀ d 0
  obtain ⟨j,hj,_⟩ := exists_unique_solution_full N C hC hN hT₀ hT g
  have hi := intervalIntegrable_kernel_unweighted N C hC hN j
  have he := unweighted_solves N C hC hN hT₀ g j hj
  have hk : ∀ t r, kernel N t r=residualKernel hα A b hT₀ t r :=
    kernel_eq_residualKernel hα A b hT₀ C hC hN
  simp_rw [hk] at hi he
  have hg : ∀ t : Time T, unweighted g t.val= -actualResidual hα A b t (initial hT₀) d := by
    intro t
    simpa using unweighted_weightedSource hα A b hT₀ hT C hC hR₀ d 0 t
  simp_rw [hg] at he
  refine ⟨j,hi,he,?_⟩
  let : NormedAddCommGroup (Time T →ᵇ C₀(V,ℂ)) := inferInstance
  have hgnorm : ‖g‖≤C*‖d‖ := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg d))).mpr
    intro t
    have hh := norm_sourceRHS_le hα A b hT₀ hT C hC hR₀ d 0 t
    have hz : ‖(0 : Time T →ᵇ C₀(V,ℂ))‖=0 := norm_zero
    change ‖sourceRHS hα A b hT₀ d 0 t‖≤C*‖d‖
    simpa only [hz,zero_add] using hh
  have hExp : Real.exp (κ*T)^2≤Real.exp κ^2 := by
    gcongr
    exact mul_le_of_le_one_right hκ.le hT
  calc
    ‖j‖ ≤ Real.exp (κ*T)^2/(1-Q)*‖g‖ := norm_solution_full_le N C hC hN κ hκ hT₀ hT hsmall g j hj
    _ ≤ D*‖g‖ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hExp hden.le) (norm_nonneg g)
    _ ≤ D*(C*‖d‖) := mul_le_mul_of_nonneg_left hgnorm hD.le
end ParametrixVolterra

end

end OAI
