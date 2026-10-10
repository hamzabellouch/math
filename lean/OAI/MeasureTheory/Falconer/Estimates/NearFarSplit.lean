import OAI.MeasureTheory.Falconer.Recursion.ProfileNear
import OAI.MeasureTheory.Falconer.Angular.DyadicCapTerms

namespace OAI

/-! # Exact angular near/far splitting before taking absolute values -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem integral_selected_sum {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (G : ι → ι → Prop) (F : ι → ι → X → ℂ)
    (hF : ∀ i ∈ S, ∀ j ∈ S, Integrable (F i j) μ) :
    (∫ x, ∑ i ∈ S, ∑ j ∈ S, if G i j then F i j x else 0 ∂μ) =
      ∑ i ∈ S, ∑ j ∈ S, if G i j then (∫ x, F i j x ∂μ) else 0 := by
  have hi (i) (hi : i ∈ S) (j) (hj : j ∈ S) :
      Integrable (fun x => if G i j then F i j x else 0) μ := by
    by_cases h : G i j
    · simpa only [ite_eq_left h] using hF i hi j hj
    · simp only [ite_eq_right h]; exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun i h => integrable_finsetSum _ (hi i h))]
  apply Finset.sum_congr rfl
  intro i h
  rw [integral_finsetSum _ (hi i h)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : G i j <;> simp only [h,ite_true,ite_false,integral_zero]

theorem norm_integral_near_far {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (G : ι → ι → Prop) (F : ι → ι → X → ℂ)
    (hF : ∀ i ∈ S, ∀ j ∈ S, Integrable (F i j) μ) :
    ‖∫ x, ∑ i ∈ S, ∑ j ∈ S, F i j x ∂μ‖ ≤
      ‖∫ x, ∑ i ∈ S, ∑ j ∈ S, if G i j then F i j x else 0 ∂μ‖ +
        ∑ i ∈ S, ∑ j ∈ S, if G i j then 0 else ‖∫ x, F i j x ∂μ‖ := by
  have hfull : (∫ x, ∑ i ∈ S, ∑ j ∈ S, F i j x ∂μ) =
      ∑ i ∈ S, ∑ j ∈ S, ∫ x, F i j x ∂μ := by
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (hF i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum _ (hF i hi)
  rw [hfull,integral_selected_sum μ S G F hF]
  have hsplit : (∑ i ∈ S, ∑ j ∈ S, ∫ x, F i j x ∂μ) =
      (∑ i ∈ S, ∑ j ∈ S, if G i j then (∫ x, F i j x ∂μ) else 0) +
      (∑ i ∈ S, ∑ j ∈ S, if G i j then 0 else (∫ x, F i j x ∂μ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : G i j <;> simp only [h,ite_true,ite_false,zero_add,add_zero]
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases h : G i j <;> simp only [h,ite_true,ite_false,norm_zero,le_refl]

 theorem profile_energy_near_far {d : ℕ} (P₁ P₂ : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (profile : ℝ → ℝ) (N a h : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (ρ.restrict P₁.carrier) (profileModelMass profile N a) b z.1 z.2)
      (fun z => endpointTransform (ρ.restrict P₂.carrier) (profileModelMass profile N a) c z.1 z.2) ≤
    profileNearEnergy P₁ P₂ ρ profile N a h v Ψ b c +
      ((profileModelMass profile N h/profileModelMass profile N a)^4*
        (2:ℝ)^((d:ℝ)*(v-a))) *
        ∑ row ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
          ∑ col ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
            if nearDyadicEdge P₁ P₂ (10*((d:ℝ)+1)/(2:ℝ)^h) row col then 0 else
              ‖∫ z, dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
                  (profileModelMass profile N h) b c row z *
                star (dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
                  (profileModelMass profile N h) b c col z)
                ∂angularProductMeasure d v Ψ‖ := by
  have hMa : 0 < profileModelMass profile N a := by unfold profileModelMass; positivity
  have hMh : 0 < profileModelMass profile N h := by unfold profileModelMass; positivity
  let F := fun row col z => dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
      (profileModelMass profile N h) b c row z *
    star (dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
      (profileModelMass profile N h) b c col z)
  have hi (row col) : Integrable (F row col) (angularProductMeasure d v Ψ) := by
    have hcross :=
      dyadicCapIntegrand_integrable P₁ P₂ ρ ρ (profileModelMass profile N h)
        (profileModelMass profile N h) v Ψ hMh hMh b c hb hc (fun _ => 1) (fun _ => 1)
        measurable_const measurable_const (by intro; norm_num) (by intro; norm_num) hB hbB hcB row col
    have heq : dyadicCapIntegrand P₁ P₂ ρ ρ (profileModelMass profile N h)
        (profileModelMass profile N h) b c (fun _ => 1) (fun _ => 1) row col = F row col := by
      funext z
      simp only [dyadicCapIntegrand,one_mul,one_smul]
      rfl
    rwa [heq] at hcross
  have he := independentAngularEnergy_dyadic_expansion P₁ P₂ ρ ρ (h-a) a v Ψ
    (profileModelMass profile N a) (profileModelMass profile N a)
    (profileModelMass profile N h) (profileModelMass profile N h) hMa hMa
    hMh.ne' hMh.ne' b c hb hc hB hB hbB hcB
  have hp : ((profileModelMass profile N h/profileModelMass profile N a)*
      (profileModelMass profile N h/profileModelMass profile N a))^2 =
      (profileModelMass profile N h/profileModelMass profile N a)^4 := by ring
  rw [hp] at he
  rw [he]
  have hs := norm_integral_near_far (angularProductMeasure d v Ψ)
    (P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a))
    (nearDyadicEdge P₁ P₂ (10*((d:ℝ)+1)/(2:ℝ)^h)) F (fun i _ j _ => hi i j)
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤
      (profileModelMass profile N h/profileModelMass profile N a)^4*
        (2:ℝ)^((d:ℝ)*(v-a)) by positivity)
  simpa only [profileNearEnergy,F,mul_add,mul_assoc,mul_left_comm,mul_comm] using hb

end Falconer

end OAI
