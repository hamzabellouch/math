import OAI.MeasureTheory.Falconer.Estimates.RetainedEnergy
import OAI.MeasureTheory.Falconer.Angular.CapEnergyExpansion
import OAI.MeasureTheory.Falconer.Angular.DyadicCapTerms

namespace OAI

/-!
# From integrated localization to the original independent energy

This is the algebraic assembly step: exact original-law splitting, the
actual cap partition, integrated localization, and the proved Schur bound.
The localization premise is supplied by `dyadic_localization_error`.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem independentAngularEnergy_of_localization
    {d j g₁ g₂ L C₁ C₂ : ℕ} {κ : Type*}
    (Q₁ Q₂ : DyadicCube d) (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (K : Finset κ) (η : κ → Sphere d → ℝ) (center : κ → Sphere d)
    (hη : ∀ k ∈ K, ∀ w, 0 ≤ η k w)
    (hpartition : ∀ w, ∑ k ∈ K, η k w = 1)
    {δ τ W₁ W₂ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ k ∈ K, ∀ w, 0 < η k w → ‖(w : Space d)-center k‖ ≤ δ)
    (hg₁ : g₁ ≤ j) (hg₂ : g₂ ≤ j)
    (hL : 4*τ*((2 : ℝ)^j/Q₁.side) ≤ L)
    (hwidth₁ : 2*τ+2*δ*(Real.sqrt d*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁)
    (hwidth₂ : 2*τ+2*δ*(Real.sqrt d*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂)
    (hsupport₁ : ∀ q ∈ Q₁.occupiedPaths μ j,
      ∀ᵐ x ∂μ.restrict (Q₁.descendant q).carrier,
        ∀ w : Sphere d, b x w ≠ 0 →
          DyadicParallelTest Q₁ (Q₁.occupiedPaths μ j) g₁ q (w : Space d) W₁ C₁)
    (hsupport₂ : ∀ q ∈ Q₂.occupiedPaths ν j,
      ∀ᵐ x ∂ν.restrict (Q₂.descendant q).carrier,
        ∀ w : Sphere d, c x w ≠ 0 →
          DyadicParallelTest Q₂ (Q₂.occupiedPaths ν j) g₂ q (w : Space d) W₂ C₂)
    (a p v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {ε : ℝ}
    (herror :
      let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
      let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
        (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
        (center k.1) (center k.2) τ
      let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν Mp₁ Mp₂ b c (η k.1) (η k.2)
      ‖(∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S, F k row col z ∂angularProductMeasure d v Ψ) -
        (∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S,
          if G k row col then F k row col z else 0 ∂angularProductMeasure d v Ψ)‖ ≤ ε) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) ≤
    ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
      ((2 : ℝ)^((d : ℝ)*(p-a)) *
        ((2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂)) : ℕ) *
        ∑ row ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j,
          independentAngularEnergy p v Ψ
            (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) Mp₁ b z.1 z.2)
            (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) Mp₂ c z.1 z.2)) +
      (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*ε := by
  let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
  let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
    (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
    (center k.1) (center k.2) τ
  let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν Mp₁ Mp₂ b c (η k.1) (η k.2)
  let full := ∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S, F k row col z
    ∂angularProductMeasure d v Ψ
  let kept := ∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S,
    if G k row col then F k row col z else 0 ∂angularProductMeasure d v Ψ
  have hfull : independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) =
      (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*‖full‖ := by
    rw [independentAngularEnergy_dyadic_expansion Q₁ Q₂ μ ν j a v Ψ
      Ma₁ Ma₂ Mp₁ Mp₂ hMa₁ hMa₂ hMp₁.ne' hMp₂.ne' b c hb hc hB hB hbB hcB]
    rw [integrated_cap_cross_expansion S K η hpartition]
    rfl
  have hkept : kept = ∫ z, ∑ k ∈ K ×ˢ K, (η k.1 z.2.1*η k.2 z.2.2) •
      (∑ row ∈ S, ∑ col ∈ S, if G k row col then
        dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c row z *
        star (dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c col z) else 0)
      ∂angularProductMeasure d v Ψ := by
    apply integral_congr_ae
    filter_upwards with z
    simp only [F,dyadicCapIntegrand,Finset.smul_sum,smul_ite,smul_zero]
  have hret := retained_dyadic_energy_bound Q₁ Q₂ hQ hside μ ν Mp₁ Mp₂ hMp₁ hMp₂
    b c hb hc hB hB hbB hcB K η center hη hpartition hδ hcap hg₁ hg₂ hL
    hwidth₁ hwidth₂ hsupport₁ hsupport₂ a p v Ψ
  change (2 : ℝ)^((d : ℝ)*(v-a))*‖_‖ ≤ _ at hret
  rw [← hkept] at hret
  have he : ‖full-kept‖ ≤ ε := herror
  have hnorm : ‖full‖ ≤ ‖kept‖+ε := by
    calc
      _ = ‖kept+(full-kept)‖ := by congr 1; abel
      _ ≤ ‖kept‖+‖full-kept‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl he
  rw [hfull]
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*(‖kept‖+ε) := by gcongr
    _ = ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*((2 : ℝ)^((d : ℝ)*(v-a))*‖kept‖) +
        (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*ε := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hret (sq_nonneg _)) le_rfl

end Falconer

end OAI
