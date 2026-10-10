import OAI.MeasureTheory.Falconer.Estimates.RootSpatialTerms

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

theorem rootNormalizedF_finite_separation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (U V : DyadicSquare)
    (hcarry₁ : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hcarry₂ : ∀ᵐ y ∂e.ρ, y ∈ V.carrier)
    (hsep : ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y ∧ dist x y ≤ L)
    (n : ℕ) (r : ℝ) :
    rootNormalizedF d e N sig n U V r =
      (((r^(1/2:ℝ)):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((((r/(2:ℝ)^(N:ℝ))⁻¹)^j:ℝ):ℂ) *
          ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
            rootAbsorbedCoefficient d e N sig j b *
              ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
                sourceParentDistanceF U V d.ρ e.ρ 1 1
                  (spatialPhasedSymbol 1 ξ (rootLeftSymbol d N sig b.2))
                  (spatialPhasedSymbol 1 ξ (rootRightSymbol e N sig b.2)) r)).sum := by
  let I := fun j => inverseLeibnizTerms j (rootMaskIndices d e)
  let R := fun j => ((((r/(2:ℝ)^(N:ℝ))⁻¹)^j:ℝ):ℂ)
  let A := (((r^(1/2:ℝ)):ℝ):ℂ)
  let K := fun j (b : ℂ × (RootMaskIndex → ℕ)) => rootDistanceEndpointKernel d e N sig U V j b.2 r
  let c := fun j b => rootAbsorbedCoefficient d e N sig j b
  have hdist : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2 := by
    filter_upwards [root_pair_ae_patches d e U V hcarry₁ hcarry₂] with z hz
    exact (hsep z.1 hz.1 z.2 hz.2).1
  have hi (j : ℕ) (b : ℂ × (RootMaskIndex → ℕ)) (hb : b ∈ I j) :
      Integrable (fun z => c j b * K j b z) (d.ρ.prod e.ρ) :=
    (rootDistanceEndpointKernel_integrable d e N sig hd he U V hδ hdist j hb r).const_mul (c j b)
  have hiJ (j : ℕ) : Integrable (fun z => R j * ((I j).map (fun b => c j b * K j b z)).sum) (d.ρ.prod e.ρ) :=
    (integrable_list_sum (d.ρ.prod e.ρ) (I j) (fun b z => c j b * K j b z) (hi j)).const_mul (R j)
  have heJ (j : ℕ) :
      (∫ z, R j * ((I j).map (fun b => c j b * K j b z)).sum ∂d.ρ.prod e.ρ) =
        R j * ((I j).map (fun b => c j b * ∫ z, K j b z ∂d.ρ.prod e.ρ)).sum := by
    rw [integral_const_mul,integral_list_sum (d.ρ.prod e.ρ) (I j) _ (hi j)]
    simp_rw [integral_const_mul]
  have hk (z : Plane × Plane) : rootNormalizedKernel d e N sig n r
      (sourceConeCircle (sourceParentAxis U V)) z =
      A * ∑ j ∈ Finset.range (n+1), R j * ((I j).map (fun b => c j b * K j b z)).sum := by
    simp only [rootNormalizedKernel,neg_zero,Real.rpow_zero,mul_one,div_one,
      A,R,I,c,K,rootDistanceEndpointKernel]
  unfold rootNormalizedF
  simp_rw [hk]
  rw [integral_const_mul,integral_finsetSum (Finset.range (n+1)) (fun j _ => hiJ j)]
  simp_rw [heJ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  rw [show (∫ z, K j b z ∂d.ρ.prod e.ρ) = _ from
    rootDistanceEndpointKernel_form δ L hδ hL d e N sig hd he U V hcarry₁ hcarry₂ hsep j hb r]

end PlanarFalconer

end OAI
