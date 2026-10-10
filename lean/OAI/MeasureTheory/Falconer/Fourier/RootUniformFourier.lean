import OAI.MeasureTheory.Falconer.Fourier.RootFourierError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

theorem uniform_root_fourier_error {sig δ T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    ∀ [IsProbabilityMeasure d.ρ] [IsProbabilityMeasure e.ρ],
    0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
    (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    (∀ᵐ x ∂d.ρ, x ∈ U.carrier) → (∀ᵐ y ∂e.ρ, y ∈ V.carrier) →
    (∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y) →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
    Integrable (rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)))
      (d.ρ.prod e.ρ) ∧
    ‖charFun (rootWeightedDistance d e N sig) r - rootNormalizedF d e N sig n U V r‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_root_normalized_error (T := T) hsig hsmall hδ
  refine ⟨n,N₀,?_⟩
  intro N hN d e instd inste hd he hc₁ hc₂ hL₁ hL₂ U V hU hV hcarry₁ hcarry₂ hdist s hUs hVs hsep r hr
  have hmem := root_pair_ae_patches d e U V hcarry₁ hcarry₂
  have hdist' : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2 := by
    filter_upwards [hmem] with z hz
    exact hdist z.1 hz.1 z.2 hz.2
  have herr : ∀ᵐ z ∂d.ρ.prod e.ρ,
      ‖(rootSpatialWeight d e N sig z:ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ)) -
        rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) z‖ ≤ ((2:ℝ)^N)^(-T) := by
    filter_upwards [hmem] with z hz
    exact h₀ N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr
      z.1 hz.1 z.2 hz.2 (hdist z.1 hz.1 z.2 hz.2)
  have hh := rootNormalizedF_error_of_pointwise d e hd he N sig n U V r _ hδ hdist' herr
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,one_mul] using hh

theorem root_patch_distance_lower (U V : DyadicSquare) (hU : 0 < U.side) (hV : 0 < V.side)
    {s : ℝ} (hUs : U.side ≤ s) (hVs : V.side ≤ s) (hsep : 100*s ≤ dist U.center V.center)
    {x y : Plane} (hx : x ∈ U.carrier) (hy : y ∈ V.carrier) : 96*s ≤ dist x y := by
  have h₁ := U.dist_center_le_three_quarters hU.le hx
  have h₂ := V.dist_center_le_three_quarters hV.le hy
  have h₃ := dist_triangle U.center x V.center
  have h₄ := dist_triangle x y V.center
  rw [dist_comm U.center x] at h₃
  have hs : 0 < s := hU.trans_le hUs
  linarith

end PlanarFalconer

end OAI
