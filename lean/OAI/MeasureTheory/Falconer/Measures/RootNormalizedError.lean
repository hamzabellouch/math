import OAI.MeasureTheory.Falconer.Estimates.RootWeightedInverse
import OAI.MeasureTheory.Falconer.Fourier.RootNormalizedKernel
import OAI.MeasureTheory.Falconer.Shells.NormalizedHighShellError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem rootNormalizedKernel_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ) (n : ℕ)
    (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × (Plane × Plane) => rootNormalizedKernel d e N sig n p.1 ψ p.2) := by
  unfold rootNormalizedKernel
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_sum
    intro j _hj
    apply Measurable.mul
    · fun_prop
    · apply measurable_list_sum
      intro b _hb
      apply Measurable.const_mul
      apply Measurable.mul
      · fun_prop
      · exact measurable_sourceDistanceKernel ψ _ _ hψ
          (rootLeftSymbol_measurable d N sig b.2) (rootRightSymbol_measurable e N sig b.2)

theorem uniform_root_normalized_error {sig δ T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
    (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
    ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y →
    ‖(rootSpatialWeight d e N sig (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) (x,y)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_root_weighted_inverse (T := T) hsig hsmall hδ
  refine ⟨n,N₀,?_⟩
  intro N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hb := h₀ N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hrp : 0 < r := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hr
  have hdist : 0 < dist x y := hδ.trans_le hxy
  have heq := root_weightedInverseCircle_normalized d e hd he N sig n (r := r) hrp (z := (x,y)) hdist
    (sourceConeCircle (sourceParentAxis U V)) (measurable_sourceConeCircle _)
    (by norm_num : (0:ℝ) ≤ 1) (sourceConeCircle_norm_le _)
  simp only [neg_zero,Real.rpow_zero,div_one] at heq
  rw [heq] at hb
  exact hb

end PlanarFalconer

end OAI
