import OAI.MeasureTheory.Falconer.Shells.RootHighShellInverse

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_root_weighted_inverse {sig δ T : ℝ}
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
      (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
        sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
          (rootPairSymbol d e N sig (x,y))‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_root_high_shell_inverse (T := T+1) hsig hsmall hδ
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (δ^(-(1/2:ℝ)))
  refine ⟨n,max N₁ N₂,?_⟩
  intro N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hb := h₁ N ((le_max_left _ _).trans hN) d e hd he hc₁ hc₂ hL₁ hL₂
    U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hw0 : 0 ≤ (dist x y)^(-(1/2:ℝ)) := Real.rpow_nonneg dist_nonneg _
  have hw : (dist x y)^(-(1/2:ℝ)) ≤ ((2:ℝ)^N)^(1:ℝ) :=
    (Real.rpow_le_rpow_of_nonpos hδ hxy (by norm_num)).trans (h₂ N ((le_max_right _ _).trans hN))
  have hexp : ((2:ℝ)^N)^(1:ℝ)*((2:ℝ)^N)^(-(T+1)) = ((2:ℝ)^N)^(-T) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
    congr 1
    ring
  have heq : (rootSpatialWeight d e N sig (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
        sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
          (rootPairSymbol d e N sig (x,y)) =
      (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
        (Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ))*(rootPairMask d e N sig (x,y):ℂ) -
          sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
            (rootPairSymbol d e N sig (x,y))) := by
    simp only [rootSpatialWeight,Complex.ofReal_mul]
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw0]
  exact (mul_le_mul hw hb (norm_nonneg _) (by positivity)).trans_eq hexp

end PlanarFalconer

end OAI
