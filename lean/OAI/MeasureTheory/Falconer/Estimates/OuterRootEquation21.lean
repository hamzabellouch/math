import OAI.MeasureTheory.Falconer.Estimates.ActualRootEquation21

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

theorem source_root_sigma_small {δ β kap sig : ℝ} (hδ : δ < 1)
    (hβ : β = δ/10) (hkap : 1000000*kap < β) (hsig : sig < kap/1000) : sig ≤ 1/4 := by
  linarith

namespace RootShellData

noncomputable def ofOuter (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam₁ lam₂ sig kap : ℝ) (c : ℕ) (U V : DyadicSquare) : RootShellData :=
  ⟨RootEndpointData.ofOuter Q₁ ρ m₁ N lam₁ sig kap c,
    RootEndpointData.ofOuter Q₂ ν m₂ N lam₂ sig kap c,N,sig,U,V⟩

theorem ofOuter_measure (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam₁ lam₂ sig kap : ℝ) (c : ℕ) (U V : DyadicSquare) :
    (ofOuter Q₁ Q₂ ρ ν m₁ m₂ N lam₁ lam₂ sig kap c U V).measure =
      Measure.map (fun z : Plane × Plane => dist z.1 z.2)
        ((ρ.prod ν).withDensity (fun z => ENNReal.ofReal
          ((dist z.1 z.2)^(-(1/2:ℝ)) *
            (outerEndpointMask Q₁ ρ m₁ N lam₁ sig kap c z.1 (sourceRadialUnit z.2 z.1) *
             outerEndpointMask Q₂ ν m₂ N lam₂ sig kap c z.2 (sourceRadialUnit z.2 z.1))))) := rfl

theorem uniform_outer_equation21 {sig kap δ L eps T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hkap : 0 < kap)
    (hδ : 0 < δ) (hL : 0 < L) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀,
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ ρ ν : Measure Plane, ∀ [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν],
    ∀ (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ) (c : ℕ), 2*c ≤ N →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    (∀ᵐ x ∂ρ, x ∈ U.carrier) → (∀ᵐ y ∂ν, y ∈ V.carrier) →
    (∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) → (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    let d := ofOuter Q₁ Q₂ ρ ν m₁ m₂ N lam₁ lam₂ sig kap c U V
    (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
      ((2:ℝ)^N)^eps*d.inverseShellSupremum n N Ψ+((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_equation21 (T := T) hsig hsmall hδ hL heps
  refine ⟨n,max 1 N₁,?_⟩
  intro N hN Q₁ Q₂ hQ₁ hQ₂ ρ ν instρ instν m₁ m₂ lam₁ lam₂ c hc U V hU hV hcarry₁ hcarry₂ hsep s hUs hVs hstrong Ψ hΨ hpos hs W hW hΨW hone
  let d := ofOuter Q₁ Q₂ ρ ν m₁ m₂ N lam₁ lam₂ sig kap c U V
  let : IsProbabilityMeasure d.left.ρ := by change IsProbabilityMeasure ρ; infer_instance
  let : IsProbabilityMeasure d.right.ρ := by change IsProbabilityMeasure ν; infer_instance
  have hNpos : 0 < N := by have := (le_max_left 1 N₁).trans hN; omega
  have hq := sourcePolicyBlock_pos hNpos hkap
  exact h₁ d ((le_max_right _ _).trans hN) rfl hQ₁ hQ₂
    (outerDescriptorList_card m₁ hq) (outerDescriptorList_card m₂ hq)
    (fun b hb => outerDescriptorList_half m₁ hq hc hb)
    (fun b hb => outerDescriptorList_half m₂ hq hc hb)
    hU hV hcarry₁ hcarry₂ hsep s hUs hVs hstrong Ψ hΨ hpos hs W hW hΨW hone

end RootShellData

end PlanarFalconer

end OAI
