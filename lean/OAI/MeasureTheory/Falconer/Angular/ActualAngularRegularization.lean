import OAI.MeasureTheory.Falconer.Radial.ProjectionExceptional

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

structure SourceAngularBounds (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) : Prop where
  parallel : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ P : CellPath, P.length = p →
    sourceArcLength (parallelGoodSet Q ρ g p P
      (2/(2:ℝ)^p*((2:ℝ)^N)^(1000*sig))
      (((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+2000*(lam+sig))))ᶜ ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))
  projection : ∀ p u : ℕ, p ≤ u → u ≤ N → ∀ P : CellPath, P.length = p →
    sourceArcLength (projectionGoodSet Q ρ p u P
      (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
      (((2:ℝ)^N)^(m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+2000*(lam+sig))))ᶜ ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))

theorem actual_angular_regularization (Q : DyadicSquare) (hQ : Q.side = 1)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {δ C lam sig : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) (hsig : 0 < sig)
    (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      (retainedClassLabels Q μ N B t).card ≤ (4*N+1)^(2*H+1) ∧
      μ (retainedClassUnion Q μ N B t)ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        (((4*N+1)^(2*H+1):ℕ):ENNReal)*t ∧
      ∀ T ∈ retainedClassLabels Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ m : ℝ → ℝ,
          RegularizedProfileData Q (normalizedClass Q μ L F T) N B δ lam m ∧
          SourceAngularBounds Q (normalizedClass Q μ L F T) m N lam sig := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨H,N₁,hH,hHbound,hreg⟩ := actual_profile_regularization Q hside μ hcarry hC hlam hball
  obtain ⟨N₂,hpar⟩ := uniform_parallel_exceptional hlam hsig
  obtain ⟨N₃,hproj⟩ := uniform_projection_exceptional hlam hsig
  refine ⟨H,max N₁ (max N₂ N₃),hH,hHbound,?_⟩
  intro N hN
  have hNmax : max N₂ N₃ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hc,hd,hr⟩ := hreg N ((le_max_left _ _).trans hN)
  refine ⟨hc,hd,?_⟩
  intro T hT
  obtain ⟨hmass,m,hm⟩ := hr T hT
  exact ⟨hmass,m,hm,⟨hpar N ((le_max_left _ _).trans hNmax) Q hQ _ m _ δ hm,
    hproj N ((le_max_right _ _).trans hNmax) Q hQ _ m _ δ hm⟩⟩

end PlanarFalconer

end OAI
