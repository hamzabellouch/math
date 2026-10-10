import OAI.MeasureTheory.Falconer.Shells.RestoredMaskCoverage
import OAI.MeasureTheory.Falconer.Shells.RestoredShellCandidates

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def restorationArcBound (N H : ℕ) (lam sig : ℝ) : ENNReal :=
  (((4*N+1)^(2*H+1):ℕ):ENNReal)*((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*
    ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))

noncomputable def restorationDiscardBound (N H : ℕ) (lam : ℝ) : ENNReal :=
  ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
    (((4*N+1)^(2*H+1):ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))

theorem actual_restored_removed_mass_bound (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ ν : ProbabilityMeasure Plane) (m₁ m₂ : List ℕ → ℝ → ℝ)
    {N H₁ H₂ : ℕ} (hN : 0 < N) (δ lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (β : ℝ)
    (hf₁ : ActualClassFamily Q μ N H₁ δ lam sig m₁) (hf₂ : ActualClassFamily Q ν N H₂ δ lam sig m₂)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K C : ENNReal} (hK : K ≠ ∞)
    (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
    (hweight : ∀ᵐ z ∂(μ:Measure Plane).prod ν, distanceWeight z ≤ C) :
    restoredShellRemoved Q μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β univ ≤
      C*(restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
        K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p)) := by
  let A := retainedClassUnion Q μ N (N/H₁) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let B := retainedClassUnion Q ν N (N/H₂) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let S := retainedAngularFailure Q μ m₁ N (N/H₁) lam sig kap
  let T := retainedAngularFailure Q ν m₂ N (N/H₂) lam sig kap
  let bad : Set (Plane × Plane) := ((Aᶜ ×ˢ univ ∪ univ ×ˢ Bᶜ) ∪ radialFailure S) ∪ Prod.swap ⁻¹' radialFailure T
  have hS := measurableSet_retainedAngularFailure Q μ m₁ N (N/H₁) lam sig kap
  have hT := measurableSet_retainedAngularFailure Q ν m₂ N (N/H₂) lam sig kap
  have hbS := radial_failure_mass_le μ ν hpq hK hμrad S hS
    (ae_retainedAngularFailure_bound Q hQ μ m₁ hN δ lam sig hkap hf₁)
  have hbT := radial_failure_mass_le ν μ hpq hK hνrad T hT
    (ae_retainedAngularFailure_bound Q hQ ν m₂ hN δ lam sig hkap hf₂)
  have hswap : ((μ:Measure Plane).prod (ν:Measure Plane)) (Prod.swap ⁻¹' radialFailure T) =
      ((ν:Measure Plane).prod (μ:Measure Plane)) (radialFailure T) := by
    rw [← Measure.map_apply measurable_swap (measurableSet_radialFailure T hT),Measure.prod_swap]
  have hbad : ((μ:Measure Plane).prod (ν:Measure Plane)) bad ≤
      restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
        K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p) := by
    calc
      _ ≤ (((μ:Measure Plane).prod (ν:Measure Plane)) (Aᶜ ×ˢ (univ : Set Plane))+((μ:Measure Plane).prod (ν:Measure Plane)) ((univ : Set Plane) ×ˢ Bᶜ)+
          ((μ:Measure Plane).prod (ν:Measure Plane)) (radialFailure S))+((μ:Measure Plane).prod (ν:Measure Plane)) (Prod.swap ⁻¹' radialFailure T) := by
        apply (measure_union_le _ _).trans
        apply add_le_add
        · apply (measure_union_le _ _).trans
          exact add_le_add (measure_union_le _ _) le_rfl
        · exact le_rfl
      _ ≤ _ := by
        simp only [Measure.prod_prod,measure_univ,mul_one,one_mul,hswap]
        exact add_le_add (add_le_add (add_le_add hf₁.discarded hf₂.discarded) hbS) hbT
  apply (removed_pushforward_mass_le ((μ:Measure Plane).prod (ν:Measure Plane)) (fun z => dist z.1 z.2) (by fun_prop)
    distanceWeight (restoredShellMask Q μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β) bad C hweight ?_).trans
  · exact mul_le_mul_right hbad C
  · apply Filter.Eventually.of_forall
    intro z hz
    have hx : z.1 ∈ A := by
      by_contra hn
      exact hz (Or.inl (Or.inl (Or.inl ⟨hn,mem_univ _⟩)))
    have hy : z.2 ∈ B := by
      by_contra hn
      exact hz (Or.inl (Or.inl (Or.inr ⟨mem_univ _,hn⟩)))
    have hfS : sourceRadialUnit z.1 z.2 ∉ S z.1 := by
      intro h
      exact hz (Or.inl (Or.inr h))
    have hfT : sourceRadialUnit z.2 z.1 ∉ T z.2 := by
      intro h
      exact hz (Or.inr h)
    exact restoredShellMask_one_outside Q hQ μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β z hx hy hfS hfT

end PlanarFalconer

end OAI
