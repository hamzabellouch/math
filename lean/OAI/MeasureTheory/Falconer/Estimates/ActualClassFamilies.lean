import OAI.MeasureTheory.Falconer.Angular.ActualAngularRegularization

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

structure ActualClassFamily (Q : DyadicSquare) (μ : Measure Plane) (N H : ℕ)
    (δ lam sig : ℝ) (m : List ℕ → ℝ → ℝ) : Prop where
  count : (retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))).card ≤ (4*N+1)^(2*H+1)
  discarded : μ (retainedClassUnion Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))ᶜ ≤
    ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
      (((4*N+1)^(2*H+1):ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))
  mass : ∀ T ∈ retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
    ENNReal.ofReal (((2:ℝ)^N)^(-lam)) ≤
      classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N (N/H)) T univ
  profiles : ∀ T ∈ retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
    RegularizedProfileData Q
      (normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N (N/H)) T)
        N (N/H) δ lam (m T) ∧
    SourceAngularBounds Q
      (normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N (N/H)) T)
        (m T) N lam sig

theorem actual_class_family (Q : DyadicSquare) (hQ : Q.side = 1)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {δ C lam sig : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) (hsig : 0 < sig)
    (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      ∃ m : List ℕ → ℝ → ℝ, ActualClassFamily Q μ N H δ lam sig m := by
  classical
  obtain ⟨H,N₀,hH,hHbound,hr⟩ := actual_angular_regularization Q hQ μ hcarry hC hlam hsig hball
  refine ⟨H,N₀,hH,hHbound,?_⟩
  intro N hN
  obtain ⟨hc,hd,hp⟩ := hr N hN
  let S := retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let m : List ℕ → ℝ → ℝ := fun T => if hT : T ∈ S then Classical.choose (hp T hT).2 else fun _ => 0
  refine ⟨m,⟨hc,hd,fun T hT => (hp T hT).1,?_⟩⟩
  intro T hT
  change T ∈ S at hT
  simpa only [m, dite_eq_left hT] using Classical.choose_spec (hp T hT).2

end PlanarFalconer

end OAI
