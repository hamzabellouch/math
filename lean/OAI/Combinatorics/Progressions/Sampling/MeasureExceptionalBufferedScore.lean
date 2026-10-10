import OAI.Combinatorics.Progressions.Probability.MeasureGoodAtomTransfer

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem exists_measure_buffered_score_of_uniform_good_comparison
    {H Ω U I : Type*} [MeasurableSpace H] [Fintype Ω] [Fintype U] [Fintype I] {m : ℕ}
    (law : Measure H) [IsProbabilityMeasure law]
    (productive bad : Set H) (hprod : MeasurableSet productive) (hbad : MeasurableSet bad)
    (Qgood : H → Prop) (hQgood : ∀ᵐ h ∂law, Qgood h)
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ)
    (T : Ω → (Fin m → ℤ) → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (ψ : H → U → Ω)
    (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ x T f lam u : ℂ)) =
      (∑ i, c i • J i) + e) {τ ρ M₀ η : ℝ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M₀)
    (hmass : τ ≤ law.real productive) (hbadmass : law.real bad ≤ τ / 4)
    (hatom : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ i,
      ‖(𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖ ≤ η)
    (hb : Integrable (fun h => 𝔼 a, e (ψ h a)) law)
    (hlocal : (∫ h, ‖𝔼 a, e (ψ h a)‖ ∂law) ≤ τ * ρ / 32)
    (hforecast : ∀ h ∈ productive, h ∉ bad → Qgood h →
      ‖𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * e u‖ ≤ ρ / 8)
    (hbudget : M₀ * η ≤ ρ / 8)
    (hscore : ∀ h ∈ productive, h ∉ bad → Qgood h →
      ρ ≤ 𝔼 a, bufferedScalarScore χ x T f lam (ψ h a)) :
    ∃ h ∈ productive, h ∉ bad ∧ Qgood h ∧ ρ / 2 ≤ 𝔼 u, (f u - lam) * ∑' b,
      χ.value (fun i => x u i - (b i : ℝ)) * G h u b * T u b := by
  let A := fun h => finiteWeightedTest id (fun u => (G h u (nearestIntegerLift (x u)) : ℂ))
  let B := fun h => finiteWeightedTest (ψ h) (fun _ => (1 : ℂ))
  have hatom' : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ i,
      ‖A h (J i) - B h (J i)‖ ≤ η := by
    simpa only [A, B, finiteWeightedTest, LinearMap.coe_mk, AddHom.coe_mk,
      id_eq, one_mul] using hatom
  have hb' : Integrable (fun h => B h e) law := by
    simpa only [B, finiteWeightedTest, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using hb
  have hlocal' : (∫ h, ‖B h e‖ ∂law) ≤ τ * ρ / 32 := by
    simpa only [B, finiteWeightedTest, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using hlocal
  have hforecast' : ∀ h ∈ productive, h ∉ bad → Qgood h → ‖A h e‖ ≤ ρ / 8 := by
    simpa only [A, finiteWeightedTest, LinearMap.coe_mk, AddHom.coe_mk, id_eq] using hforecast
  have hscore' : ∀ h ∈ productive, h ∉ bad → Qgood h →
      ρ ≤ (B h (fun u => (bufferedScalarScore χ x T f lam u : ℂ))).re := by
    intro h hh hg hq
    simpa only [B, ← Complex.ofReal_one, finiteWeightedTest_real, one_mul] using hscore h hh hg hq
  obtain ⟨h, hh, hg, hq, hs⟩ := exists_measure_model_transfer_of_uniform_good_comparison law
    productive bad hprod hbad A B _ e J c hmodel Qgood hQgood hτ hρ hη hc hmass hbadmass
    hatom' hb' hlocal' hforecast' hbudget hscore'
  refine ⟨h, hh, hg, hq, ?_⟩
  simpa only [A, finiteWeightedTest_real, id_eq, bufferedScalarScore_weighted] using hs

end Erdos3

end

end OAI
