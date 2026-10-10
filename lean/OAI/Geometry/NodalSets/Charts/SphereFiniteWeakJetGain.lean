import OAI.Geometry.NodalSets.Charts.SphereInteriorWeakDerivativeGain
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetEquation
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetForcingBounds

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_weak_jet_gain (d : SphereEnergyData) (p : Base)
    (B : Yau.Jets.Coord → ℝ) (hB : ContDiff ℝ ∞ B)
    (R r : ℝ) (hr : r < R) (hR : R ≤ 1)
    (N : ℕ) (ds : List (Fin 4)) (hd : ds.length ≤ N) :
    ∃ K > 0, ∀ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
      let Q := Yau.realCenteredCube 4 R
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
          ∫ x in Q, B x*U [] x*psi x) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
        (∑ a, ∑ i, ‖H a i‖^2) ≤ K*E ∧
        ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          IntegrableOn (fun x ↦ U (a::ds) x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
          IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 r) ∧
          (∫ x in Yau.realCenteredCube 4 r, U (a::ds) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
  let Q := Yau.realCenteredCube 4 R
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 R
  obtain ⟨F,hF,hforcing⟩ := Yau.real_weak_jet_forcing_H1_bound hQ (sphereChartPrincipalDensity d p)
    B (sphereChartPrincipalDensity_smooth d p) hB N ds hd
  obtain ⟨C,hC,hgain⟩ := sphere_interior_weak_derivative_gain d p R r hr hR
  refine ⟨C*(F+1),by positivity,?_⟩
  intro U
  dsimp only
  intro hU hw he E hE hUE
  have hf := hforcing U hU hw E hE hUE
  have heq := Yau.real_finite_weak_jet_equation hQ (sphereChartPrincipalDensity d p) B
    (sphereChartPrincipalDensity_smooth d p) hB U N hU hw he ds hd
  have hsmall : E ≤ (F+1)*E := by nlinarith only [mul_nonneg hF.le hE]
  have hlarge : F*E ≤ (F+1)*E := by nlinarith only [hE]
  have h := hgain (U ds) (fun a ↦ U (a::ds)) (fun a ↦ U (a::ds))
    (Yau.realWeakJetFluxError (sphereChartPrincipalDensity d p) U ds)
    (Yau.realWeakJetFluxErrorDerivative (sphereChartPrincipalDensity d p) U ds)
    (Yau.realWeakJetExpansion B U [] ds)
    (hU ds (by omega)) (fun a ↦ hU _ (by simp only [List.length_cons]; omega))
    (fun a ↦ hU _ (by simp only [List.length_cons]; omega))
    (fun j ↦ (hf.2 j 0).1.1) (fun j i ↦ (hf.2 j i).2.1.1) hf.1.1
    (fun _ ↦ Filter.EventuallyEq.rfl) (hw ds hd)
    (fun j i psi hp hc hs ↦ ((hf.2 j i).2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (heq.2.2 psi hp hc hs).2.2.2)
    ((F+1)*E) (mul_nonneg (by positivity) hE)
    ((hUE ds (by omega)).trans hsmall)
    (fun a ↦ (hUE _ (by simp only [List.length_cons]; omega)).trans hsmall)
    (hf.1.2.trans hlarge) (fun j ↦ (hf.2 j 0).1.2.trans hlarge)
    (fun j i ↦ (hf.2 j i).2.1.2.trans hlarge)
  simpa only [mul_assoc] using h

end
end Yau.Target

end OAI
