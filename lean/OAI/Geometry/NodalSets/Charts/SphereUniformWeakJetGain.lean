import OAI.Geometry.NodalSets.Charts.SphereFiniteWeakJetGain
import OAI.Geometry.NodalSets.Elliptic.RealFiniteWordBounds

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_uniform_weak_jet_gain (d : SphereEnergyData) (p : Base)
    (B : Yau.Jets.Coord → ℝ) (hB : ContDiff ℝ ∞ B)
    (R r : ℝ) (hr : r < R) (hR : R ≤ 1) (N : ℕ) :
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
      ∀ ds, ds.length ≤ N →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
        (∑ a, ∑ i, ‖H a i‖^2) ≤ K*E ∧
        ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          IntegrableOn (fun x ↦ U (a::ds) x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
          IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 r) ∧
          (∫ x in Yau.realCenteredCube 4 r, U (a::ds) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
  have hex (ds : List (Fin 4)) := sphere_finite_weak_jet_gain d p B hB R r hr hR ds.length ds le_rfl
  choose C hC hc using hex
  obtain ⟨K,hK,hk⟩ := Yau.real_finite_word_positive_majorant 4 N C
  refine ⟨K,hK,?_⟩
  intro U
  dsimp only
  intro hU hw he E hE hUE ds hd
  obtain ⟨H,hH,hpair⟩ := hc ds U (fun es hh ↦ hU es (by omega))
    (fun es hh ↦ hw es (by omega)) he E hE (fun es hh ↦ hUE es (by omega))
  exact ⟨H,hH.trans (mul_le_mul_of_nonneg_right (hk ds hd) hE),hpair⟩

end
end Yau.Target

end OAI
