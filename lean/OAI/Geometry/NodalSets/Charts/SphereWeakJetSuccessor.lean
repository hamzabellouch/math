import OAI.Geometry.NodalSets.Charts.SphereUniformWeakJetGain
import OAI.Geometry.NodalSets.Elliptic.RealFiniteWeakJetExtension
import OAI.Geometry.NodalSets.Elliptic.RealWeakEquationRestriction

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_weak_jet_successor (d : SphereEnergyData) (p : Base)
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
      ∃ V : List (Fin 4) → Yau.Jets.Coord → ℝ,
        let q := Yau.realCenteredCube 4 r
        (∀ es, es.length ≤ N+1 → V es=U es) ∧
        (∀ es, es.length ≤ N+2 → MemLp (V es) 2 (volume.restrict q) ∧
          (∫ x in q, (V es x)^2) ≤ K*E) ∧
        (∀ es, es.length ≤ N+1 → ∀ i psi,
          ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          IntegrableOn (fun x ↦ V es x*Yau.coordPartial psi x i) q ∧
          IntegrableOn (fun x ↦ V (i::es) x*psi x) q ∧
          (∫ x in q, V es x*Yau.coordPartial psi x i)=-(∫ x in q, V (i::es) x*psi x)) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          (∑ a, ∑ j, ∫ x in q, sphereChartPrincipalDensity d p x a j*V [a] x*Yau.coordPartial psi x j) =
            ∫ x in q, B x*V [] x*psi x := by
  obtain ⟨C,hC,hgain⟩ := sphere_uniform_weak_jet_gain d p B hB R r hr hR N
  refine ⟨C+1,by positivity,?_⟩
  intro U
  dsimp only
  intro hU hw he E hE hUE
  have hex (ds : List (Fin 4)) :
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
      ds.length=N → (∑ a, ∑ i, ‖H a i‖^2) ≤ C*E ∧
        ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          (∫ x in Yau.realCenteredCube 4 r, U (a::ds) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
    by_cases hd : ds.length=N
    · obtain ⟨H,hH,hpair⟩ := hgain U hU hw he E hE hUE ds hd.le
      exact ⟨H,fun _ ↦ ⟨hH,fun a i psi hp hc hs ↦ (hpair a i psi hp hc hs).2.2⟩⟩
    · exact ⟨fun _ _ ↦ 0,fun h ↦ (hd h).elim⟩
  choose H hH using hex
  let V := Yau.realWeakJetSuccessor U (fun ds a i ↦ H ds a i) N
  have hsub : Yau.realCenteredCube 4 r ⊆ Yau.realCenteredCube 4 R := Yau.realCenteredCube_mono hr.le
  have h := Yau.real_finite_weak_jet_extension (Yau.realCenteredCube_isCompact 4 r)
    (Yau.realCenteredCube_isCompact 4 R).measurableSet hsub N U hU hw E C hE hC.le hUE H
    (fun ds hd ↦ (hH ds hd).1) (fun ds hd ↦ (hH ds hd).2)
  refine ⟨V,h.1,h.2.1,h.2.2,?_⟩
  intro psi hp hc hs
  have hzero : V []=U [] := h.1 [] (by simp)
  have hone (a : Fin 4) : V [a]=U [a] := h.1 [a] (by simp)
  simp_rw [hzero,hone]
  exact Yau.real_weak_equation_restrict (Yau.realCenteredCube_isCompact 4 R).measurableSet hsub
    (sphereChartPrincipalDensity d p) (fun a ↦ U [a]) (fun x ↦ B x*U [] x) he psi hp hc hs

end
end Yau.Target

end OAI
