import OAI.Geometry.NodalSets.Charts.SphereWeakJetSuccessor
import OAI.Geometry.NodalSets.Elliptic.RealPositiveNestedRadii

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_weak_jet_iteration (d : SphereEnergyData) (p : Base)
    (B : Yau.Jets.Coord → ℝ) (hB : ContDiff ℝ ∞ B) (m : ℕ) :
    ∃ K > 0, ∀ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
      let Q := Yau.realCenteredCube 4 (1/8)
      (∀ es, es.length ≤ 4 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ 3 → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
          ∫ x in Q, B x*U [] x*psi x) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ 4 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∃ V : List (Fin 4) → Yau.Jets.Coord → ℝ,
        let q := Yau.realCenteredCube 4 (Yau.realWeakJetRadius m)
        (∀ es, es.length ≤ 4 → V es=U es) ∧
        (∀ es, es.length ≤ m+4 → MemLp (V es) 2 (volume.restrict q) ∧
          (∫ x in q, (V es x)^2) ≤ K*E) ∧
        (∀ es, es.length ≤ m+3 → ∀ i psi,
          ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          (∫ x in q, V es x*Yau.coordPartial psi x i)=-(∫ x in q, V (i::es) x*psi x)) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          (∑ a, ∑ j, ∫ x in q, sphereChartPrincipalDensity d p x a j*V [a] x*Yau.coordPartial psi x j) =
            ∫ x in q, B x*V [] x*psi x := by
  induction m with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro U
    dsimp only
    intro hU hw he E hE hUE
    refine ⟨U,fun _ _ ↦ rfl,?_,?_,?_⟩
    · simpa only [Yau.realWeakJetRadius_zero,Nat.zero_add,one_mul] using
        (show ∀ es, es.length ≤ 4 → MemLp (U es) 2 (volume.restrict (Yau.realCenteredCube 4 (1/8))) ∧
          (∫ x in Yau.realCenteredCube 4 (1/8), (U es x)^2) ≤ E from fun es hh ↦ ⟨hU es hh,hUE es hh⟩)
    · simpa only [Yau.realWeakJetRadius_zero,Nat.zero_add] using hw
    · simpa only [Yau.realWeakJetRadius_zero] using he
  | succ m ih =>
    obtain ⟨C,hC,hbase⟩ := ih
    obtain ⟨D,hD,hstep⟩ := sphere_weak_jet_successor d p B hB
      (Yau.realWeakJetRadius m) (Yau.realWeakJetRadius (m+1)) (Yau.realWeakJetRadius_succ_lt m)
      ((Yau.realWeakJetRadius_upper m).trans (by norm_num)) (m+3)
    refine ⟨D*C,mul_pos hD hC,?_⟩
    intro U
    dsimp only
    intro hU hw he E hE hUE
    obtain ⟨V,hlo,hV,hvw,hve⟩ := hbase U hU hw he E hE hUE
    obtain ⟨W,hWlo,hW,hww,hwe⟩ := hstep V (fun es hh ↦ (hV es (by omega)).1)
      hvw hve (C*E) (mul_nonneg hC.le hE) (fun es hh ↦ (hV es (by omega)).2)
    refine ⟨W,fun es hh ↦ (hWlo es (by omega)).trans (hlo es hh),?_,?_,hwe⟩
    · intro es hh
      have h := hW es (by omega)
      exact ⟨h.1,by simpa only [mul_assoc] using h.2⟩
    · intro es hh i psi hp hc hs
      exact (hww es (by omega) i psi hp hc hs).2.2

end
end Yau.Target

end OAI
