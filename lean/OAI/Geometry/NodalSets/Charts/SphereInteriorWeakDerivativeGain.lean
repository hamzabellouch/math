import OAI.Geometry.NodalSets.Charts.SphereInteriorDifferenceBound
import OAI.Geometry.NodalSets.Elliptic.RealNestedWeakDerivative

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_interior_weak_derivative_gain (d : SphereEnergyData) (p : Base)
    (R0 r : ℝ) (hr : r < R0) (hR : R0 ≤ 1) :
    ∃ C > 0,
      ∀ (u : Yau.Jets.Coord → ℝ) (V0 P0 G : Fin 4 → Yau.Jets.Coord → ℝ)
        (DG : Fin 4 → Fin 4 → Yau.Jets.Coord → ℝ) (F0 : Yau.Jets.Coord → ℝ),
      let Q := Yau.realCenteredCube 4 R0
      MemLp u 2 (volume.restrict Q) →
      (∀ a, MemLp (V0 a) 2 (volume.restrict Q)) →
      (∀ a, MemLp (P0 a) 2 (volume.restrict Q)) →
      (∀ j, MemLp (G j) 2 (volume.restrict Q)) →
      (∀ j i, MemLp (DG j i) 2 (volume.restrict Q)) →
      MemLp F0 2 (volume.restrict Q) →
      (∀ a, P0 a =ᵐ[volume.restrict (interior Q)] V0 a) →
      (∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, u x*Yau.coordPartial psi x j)=-(∫ x in Q, V0 j x*psi x)) →
      (∀ j i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, G j x*Yau.coordPartial psi x i)=-(∫ x in Q, DG j i x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*P0 a x*Yau.coordPartial psi x j)=
          (∫ x in Q, F0 x*psi x)-(∑ j, ∫ x in Q, G j x*Yau.coordPartial psi x j)) →
      ∀ E : ℝ, 0 ≤ E →
        (∫ x in Q, (u x)^2) ≤ E →
        (∀ a, (∫ x in Q, (V0 a x)^2) ≤ E) →
        (∫ x in Q, (F0 x)^2) ≤ E →
        (∀ j, (∫ x in Q, (G j x)^2) ≤ E) →
        (∀ j i, (∫ x in Q, (DG j i x)^2) ≤ E) →
        ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
          (∑ a, ∑ i, ‖H a i‖^2) ≤ C*E ∧
          ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
            tsupport psi ⊆ Yau.realCenteredCube 4 r →
            IntegrableOn (fun x ↦ V0 a x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
            IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 r) ∧
            (∫ x in Yau.realCenteredCube 4 r, V0 a x*Yau.coordPartial psi x i)=
              -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
  obtain ⟨B,hB,hgain⟩ := sphere_interior_difference_bound d p R0 r hr hR
  refine ⟨16*B,by positivity,?_⟩
  intro u V0 P0 G DG F0
  dsimp only
  intro hu hv hp hg hd hf hsame hweak hcomm hequation E hE hbu hbv hbf hbg hbd
  have hdiff := hgain u V0 P0 G DG F0 hu hv hp hg hd hf hsame hweak hcomm hequation
    E hE hbu hbv hbf hbg hbd
  have hder (a i : Fin 4) :
      ∃ H : Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)), ‖H‖^2 ≤ B*E ∧
        ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          IntegrableOn (fun x ↦ V0 a x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
          IntegrableOn (fun x ↦ H x*psi x) (Yau.realCenteredCube 4 r) ∧
          (∫ x in Yau.realCenteredCube 4 r, V0 a x*Yau.coordPartial psi x i)=
            -(∫ x in Yau.realCenteredCube 4 r, H x*psi x) := by
    apply Yau.real_nested_weak_derivative_of_difference_bound R0 r ((R0-r)/8)
      hr.le (by linarith) (by linarith) (V0 a) (hv a) i (B*E) (mul_nonneg hB.le hE)
      (fun h hh ↦ (hdiff i h hh).1 a)
    intro h hh
    exact (Finset.single_le_sum (f := fun b ↦ ∫ x in Yau.realCenteredCube 4 r,
      (Yau.realDifferenceQuotient i h (V0 b) x)^2)
      (fun b _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ a)).trans (hdiff i h hh).2
  choose H hH hpair using hder
  refine ⟨H,?_,hpair⟩
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hH a i))
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
  exact ht.trans_eq (by ring)

end
end Yau.Target

end OAI
