import OAI.Geometry.NodalSets.Elliptic.RealInhomogeneousCaccioppoli

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_inhomogeneous_caccioppoli (k L M : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W f eta : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ f → ContDiff ℝ ∞ eta →
      (∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) → HasCompactSupport eta →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta,
        Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x) →
      Integrable (fun x ↦ eta x^2*realGradientSquare W x) ∧
      Integrable (fun x ↦ (eta x^2+realGradientSquare eta x)*W x^2) ∧
      Integrable (fun x ↦ eta x^2*f x^2) ∧
      Integrable (fun x ↦ eta x^2*(∑ i, F x i^2)) ∧
      (∫ x, eta x^2*realGradientSquare W x) ≤ K *
        ((∫ x, (eta x^2+realGradientSquare eta x)*W x^2)+
          (∫ x, eta x^2*f x^2)+(∫ x, eta x^2*(∑ i, F x i^2))) := by
  obtain ⟨K,hK,hbound⟩ := real_inhomogeneous_caccioppoli k L M hk hL hM
  refine ⟨K,hK,fun C V W f eta F hC hV hW hf heta hF hc hs hlo hhi hpot he ↦ ?_⟩
  let g := fun x ↦ Yau.coordDiv (realMatrixFlux C W) x+V x*W x-Yau.coordDiv F x
  have hg : ContDiff ℝ ∞ g :=
    ((ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (realMatrixFlux_smooth C W hC hW i) i)).add
      (hV.mul hW)).sub (ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hF i) i))
  have h := hbound C V W g eta F hC hV hW hg heta hF hc hs hlo hhi hpot (fun x ↦ by dsimp [g]; ring)
  have hid : (fun x ↦ eta x^2*g x^2)=(fun x ↦ eta x^2*f x^2) := by
    funext x
    by_cases hx : x ∈ tsupport eta
    · have heq : g x=f x := by dsimp [g]; linarith only [he x hx]
      rw [heq]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [hid] at h
  exact h

end
end Yau.Geometry

end OAI
