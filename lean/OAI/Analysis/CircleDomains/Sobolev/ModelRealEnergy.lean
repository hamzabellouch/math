import OAI.Analysis.CircleDomains.Transfer.ModelRealSubfamily

namespace OAI

/-! Recover ordinary real Dirichlet estimates from the same masked
circle metric. The full-mask barriers retain their real gradient energy. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {J I A : Type*} {n N : ℕ} {T : J → ℂ ≃ₜ ℂ} {H : I → ℂ ≃ₜ ℂ}
  {G K : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
  {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
  {θ : Fin n → ℝ} {ε : ℝ} {Q : MaskedModelData T H G K M f χ N θ ε}
  {ι : A → Fin n} {r : A → (ℝ × ℝ) → ℝ}

theorem ModelRealSubfamily.gradient_eq (W : ModelRealSubfamily Q ι r)
    (hG : IsOpen G) (j : A) {x : ℝ × ℝ}
    (hx : x ∈ G ∪ ⋃ i, realJordanInterior (H i)) :
    circleGradient (Q.functions (ι j)) x = planarGradient (W.functions j) x := by
  have he : Q.functions (ι j) = fun y => (W.functions j y : UnitAddCircle) :=
    funext (fun y => (W.projection j y).symm)
  rw [he]
  exact circleGradient_coe_eq_planarGradient
    (hG.union (isOpen_iUnion fun i => (realJordanInterior_geometry (H i)).1)) (W.filled.1 j) hx

theorem ModelRealSubfamily.source_energy (W : ModelRealSubfamily Q ι r)
    (hG : IsOpen G) (hRM : ∀ j, M (ι j) = univ)
    (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (j : A) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ K) :
    (∫ x in realChartDomain (completedRegion T) \ E, gradientEnergy (W.functions j) Q.metric x) <
      (∫ x in G \ E, gradientEnergy (r j) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  have hF : (∫ x in realChartDomain (completedRegion T) \ E,
      gradientEnergy (W.functions j) Q.metric x) =
      ∫ x in realChartDomain (completedRegion T) \ E,
        fieldEnergy (circleGradient (Q.functions (ι j))) Q.metric x := by
    apply setIntegral_congr_fun ((isClosed_real_completedRegion T).measurableSet.diff hE)
    intro x hx
    change covectorEnergy _ _ = covectorEnergy _ _
    rw [W.gradient_eq hG j (W.extension_contains hx.1)]
  have hf : (∫ x in G \ E, fieldEnergy (circleGradient (f (ι j)))
      (fun x => sphericalMetricFactor x • 1) x) =
      ∫ x in G \ E, gradientEnergy (r j) (fun x => sphericalMetricFactor x • 1) x := by
    apply setIntegral_congr_fun (hG.measurableSet.diff hE)
    intro x hx
    have he : f (ι j) = fun y => (r j y : UnitAddCircle) := funext (fun y => (hrproj j y).symm)
    change covectorEnergy _ _ = covectorEnergy _ _
    rw [he, circleGradient_coe_eq_planarGradient hG (hr j) hx.1]
  have h := Q.localized (ι j) E hE hEK
  rw [hRM j, inter_univ, inter_univ, hf, ← hF] at h
  exact h

end CircleDomainRigidity.FiniteTransfer

end

end OAI
