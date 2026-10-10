import OAI.Geometry.NodalSets.Elliptic.RealL2DifferenceQuotient

namespace OAI

namespace Yau
open MeasureTheory Filter
open scoped Topology
noncomputable section

def realL2DifferenceMap {n : ℕ} (i : Fin n) (h : ℝ) :
    RealEuclideanL2 n →L[ℝ] RealEuclideanL2 n :=
  h⁻¹ • ((Lp.compMeasurePreservingₗᵢ ℝ (fun x : (Fin n → ℝ) ↦ x+Pi.single i h)
    (measurePreserving_add_right (G := Fin n → ℝ) volume (Pi.single i h : Fin n → ℝ))).toContinuousLinearMap -
      ContinuousLinearMap.id ℝ (RealEuclideanL2 n))

theorem realL2DifferenceMap_apply {n : ℕ} (i : Fin n) (h : ℝ) (u : RealEuclideanL2 n) :
    realL2DifferenceMap i h u = realL2DifferenceQuotient i h u := rfl

theorem realDifferenceQuotient_congr_ae {n : ℕ} (i : Fin n) (h : ℝ)
    {u v : (Fin n → ℝ) → ℝ} (huv : u =ᵐ[volume] v) :
    realDifferenceQuotient i h u =ᵐ[volume] realDifferenceQuotient i h v := by
  have hs := (measurePreserving_add_right (G := Fin n → ℝ) volume
    (Pi.single i h)).quasiMeasurePreserving.ae_eq_comp huv
  filter_upwards [huv,hs] with x hx ht
  exact congrArg₂ (fun a b : ℝ ↦ h⁻¹*(a-b)) ht hx

theorem realL2DifferenceMap_ae {n : ℕ} (i : Fin n) (h : ℝ) (u : RealEuclideanL2 n)
    (v : (Fin n → ℝ) → ℝ) (he : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] v) :
    (realL2DifferenceMap i h u : (Fin n → ℝ) → ℝ) =ᵐ[volume] realDifferenceQuotient i h v :=
  (realL2DifferenceQuotient_ae i h u).trans (realDifferenceQuotient_congr_ae i h he)

theorem real_L2_norm_sq_rep {n : ℕ} (u : RealEuclideanL2 n)
    (v : (Fin n → ℝ) → ℝ) (he : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] v) :
    ‖u‖^2 = ∫ x, (v x)^2 := by
  have h := real_toLp_norm_sq _ (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at h
  rw [h]
  exact integral_congr_ae (he.fun_comp (fun t : ℝ ↦ t^2))

theorem real_difference_norm_bound_limit {n : ℕ} (i : Fin n) (h : ℝ)
    (u g : RealEuclideanL2 n) (v w : ℕ → RealEuclideanL2 n)
    (hv : Tendsto v atTop (𝓝 u)) (hw : Tendsto w atTop (𝓝 g))
    (hb : ∀ k, ‖realL2DifferenceMap i h (v k)‖^2 ≤ ‖w k‖^2) :
    ‖realL2DifferenceMap i h u‖^2 ≤ ‖g‖^2 :=
  le_of_tendsto_of_tendsto
    (((realL2DifferenceMap i h).continuous.continuousAt.tendsto.comp hv).norm.pow 2)
    (hw.norm.pow 2) (Eventually.of_forall hb)

end
end Yau

end OAI
