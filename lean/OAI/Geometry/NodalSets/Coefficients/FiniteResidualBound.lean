import OAI.Geometry.NodalSets.Elliptic.FiniteLinearity

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma complexified_iterated_norm_le (u : Coord → ℝ) (hu : ContDiff ℝ ∞ u)
    (k : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ k (fun z ↦ (u z:ℂ)) x‖ ≤ ‖iteratedFDeriv ℝ k u x‖ := by
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left (hu.contDiffAt (x := x))
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
  change iteratedFDeriv ℝ k (fun z ↦ (u z:ℂ)) x = _ at he
  rw [he]
  have hc : ‖Complex.ofRealCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z ↦ by simp)
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hc (norm_nonneg (iteratedFDeriv ℝ k u x)))

theorem gaussianWaveField_source_residual_bound
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (V : ι → Coord → ℂ) (hV : ∀ a, ContDiff ℝ ∞ (V a))
    (hf : ∀ a i, ContDiff ℝ ∞ (sourceFlux g w (V a) i))
    (lam : ℝ)
    (hr : ∀ a, ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w (V a) x+(lam:ℂ)*V a x))
    (coeff : ι × Fin 2 → ℝ) {R : ℝ} (hR : 0 ≤ R) (hc : coeff ∈ coefficientEvent R)
    (k : ℕ) (x : Coord) {B : ℝ}
    (hb : ∀ a, ‖iteratedFDeriv ℝ k
      (fun x ↦ sourceWeightedOperator g w (V a) x+(lam:ℂ)*V a x) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun x ↦
      sourceWeightedOperator g w (fun z ↦ (gaussianWaveField V coeff z:ℂ)) x+
      (lam:ℂ)*(gaussianWaveField V coeff x:ℂ)) x‖ ≤ (Fintype.card ι:ℝ)*R*B := by
  rw [gaussianWaveField_source_residual g w V hV hf coeff lam]
  exact (complexified_iterated_norm_le _ (gaussianWaveField_contDiff _ coeff hr) k x).trans
    (gaussianWaveField_iterated_bound _ coeff hr k x hR hc hb)

end
end Yau.Geometry

end OAI
