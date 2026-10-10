import OAI.Geometry.NodalSets.Elliptic.RescaledCoordinates
import OAI.Geometry.NodalSets.Elliptic.RescaledSeedBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma affine_rescaling_derivative_le (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (x v : Coord) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (x+r • z)) v‖ ≤
      ‖iteratedFDeriv ℝ k f (x+r • v)‖ := by
  let L : Coord →L[ℝ] Coord := r • ContinuousLinearMap.id ℝ Coord
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖r • z‖ ≤ 1*‖z‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)
  change ‖iteratedFDeriv ℝ k ((fun z ↦ f (x+z)) ∘ L) v‖ ≤ _
  have htrans : ContDiff ℝ ∞ (fun z : Coord ↦ f (x+z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [L.iteratedFDeriv_comp_right htrans v
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)),iteratedFDeriv_comp_add_left]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ _ : Fin k, ‖L‖) ≤ 1 := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg L) hL
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

def normalizedRescaling (f : Coord → ℂ) (S : Coord → ℝ)
    (N s σ : ℝ) (x v : Coord) : ℂ :=
  (σ⁻¹:ℂ)*rescaledSeedNormalizer S (x,s⁻¹) v*f (x+(N*s)⁻¹ • v)

lemma normalizedRescaling_eq_div (f : Coord → ℂ) (S : Coord → ℝ)
    (N s σ : ℝ) (x v : Coord) :
    normalizedRescaling f S N s σ x v =
      f (x+(N*s)⁻¹ • v) / (σ*Real.exp (fderiv ℝ S x v/s):ℝ) := by
  simp only [normalizedRescaling,rescaledSeedNormalizer,neg_mul,Real.exp_neg,
    Complex.ofReal_mul,Complex.ofReal_inv,div_eq_mul_inv,mul_inv_rev]
  rw [show fderiv ℝ S x v * s⁻¹ = s⁻¹ * fderiv ℝ S x v by ring]
  ring

lemma normalizedRescaling_square_bound (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) (N s σ : ℝ)
    (hN : 1 ≤ N) (hs : 1 ≤ s) (hσ : 0 < σ) (x v : Coord) (d : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ j, j ≤ d → ‖iteratedFDeriv ℝ j (rescaledSeedNormalizer S (x,s⁻¹)) v‖ ≤ A)
    (k : ℕ) (hk : k ≤ d) :
    ‖iteratedFDeriv ℝ k (normalizedRescaling f S N s σ x) v‖^2 ≤
      (2^d*A)^2*(∑ j : Fin (d+1), ‖iteratedFDeriv ℝ j.val f (x+(N*s)⁻¹ • v)‖^2)/σ^2 := by
  let E : ℝ := ∑ j : Fin (d+1), ‖iteratedFDeriv ℝ j.val f (x+(N*s)⁻¹ • v)‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hj (j : ℕ) (hjd : j ≤ d) : ‖iteratedFDeriv ℝ j f (x+(N*s)⁻¹ • v)‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact Finset.single_le_sum (f := fun i : Fin (d+1) ↦
      ‖iteratedFDeriv ℝ i.val f (x+(N*s)⁻¹ • v)‖^2)
      (fun i _ ↦ sq_nonneg _) (Finset.mem_univ (⟨j,by omega⟩ : Fin (d+1)))
  obtain ⟨hr0,hr1,_⟩ := rescaling_radius_bound hN hs
  let amp := rescaledSeedNormalizer S (x,s⁻¹)
  let F : Coord → ℂ := fun z ↦ f (x+(N*s)⁻¹ • z)
  have hamp : ContDiff ℝ ∞ amp := (rescaledSeedNormalizer_smooth S hS).comp
    (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_const.add (contDiff_id.const_smul _))
  have hprod := mul_derivative_power_bound hamp hF k v hA (by norm_num : (0:ℝ) ≤ 1)
    (N := 1) (w := 1)
    (fun j hjk ↦ by simpa using ha j (hjk.trans hk))
    (fun j hjk ↦ by simpa only [one_pow,mul_one] using
      (affine_rescaling_derivative_le f hf x v hr0 hr1 j).trans (hj j (hjk.trans hk)))
  simp only [one_pow,mul_one] at hprod
  have hp : (2:ℝ)^k ≤ 2^d := pow_le_pow_right₀ (by norm_num) hk
  have hb : ‖iteratedFDeriv ℝ k (fun z ↦ amp z*F z) v‖ ≤ (2^d*A)*Real.sqrt E :=
    hprod.trans (by gcongr)
  have he : normalizedRescaling f S N s σ x = fun z ↦ (σ⁻¹:ℂ) • (amp z*F z) := by
    funext z
    simp only [normalizedRescaling,smul_eq_mul,amp,F,mul_assoc]
  rw [he,iteratedFDeriv_const_smul_apply' ((hamp.mul hF).of_le (by
    exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul,
    norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσ]
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ σ⁻¹*‖iteratedFDeriv ℝ k (fun z ↦ amp z*F z) v‖)
    (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hσ.le)) 2
  refine h.trans_eq ?_
  rw [mul_pow,mul_pow,Real.sq_sqrt hE]
  dsimp [E]
  ring

end
end Yau.Geometry

end OAI
